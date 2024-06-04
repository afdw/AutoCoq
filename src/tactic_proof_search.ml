open Proofview.Notations

type infer_request = string
  [@@deriving yojson { variants = `Internal "type"; exn = true }]

type infer_response = string list
  [@@deriving yojson { variants = `Internal "type"; exn = true }]

let http_infer (url : string) (infer_request : infer_request) : infer_response =
  let open Lwt.Infix in
  Lwt_main.run (
    Cohttp_lwt_unix.Client.post
      ~body:(Cohttp_lwt.Body.of_string (infer_request |> infer_request_to_yojson |> Yojson.Safe.to_string))
      (Uri.of_string url) >>= fun (response, body) ->
    Cohttp_lwt.Body.to_string body >>= fun body_string ->
    if response |> Cohttp.Response.status <> `OK then
      CErrors.user_err Pp.(
        str "Request failed: " ++ str (Cohttp.Code.string_of_status (response |> Cohttp.Response.status)) ++
        fnl () ++ str body_string
      );
    Lwt.return (body_string |> Yojson.Safe.from_string |> infer_response_of_yojson_exn)
  )

let simple_string_of_ppcmds (c : Pp.t) : string =
  let open Pp in
  let buffer = Buffer.create 512 in
  let rec aux f = function
    | Ppcmd_empty -> ()
    | Ppcmd_string s -> Printf.bprintf buffer "%s" s
    | Ppcmd_glue cs -> List.iter (aux f) (List.map Pp.repr cs)
    | Ppcmd_box (btype, c) ->
      aux (
        match btype with
        | Pp_hbox -> false
        | Pp_vbox _ -> true
        | Pp_hvbox _ -> false
        | Pp_hovbox _ -> false
      ) (Pp.repr c)
    | Ppcmd_tag (_, c) -> (aux f) (Pp.repr c)
    | Ppcmd_print_break (n, _) -> Printf.bprintf buffer "%s" (if f then "\n" else String.make n ' ')
    | Ppcmd_force_newline -> Printf.bprintf buffer "\n"
    | Ppcmd_comment ss -> List.iter (Printf.bprintf buffer "%s") ss in
  aux false (Pp.repr c);
  buffer |> Buffer.to_bytes |> String.of_bytes

exception NoTactics

let rec or_many : type a. a Proofview.tactic list -> a Proofview.tactic = fun tacs ->
  match tacs with
  | [] -> Proofview.tclZERO ~info:(Exninfo.reify()) NoTactics
  | tac :: tacs -> tac <+> or_many tacs

type proofstate = Environ.env * Evd.evar_map * Proofview_monad.goal_with_state list

let save_proofstate : proofstate Proofview.tactic =
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  Proofview.tclUNIT (env, sigma, goals)

let load_proofstate (proofstate : proofstate) : unit Proofview.tactic =
  let (env, sigma, goals) = proofstate in
  Proofview.Unsafe.tclSETENV env <*>
  Proofview.Unsafe.tclEVARS sigma <*>
  Proofview.Unsafe.tclSETGOALS goals

exception CapturingProofstates
exception NoProofstates

let rec capture_proofstates : type a. a Proofview.tactic -> (proofstate * a) list Proofview.tactic = fun tac ->
  Proofview.tclCASE tac >>= function
  | Fail _ -> Proofview.tclUNIT []
  | Next (r, k) ->
    save_proofstate >>= fun proofstate ->
    capture_proofstates (k (Exninfo.capture CapturingProofstates)) >>= fun proofstates ->
    Proofview.tclUNIT ((proofstate, r) :: proofstates)

let rec simulate_proofstates : type a. (proofstate * a) list -> a Proofview.tactic = fun proofstates ->
  match proofstates with
  | [] -> Proofview.tclZERO ~info:(Exninfo.reify()) NoProofstates
  | (proofstate, r) :: proofstates ->
    Proofview.tclOR
      (load_proofstate proofstate <*> Proofview.tclUNIT r)
      (fun _ -> simulate_proofstates proofstates)

let eager (type a key) ?(compare : key -> key -> int = Stdlib.compare) (measure : key Proofview.tactic) (tac : a Proofview.tactic) : a Proofview.tactic =
  let t =
    tac >>= fun r ->
    measure >>= fun key ->
    Proofview.tclUNIT (key, r) in
  capture_proofstates t >>= fun proofstates ->
  let proofstates =
    proofstates
      |> List.stable_sort (fun (_, (key_1, _)) (_, (key_2, _)) -> compare key_1 key_2)
      |> List.map (fun (proofstate, (_, r)) -> (proofstate, r)) in
  simulate_proofstates proofstates

let catch_panics (type a) (tac : a Proofview.tactic) : a Proofview.tactic =
  save_proofstate >>= fun proofstate ->
  let t =
    load_proofstate proofstate <*>
    capture_proofstates tac in
  let _, proofview = Proofview.init (Evd.from_env Environ.empty_env) [] in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (name, poly) ->
  Proofview.wrap_exceptions (fun () ->
    Proofview.tclUNIT (Proofview.apply ~name ~poly Environ.empty_env t proofview)
  ) >>= fun (proofstates, _, status, _) ->
  (if status then Proofview.tclUNIT () else Proofview.mark_as_unsafe) <*>
  simulate_proofstates proofstates

let run_ltac (tactic : string) : unit Proofview.tactic =
  Proofview.tclENV >>= fun env ->
  Proofview.wrap_exceptions (fun () ->
    let ist = Ltac_plugin.Tacinterp.default_ist () in
    let raw_tac = Pcoq.parse_string Ltac_plugin.Pltac.tactic_eoi tactic in
    let glob_tac = Ltac_plugin.Tacintern.intern_pure_tactic (Genintern.empty_glob_sign ~strict:false env) raw_tac in
    let tac = Ltac_plugin.Tacinterp.eval_tactic_ist ist glob_tac in
    catch_panics tac
  )

let print_goal (goal : Proofview.Goal.t) : string =
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  (goal |> Proofview.Goal.hyps |> List.map (
    let open Context.Named.Declaration in function
    | LocalAssum (name, type_) ->
      (name.binder_name |> Names.Id.to_string) ^ " : " ^
      simple_string_of_ppcmds (Printer.pr_econstr_env env sigma type_)
    | LocalDef (name, value, type_) ->
      (name.binder_name |> Names.Id.to_string) ^ " : " ^
      simple_string_of_ppcmds (Printer.pr_econstr_env env sigma type_) ^ " = " ^
      simple_string_of_ppcmds (Printer.pr_econstr_env env sigma value)
  ) |> String.concat ", ") ^ " ⊢ " ^
  simple_string_of_ppcmds (Printer.pr_econstr_env env sigma (goal |> Proofview.Goal.concl))

let proof_search (infer : infer_request -> infer_response) : unit Proofview.tactic =
  let step =
    Proofview.tclFOCUS 1 1 (
      Proofview.Goal.enter (fun goal ->
        let printed_goal = print_goal goal in
        Feedback.msg_info Pp.(str "Goal goal: " ++ str printed_goal);
        let t = or_many (infer printed_goal |> List.map (fun s ->
          Proofview.tclUNIT () >>= fun () ->
          Feedback.msg_info Pp.(str "Applying: " ++ str s);
          Proofview.tclPROGRESS (run_ltac s)
        )) in
        eager Proofview.numgoals t
      )
    ) in
  let rec search current_depth =
    Feedback.msg_info Pp.(str "Current depth: " ++ int current_depth);
    Proofview.numgoals >>= fun goal_count ->
    if goal_count = 0 then
      Proofview.tclUNIT ()
    else
      step >>= fun () ->
      search (current_depth + 1) in
  search 0

let entry_tactic_proof_search (url : string) : unit Proofview.tactic =
  proof_search (http_infer url)
