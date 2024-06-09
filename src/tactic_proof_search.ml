open Proofview.Notations

type infer_request = string
  [@@deriving yojson { variants = `Internal "type"; exn = true }]

type infer_response = (string * float) list
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

let if_solved (type a b) (tac : a Proofview.tactic) (then_ : a -> b Proofview.tactic) (else_ : a Proofview.tactic -> b Proofview.tactic) =
  capture_proofstates tac >>= fun proofstates ->
  let solution_proofstate =
    proofstates |> List.find_opt (fun (proofstate, _) ->
      let (_, _, goals) = proofstate in
      goals = []
    ) in
  match solution_proofstate with
  | Some (proofstate, x) ->
    load_proofstate proofstate <*>
    then_ x
  | None ->
    else_ (simulate_proofstates proofstates)

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

let f_branch_proba : float Evd.Store.field = Evd.Store.field "branch_proba"

let get_branch_proba : float Proofview.tactic =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let branch_proba = Evd.Store.get store f_branch_proba |> Option.default 1.0 in
  Proofview.tclUNIT branch_proba

let update_branch_proba (proba_multiplier : float) : unit Proofview.tactic =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let branch_proba = Evd.Store.get store f_branch_proba |> Option.default 1.0 in
  let branch_proba = branch_proba *. proba_multiplier in
  let store = Evd.Store.set store f_branch_proba branch_proba in
  let sigma = Evd.set_extra_data store sigma in
  Proofview.Unsafe.tclEVARS sigma

let f_trace : string list Evd.Store.field = Evd.Store.field "trace"

let get_trace : string list Proofview.tactic =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let trace = Evd.Store.get store f_trace |> Option.default [] in
  Proofview.tclUNIT trace

let cons_trace (trace_element : string) : unit Proofview.tactic =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let trace = Evd.Store.get store f_trace |> Option.default [] in
  let trace = trace @ [trace_element] in
  let store = Evd.Store.set store f_trace trace in
  let sigma = Evd.set_extra_data store sigma in
  Proofview.Unsafe.tclEVARS sigma

exception DepthLimitExceeded

let proof_search (infer : infer_request -> infer_response) : unit Proofview.tactic =
  let step current_depth =
    Proofview.tclFOCUS 1 1 (
      Proofview.Goal.enter (fun goal ->
        Feedback.msg_info Pp.(str "Current depth: " ++ int current_depth);
        let printed_goal = print_goal goal in
        get_trace >>= fun trace ->
        Feedback.msg_info Pp.(str "In trace [" ++ (trace |> prlist_with_sep (fun () -> str "; ") str) ++ str "], got goal: " ++ str printed_goal);
        or_many (infer printed_goal |> List.map (fun (s, proba) ->
          Proofview.tclUNIT () >>= fun () ->
          Feedback.msg_info Pp.(str "Applying: " ++ str s);
          update_branch_proba proba <*>
          cons_trace s <*>
          Proofview.tclTIMEOUTF 0.1 (Proofview.tclPROGRESS (run_ltac s)) <*>
          Proofview.numgoals >>= fun goal_count ->
          Feedback.msg_info Pp.(str "  -> " ++ int goal_count ++ str " goals");
          Proofview.tclUNIT ()
        ))
      )
    ) in
  let rec search current_depth t =
    if_solved
      t
      (fun () ->
        get_trace >>= fun trace ->
        Feedback.msg_info Pp.(str "Proved! Trace: [" ++ (trace |> prlist_with_sep (fun () -> str "; ") str) ++ str "]");
        Proofview.tclUNIT ()
      )
      (fun t ->
        search (current_depth + 1) (
          let measure =
            Proofview.numgoals >>= fun goal_count ->
            get_branch_proba >>= fun branch_proba ->
            Proofview.tclUNIT ((1.0 -. branch_proba) *. 0.8 +. (float_of_int goal_count) *. 0.2) in
          eager measure t <*>
          step current_depth
        )
      ) in
  search 0 (Proofview.tclUNIT ())
  (*
    eager Proofview.numgoals (
      eager Proofview.numgoals (
        eager Proofview.numgoals (
          eager Proofview.numgoals (
            Proofview.tclUNIT ()
          ) <*>
          step 1
        ) <*>
        step 2
      ) <*>
      step 3
    ) <*>
    Proofview.tclINDEPENDENT (Proofview.tclZERO ~info:(Exninfo.reify()) DepthLimitExceeded) in
  *)

let entry_tactic_proof_search (url : string) : unit Proofview.tactic =
  proof_search (http_infer url)
