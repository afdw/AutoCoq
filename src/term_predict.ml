module SConstr = struct
  type t =
    | SHole
    | SQuestion
    | SContext
    | SRel of int
    | SVar of Names.Id.t
    | SSort of EConstr.ESorts.t
    | SCast of t * t
    | SApp of t * t list

  let rec of_constr (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : t =
    match EConstr.kind sigma t with
    | Sort sort -> SSort sort
    | _ -> CErrors.user_err Pp.(str "Unsupported term:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

  let rec pp (env : Environ.env) (sigma : Evd.evar_map) (t : t) : Pp.t =
    let open Pp in
    match t with
    | SHole -> str "_"
    | SQuestion -> str "?"
    | SContext -> str "#"
    | SRel i -> assert false
    | SVar n -> assert false
    | SSort sort -> assert false
    | SCast (t, type_) -> str "(" ++ str "cast" ++ pp env sigma t ++ spc () ++ pp env sigma type_ ++ str ")"
    | SApp (fun_, args) -> str "(" ++ str "app" ++ pp env sigma fun_ ++ spc () ++ prlist_with_sep spc (pp env sigma) args ++ str ")"
end

let command_deconstruct (t_constr_expr : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t_constr_expr in
  Feedback.msg_info Pp.(str "command_deconstruct" ++ spc () ++ Printer.pr_econstr_env env sigma t)
