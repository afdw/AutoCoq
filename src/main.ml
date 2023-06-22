open Proofview.Notations

let get_ref (env : Environ.env) (s : string) : EConstr.t =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global env (Coqlib.lib_ref s))

type isabelle_typ =
  | Isabelle_typ_type of string * isabelle_typ list [@name "Type"]
  | Isabelle_typ_free of string * string list [@name "TFree"]
  | Isabelle_typ_var of (string * int) * string list [@name "TVar"]
  [@@deriving show, yojson]

type isabelle_term =
  | Isabelle_term_const of string * isabelle_typ [@name "Const"]
  | Isabelle_term_free of string * isabelle_typ [@name "Free"]
  | Isabelle_term_var of (string * int) * isabelle_typ [@name "Var"]
  | Isabelle_term_bound of int [@name "Bound"]
  | Isabelle_term_abs of string * isabelle_typ * isabelle_term [@name "Abs"]
  | Isabelle_term_app of isabelle_term * isabelle_term [@name "op $"]
  [@@deriving show, yojson]

  let name_binder_annot_to_string (sigma : Evd.evar_map) (name_binder_annot : Names.Name.t Context.binder_annot) (inner : EConstr.constr) : string =
    if inner |> EConstr.Vars.noccurn sigma 1 then
      "uu_"
    else
      match name_binder_annot.binder_name with
      | Anonymous -> "uu_"
      | Name id -> id |> Names.Id.to_string

let rec isabelle_translate_type (env : Environ.env) (sigma : Evd.evar_map) (type_ : EConstr.constr) : isabelle_typ =
  let f, args = type_ |> EConstr.decompose_app sigma in
  match f |> EConstr.kind sigma, args |> Array.to_list with
  | Var name, [] ->
    Isabelle_typ_free ("'" ^ (name |> Names.Id.to_string), [])
  | Sort sort, [] when sort |> EConstr.ESorts.is_prop sigma ->
    Isabelle_typ_type ("HOL.bool", [])
  | Prod (_, var_type, inner), [] when inner |> EConstr.Vars.noccurn sigma 1 ->
    Isabelle_typ_type ("fun", [
      var_type |> isabelle_translate_type env sigma;
      inner |> isabelle_translate_type env sigma;
    ])
  | _ -> CErrors.user_err Pp.(str "unsupported type:" ++ spc () ++ (type_ |> Printer.pr_econstr_env env sigma))

let rec isabelle_translate_term (env : Environ.env) (sigma : Evd.evar_map) (used_typ_frees : string list) (term : EConstr.constr) : isabelle_term =
  let f, args = term |> EConstr.decompose_app sigma in
  let f_isabelle, args =
    match f |> EConstr.kind sigma, args |> Array.to_list with
    | Rel i, args ->
      Isabelle_term_bound (i - 1), args
    | Prod (name_binder_annot, var_type, inner), args
        when EConstr.isSort sigma var_type && EConstr.destSort sigma var_type |> EConstr.ESorts.family sigma = InType ->
      let name = ref (name_binder_annot_to_string sigma name_binder_annot inner) in
      while used_typ_frees |> List.mem !name do
        name := !name ^ "_"
      done;
      inner
        |> EConstr.Vars.subst1 (EConstr.mkVar (Names.Id.of_string !name))
        |> isabelle_translate_term env sigma (used_typ_frees @ [!name]),
      args
    | Prod (name_binder_annot, var_type, inner), args ->
      Isabelle_term_app (
        Isabelle_term_const (
          "HOL.All",
          Isabelle_typ_type ("fun", [
            Isabelle_typ_type ("fun", [
              var_type |> isabelle_translate_type env sigma;
              Isabelle_typ_type ("HOL.bool", []);
            ]);
            Isabelle_typ_type ("HOL.bool", []);
          ])
        ),
        Isabelle_term_abs (
          name_binder_annot_to_string sigma name_binder_annot inner,
          var_type |> isabelle_translate_type env sigma,
          inner |> isabelle_translate_term env sigma used_typ_frees
        )
      ),
      args
    | Lambda (name_binder_annot, var_type, inner), args ->
      Isabelle_term_abs (
        name_binder_annot_to_string sigma name_binder_annot inner,
        var_type |> isabelle_translate_type env sigma,
        inner |> isabelle_translate_term env sigma used_typ_frees
      ),
      args
    | _, var_type :: args when EConstr.eq_constr sigma f (get_ref env "core.ex.type") ->
      Isabelle_term_const (
        "HOL.Ex",
        Isabelle_typ_type ("fun", [
          Isabelle_typ_type ("fun", [
            var_type |> isabelle_translate_type env sigma;
            Isabelle_typ_type ("HOL.bool", []);
          ]);
          Isabelle_typ_type ("HOL.bool", []);
        ])
      ),
      args
    | _, args when EConstr.eq_constr sigma f (get_ref env "core.True.type") ->
      Isabelle_term_const (
        "HOL.True",
        Isabelle_typ_type ("HOL.bool", [])
      ),
      args
    | _, args when EConstr.eq_constr sigma f (get_ref env "core.False.type") ->
      Isabelle_term_const (
        "HOL.False",
        Isabelle_typ_type ("HOL.bool", [])
      ),
      args
    | _, args when EConstr.eq_constr sigma f (get_ref env "core.not.type") ->
      Isabelle_term_const (
        "HOL.Not",
        Isabelle_typ_type ("fun", [
          Isabelle_typ_type ("HOL.bool", []);
          Isabelle_typ_type ("HOL.bool", []);
        ])
      ),
      args
    | _, args when EConstr.eq_constr sigma f (get_ref env "core.and.type") ->
      Isabelle_term_const (
        "HOL.conj",
        Isabelle_typ_type ("fun", [
          Isabelle_typ_type ("HOL.bool", []);
          Isabelle_typ_type ("fun", [
            Isabelle_typ_type ("HOL.bool", []);
            Isabelle_typ_type ("HOL.bool", []);
          ]);
        ])
      ),
      args
    | _, args when EConstr.eq_constr sigma f (get_ref env "core.or.type") ->
      Isabelle_term_const (
        "HOL.disj",
        Isabelle_typ_type ("fun", [
          Isabelle_typ_type ("HOL.bool", []);
          Isabelle_typ_type ("fun", [
            Isabelle_typ_type ("HOL.bool", []);
            Isabelle_typ_type ("HOL.bool", []);
          ]);
        ])
      ),
      args
    | _, args when EConstr.eq_constr sigma f (get_ref env "core.iff.type") ->
      Isabelle_term_const (
        "HOL.eq",
        Isabelle_typ_type ("fun", [
          Isabelle_typ_type ("HOL.bool", []);
          Isabelle_typ_type ("fun", [
            Isabelle_typ_type ("HOL.bool", []);
            Isabelle_typ_type ("HOL.bool", []);
          ]);
        ])
      ),
      args
    | _, type_ :: args when EConstr.eq_constr sigma f (get_ref env "core.eq.type") ->
      Isabelle_term_const (
        "HOL.eq",
        Isabelle_typ_type ("fun", [
          type_ |> isabelle_translate_type env sigma;
          Isabelle_typ_type ("fun", [
            type_ |> isabelle_translate_type env sigma;
            Isabelle_typ_type ("HOL.bool", []);
          ]);
        ])
      ),
      args
    | _ -> CErrors.user_err Pp.(str "unsupported term:" ++ spc () ++ (term |> Printer.pr_econstr_env env sigma)) in
  args
    |> List.map (isabelle_translate_term env sigma used_typ_frees)
    |> List.fold_left (fun a b -> Isabelle_term_app (a, b)) f_isabelle

let ac_isabelle : unit Proofview.tactic =
  Proofview.Goal.enter (fun goal ->
    let env = Proofview.Goal.env goal in
    let sigma = Proofview.Goal.sigma goal in
    let statement = Proofview.Goal.concl goal in
    let conclusion_isabelle =
      Isabelle_term_app (
        Isabelle_term_const (
          "HOL.Trueprop",
          Isabelle_typ_type ("fun", [
            Isabelle_typ_type ("HOL.bool", []);
            Isabelle_typ_type ("prop", []);
          ])
        ),
        statement |> isabelle_translate_term env sigma []
      ) in
    Feedback.msg_notice (Pp.str (
      Printf.sprintf
        "accept ‹%s›"
        (conclusion_isabelle |> isabelle_term_to_yojson |> Yojson.Safe.to_string)
    ));
    Tacticals.tclIDTAC
  ) <*> Proofview.give_up
