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

let isabelle_typ_fun (typs : isabelle_typ list) : isabelle_typ =
  let typs = typs |> List.rev in
  typs |> List.tl |> List.fold_left (fun arg_typ fn_typ -> Isabelle_typ_type ("fun", [fn_typ; arg_typ])) (typs |> List.hd)

let isabelle_typ_bool : isabelle_typ = Isabelle_typ_type ("HOL.bool", [])
let isabelle_typ_num : isabelle_typ = Isabelle_typ_type ("Num.num", [])
let isabelle_typ_int : isabelle_typ = Isabelle_typ_type ("Int.int", [])

let name_binder_annot_to_string (sigma : Evd.evar_map) (name_binder_annot : Names.Name.t Context.binder_annot) (inner : EConstr.constr) : string =
  if inner |> EConstr.Vars.noccurn sigma 1 then
    "uu_"
  else
    match name_binder_annot.binder_name with
    | Anonymous -> "uu_"
    | Name id -> id |> Names.Id.to_string

let rec isabelle_translate_type (env : Environ.env) (sigma : Evd.evar_map) (type_ : EConstr.constr) : isabelle_typ =
  let fn, args = type_ |> EConstr.decompose_app sigma in
  match fn |> EConstr.kind sigma, args |> Array.to_list with

  (* Basic *)
  | Var name, [] ->
    Isabelle_typ_free ("'" ^ (name |> Names.Id.to_string), [])
  | Sort sort, [] when sort |> EConstr.ESorts.is_prop sigma ->
    isabelle_typ_bool
  | Prod (_, var_type, inner), [] when inner |> EConstr.Vars.noccurn sigma 1 ->
    isabelle_typ_fun [
      var_type |> isabelle_translate_type env sigma;
      inner |> isabelle_translate_type env sigma;
    ]

  (* Bool *)
  | _, [] when EConstr.eq_constr sigma fn (get_ref env "core.bool.type") ->
    isabelle_typ_bool

  (* Int *)
  | _, [] when EConstr.eq_constr sigma fn (get_ref env "num.pos.type") ->
    isabelle_typ_num
  | _, [] when EConstr.eq_constr sigma fn (get_ref env "num.Z.type") ->
    isabelle_typ_int

  | _ -> CErrors.user_err Pp.(str "unsupported type:" ++ spc () ++ (type_ |> Printer.pr_econstr_env env sigma))

let rec isabelle_translate_term (env : Environ.env) (sigma : Evd.evar_map) (used_typ_frees : string list) (term : EConstr.constr) : isabelle_term =
  let fn, args = term |> EConstr.decompose_app sigma in
  let f_isabelle, args =
    match fn |> EConstr.kind sigma, args |> Array.to_list with

    (* Basic *)
    | Cast (inner, _, inner_type), args -> (* translate to let to force printing of the type *)
      Isabelle_term_app (
        Isabelle_term_app (
          Isabelle_term_const (
            "HOL.Let",
            isabelle_typ_fun [
              inner_type |> isabelle_translate_type env sigma;
              isabelle_typ_fun [
                inner_type |> isabelle_translate_type env sigma;
                inner_type |> isabelle_translate_type env sigma;
              ];
              inner_type |> isabelle_translate_type env sigma;
            ]
          ),
          inner |> isabelle_translate_term env sigma used_typ_frees
        ),
        Isabelle_term_abs (
          "d",
          inner_type |> isabelle_translate_type env sigma,
          Isabelle_term_bound 0
        )
      ),
      args
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
          isabelle_typ_fun [
            isabelle_typ_fun [
              var_type |> isabelle_translate_type env sigma;
              isabelle_typ_bool;
            ];
            isabelle_typ_bool;
          ]
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
    | _, var_type :: args when EConstr.eq_constr sigma fn (get_ref env "core.ex.type") ->
      Isabelle_term_const (
        "HOL.Ex",
        isabelle_typ_fun [
          isabelle_typ_fun [
            var_type |> isabelle_translate_type env sigma;
            isabelle_typ_bool;
          ];
          isabelle_typ_bool;
        ]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.True.type") ->
      Isabelle_term_const (
        "HOL.True",
        isabelle_typ_bool
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.False.type") ->
      Isabelle_term_const (
        "HOL.False",
        isabelle_typ_bool
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.not.type") ->
      Isabelle_term_const (
        "HOL.Not",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.and.type") ->
      Isabelle_term_const (
        "HOL.conj",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool; isabelle_typ_bool]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.or.type") ->
      Isabelle_term_const (
        "HOL.disj",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool; isabelle_typ_bool]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.iff.type") ->
      Isabelle_term_const (
        "HOL.eq",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool; isabelle_typ_bool]
      ),
      args
    | _, type_ :: args when EConstr.eq_constr sigma fn (get_ref env "core.eq.type") ->
      Isabelle_term_const (
        "HOL.eq",
        isabelle_typ_fun [
          type_ |> isabelle_translate_type env sigma;
          type_ |> isabelle_translate_type env sigma;
          isabelle_typ_bool;
        ]
      ),
      args

    (* Bool *)
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.bool.true") ->
      Isabelle_term_const (
        "HOL.True",
        isabelle_typ_bool
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.bool.false") ->
      Isabelle_term_const (
        "HOL.False",
        isabelle_typ_bool
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.bool.negb") ->
      Isabelle_term_const (
        "HOL.Not",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.bool.andb") ->
      Isabelle_term_const (
        "HOL.conj",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool; isabelle_typ_bool]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "core.bool.orb") ->
      Isabelle_term_const (
        "HOL.disj",
        isabelle_typ_fun [isabelle_typ_bool; isabelle_typ_bool; isabelle_typ_bool]
      ),
      args

    (* Int *)
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.pos.xH") ->
      Isabelle_term_const (
        "Num.num.One",
        isabelle_typ_num
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.pos.xO") ->
      Isabelle_term_const (
        "Num.num.Bit0",
        isabelle_typ_fun [isabelle_typ_num; isabelle_typ_num]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.pos.xI") ->
      Isabelle_term_const (
        "Num.num.Bit1",
        isabelle_typ_fun [isabelle_typ_num; isabelle_typ_num]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.Z0") ->
      Isabelle_term_const (
        "Groups.zero_class.zero",
        isabelle_typ_int
      ),
      args
    | _, [arg]
        when EConstr.eq_constr sigma fn (get_ref env "num.Z.Zpos") &&
          EConstr.eq_constr sigma arg (get_ref env "num.pos.xH") -> (* specialziation *)
      Isabelle_term_const (
        "Groups.one_class.one",
        isabelle_typ_int
      ),
      []
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.Zpos") ->
      Isabelle_term_const (
        "Num.numeral_class.numeral",
        isabelle_typ_fun [isabelle_typ_num; isabelle_typ_int]
      ),
      args
    | _, [arg]
    when EConstr.eq_constr sigma fn (get_ref env "num.Z.Zneg") &&
      EConstr.eq_constr sigma arg (get_ref env "num.pos.xH") -> (* specialziation *)
      Isabelle_term_app (
        Isabelle_term_const (
          "Groups.uminus_class.uminus",
          isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int]
        ),
        Isabelle_term_const (
          "Groups.one_class.one",
          isabelle_typ_int
        )
      ),
      []
    | _, [arg] when EConstr.eq_constr sigma fn (get_ref env "num.Z.Zneg") -> (* specialziation *)
      Isabelle_term_app (
        Isabelle_term_const (
          "Groups.uminus_class.uminus",
          isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int]
        ),
        Isabelle_term_app (
          Isabelle_term_const (
            "Num.numeral_class.numeral",
            isabelle_typ_fun [isabelle_typ_num; isabelle_typ_int]
          ),
          arg |> isabelle_translate_term env sigma used_typ_frees
        )
      ),
      []
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.Zneg") ->
      Isabelle_term_app (
        Isabelle_term_app (
          Isabelle_term_const (
            "Fun.comp",
            isabelle_typ_fun [
              isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int];
              isabelle_typ_fun [isabelle_typ_num; isabelle_typ_int];
              isabelle_typ_fun [isabelle_typ_num; isabelle_typ_int]
            ]
          ),
          Isabelle_term_const (
            "Groups.uminus_class.uminus",
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int]
          )
        ),
        Isabelle_term_const (
          "Num.numeral_class.numeral",
          isabelle_typ_fun [isabelle_typ_num; isabelle_typ_int]
        )
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.add") ->
      Isabelle_term_const (
        "Groups.plus_class.plus",
        isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_int]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.sub") ->
      Isabelle_term_const (
        "Groups.minus_class.minus",
        isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_int]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.opp") ->
      Isabelle_term_const (
        "Groups.uminus_class.uminus",
        isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.mul") ->
      Isabelle_term_const (
        "Groups.times_class.times",
        isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_int]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.le") ->
      Isabelle_term_const (
        "Orderings.ord_class.less_eq",
        isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool]
      ),
      args
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.lt") ->
      Isabelle_term_const (
        "Orderings.ord_class.less",
        isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool]
      ),
      args
    | _, [arg_1; arg_2] when EConstr.eq_constr sigma fn (get_ref env "num.Z.ge") -> (* specialization *)
      Isabelle_term_app (
        Isabelle_term_app (
          Isabelle_term_const (
            "Orderings.ord_class.less_eq",
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool]
          ),
          arg_2 |> isabelle_translate_term env sigma used_typ_frees
        ),
        arg_1 |> isabelle_translate_term env sigma used_typ_frees
      ),
      []
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.ge") ->
      Isabelle_term_app (
        Isabelle_term_const (
          "Relation.conversep",
          isabelle_typ_fun [
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool];
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool];
          ]
        ),
        Isabelle_term_const (
          "Orderings.ord_class.less_eq",
          isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool]
        )
      ),
      args
    | _, [arg_1; arg_2] when EConstr.eq_constr sigma fn (get_ref env "num.Z.gt") -> (* specialization *)
      Isabelle_term_app (
        Isabelle_term_app (
          Isabelle_term_const (
            "Orderings.ord_class.less",
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool]
          ),
          arg_2 |> isabelle_translate_term env sigma used_typ_frees
        ),
        arg_1 |> isabelle_translate_term env sigma used_typ_frees
      ),
      []
    | _, args when EConstr.eq_constr sigma fn (get_ref env "num.Z.gt") ->
      Isabelle_term_app (
        Isabelle_term_const (
          "Relation.conversep",
          isabelle_typ_fun [
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool];
            isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool];
          ]
        ),
        Isabelle_term_const (
          "Orderings.ord_class.less",
          isabelle_typ_fun [isabelle_typ_int; isabelle_typ_int; isabelle_typ_bool]
        )
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
          isabelle_typ_fun [
            isabelle_typ_bool;
            Isabelle_typ_type ("prop", []);
          ]
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
