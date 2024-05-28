theory Acceptor
  imports Main "Nano_JSON.Nano_JSON" "/home/user/Documents/QuickNotes/Find_Axioms"
  keywords "accept" :: diag
begin

ML\<open>
open Nano_Json_Type

type problem = {
  goal: term
}

fun sort_of_json (STRING sort) = sort
  | sort_of_json json = error ("unknown sort: " ^ @{make_string} json)

fun typ_of_json (ARRAY [STRING "Type", STRING name, ARRAY typ_jsons]) =
      Type (name, typ_jsons |> List.map typ_of_json)
  | typ_of_json (ARRAY [STRING "TFree", STRING name, ARRAY sort_jsons]) =
      TFree (name, sort_jsons |> List.map sort_of_json)
  | typ_of_json (ARRAY [STRING "TVar",
                        ARRAY [STRING name, NUMBER (INTEGER index)],
                        ARRAY sort_jsons]) =
      TVar ((name, index), sort_jsons |> List.map sort_of_json)
  | typ_of_json json = error ("unknown typ: " ^ @{make_string} json)

fun term_of_json (ARRAY [STRING "Const", STRING name, typ_json]) =
      Const (name, typ_json |> typ_of_json)
  | term_of_json (ARRAY [STRING "Free", STRING name, typ_json]) =
      Free (name, typ_json |> typ_of_json)
  | term_of_json (ARRAY [STRING "Var",
                         ARRAY [STRING name, NUMBER (INTEGER index)],
                         typ_json]) =
      Var ((name, index), typ_json |> typ_of_json)
  | term_of_json (ARRAY [STRING "Bound", NUMBER (INTEGER i)]) =
      Bound i
  | term_of_json (ARRAY [STRING "Abs", STRING name, typ_json, term_json]) =
      Abs (name, typ_json |> typ_of_json, term_json |> term_of_json)
  | term_of_json (ARRAY [STRING "op $", fn_json, arg_json]) =
      (term_of_json fn_json) $ (term_of_json arg_json)
  | term_of_json json = error ("unknown term: " ^ @{make_string} json)

fun problem_of_json (OBJECT [("datatypes", datatypes_json), ("goal", goal_json)]) =
      {
        goal = term_of_json goal_json
      }
  | problem_of_json json = error ("unknown problem: " ^ @{make_string} json)

fun verify_type_checks ctxt t =
  Thm.cterm_of ctxt t handle exn =>
    if Exn.is_interrupt exn then
      Exn.reraise exn
    else
      let
        val t_string =
          Syntax.string_of_term (ctxt |> Config.put show_types true) t
      in
        Output.error_message ("Term does not pass type checking: " ^ t_string);
        Exn.reraise exn
      end

fun accept_cmd st problem_string = (
  let
    val ctxt = Toplevel.context_of st;
    val problem_json = Nano_Json_Parser.json_of_string problem_string;
    val problem = problem_of_json problem_json
    val goal_string =
      Syntax.string_of_term (ctxt |> Config.put show_types true) (#goal problem)
  in
    verify_type_checks ctxt (#goal problem);
    Output.information (
      Active.sendback_markup_properties
        []
        (cat_lines [
          "lemma \"" ^ goal_string ^ "\"",
          "  try",
          "  sorry"
        ])
    )
  end;
  ()
)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>accept\<close> "accept external goal"
    (Parse.embedded >> (fn input =>
      Toplevel.keep (fn st => accept_cmd st input)))
\<close>

lemma "\<forall>P::bool. P \<or> \<not> P"
  by blast






lemma "\<forall>(x::'A) y::'A_. (\<exists>z::'A. z = x) \<and> (\<exists>z::'A_. z = y)"
  try
  sorry



lemma "0 = 2"
  apply smt


term Nil
term even

typedecl propp
typedecl ('a, 'b) funn (infixr "\<Rightarrow>e" 0)

consts eqq :: "'a \<Rightarrow> 'a \<Rightarrow> prop" (infix "\<equiv>e" 0)
consts impp :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infix "\<Longrightarrow>e" 0)
consts alll :: "('a \<Rightarrow> prop) \<Rightarrow> prop" (binder "\<And>e" 0)

(*
   [(qualify (Binding.make ("eq", \<^here>)), typ "'a \<Rightarrow> 'a \<Rightarrow> prop", infix_ ("\<equiv>", 2)),
    (qualify (Binding.make ("imp", \<^here>)), typ "prop \<Rightarrow> prop \<Rightarrow> prop", infixr_ ("\<Longrightarrow>", 1)),
    (qualify (Binding.make ("all", \<^here>)), typ "('a \<Rightarrow> prop) \<Rightarrow> prop", binder ("\<And>", 0, 0)),
*)

find_consts "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
find_consts "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list"
find_consts "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list option"

fun list_update_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list option" where
"list_update_opt [] i v = None" |
"list_update_opt (x # xs) 0 v = Some (v # xs)" |
"list_update_opt (x # xs) (Suc j) v = map_option ((#) x) (list_update_opt xs j v)"

lemma list_update_length:
  assumes "list_update_opt l i x = Some l0"
  shows "length l0 = length l"
  using assms apply (induction i arbitrary: l l0)
  subgoal for l l0
    using list_update_opt.elims by force
  subgoal for i l l0
    by (smt (verit) Suc_inject Zero_not_Suc length_Cons
        list_update_opt.elims map_option_eq_Some option.distinct(1))
  done

lemma list_update_app_2:
  assumes "length l1 \<le> i"
  shows "list_update_opt (l1 @ l2) i x = map_option (\<lambda>l0. l1 @ l0) (list_update_opt l2 (i - length l1) x)"
  using assms apply (induction i arbitrary: l1)
  subgoal for l1
    by (metis length_0_conv map_option_cong option.map(2) option.map_id self_append_conv2 zero_diff zero_order(2))
  subgoal for i l1
    apply (cases l1)
    subgoal by (simp add: map_option_idI)
    subgoal
      apply (cases l2)
      subgoal apply simp
    subgoal apply simp

lemma
  assumes "length l1 \<le> i"
  shows "list_update_opt (l1 @ l2) i x = map_option (\<lambda>l0. l1 @ l0) (list_update_opt l2 (i - length l1) x)"
  using assms apply (induction i)
  subgoal
    by (metis length_0_conv map_option_cong option.map(2) option.map_id self_append_conv2 zero_diff zero_order(2))
  subgoal
    apply (cases l1)
    subgoal by (simp add: map_option_idI)
    subgoal apply simp
    value "list_update_opt ([5] @ []) 0 (5 :: nat)"
    value "map_option ((@) [5]) (list_update_opt [] (0 - length [5]) (5 :: nat))"

lemma
  "length l1 \<le> i \<Longrightarrow>
  list_update (l1 @ l2) i x = l1 @ (list_update l2 (i - length l1) x)"
  by (simp add: list_update_append)


lemma
  "length l1 \<le> i \<Longrightarrow>
  list_update (l1 @ l2) i x = map_option (\<lambda>l0. l1 @ l0) (list_update l2 (i - length l1) x)"

find_consts "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list"

lemma nat_strong_induction:
  "\<And>(P :: nat \<Rightarrow> bool).
  (\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n) \<Longrightarrow>
  (\<And>n. P n)"
  using nat_less_induct by blast

ML\<open>@{term "\<lambda>x. x"}\<close>
term "PROP A"

accept \<open>{"datatypes":[[{"name":"option","param_names":[],"constructors":[]}]],"goal":["op $",["Const","HOL.Trueprop",["Type","fun",[["Type","HOL.bool",[]],["Type","prop",[]]]]],["op $",["Const","HOL.All",["Type","fun",[["Type","fun",[["TFree","'A",[]],["Type","HOL.bool",[]]]],["Type","HOL.bool",[]]]]],["Abs","x",["TFree","'A",[]],["op $",["Const","HOL.Not",["Type","fun",[["Type","HOL.bool",[]],["Type","HOL.bool",[]]]]],["op $",["op $",["Const","HOL.eq",["Type","fun",[["Type","option",[["TFree","'A",[]]]],["Type","fun",[["Type","option",[["TFree","'A",[]]]],["Type","HOL.bool",[]]]]]]],["op $",["Const","Some",["Type","fun",[["TFree","'A",[]],["Type","option",[["TFree","'A",[]]]]]]],["Bound",0]]],["Const","None",["Type","option",[["TFree","'A",[]]]]]]]]]]}\<close>

lemma "((a = b \<Longrightarrow> a = c) &&& (b = c \<Longrightarrow> False)) \<Longrightarrow> False"
  try

  term "THE x. x = 5"
thm HOL.ext

inductive X where x: X

datatype 'a option =
    None
    | Some (a: 'a)
  and 'a x = X

inductive Fin :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" for A :: "'a \<Rightarrow> bool"
where
empty: "Fin A (\<lambda>_. False)"
| insert: "\<And>a B. A a \<Longrightarrow> Fin A B \<Longrightarrow> Fin A (\<lambda>x. x = a \<or> B x)"

inductive Fin :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" for A :: "'a set"
where
empty: "Fin A {}"
| insert: "\<And>B. a \<in> A \<Longrightarrow> Fin A B \<Longrightarrow> Fin A (insert a B)"

term Fin

definition "eql x y \<longleftrightarrow> (\<forall>P. P x \<longrightarrow> P y)"

lemma eql_eq: "eql = (=)"
proof (rule ext; rule ext; rule iffI)
  fix x y :: 'a
  assume 0: "eql x y"
  show "x = y"
    using 0[unfolded eql_def, THEN allE[of _ "\<lambda>z. x = z"]]
    by blast
next
  fix x y :: 'a
  assume 1: "x = y"
  show "eql x y"
    unfolding eql_def 1
    by blast
qed

declare [[sledgehammer_atp_problem_dest_dir="/tmp/tmp.JXqlFARAVN"]]

lemma "(\<And>x y :: 'a. eql x y) \<Longrightarrow> (\<not>(\<exists>x y :: 'a. \<not> (eql x y)))"
  sledgehammer[debug]



axiomatization eql :: "['a, 'a] \<Rightarrow> bool"

lemma eql_prop: "eql x y \<longleftrightarrow> (\<forall>P. P x \<longrightarrow> P y)"
  sorry

lemma eql_eq: "eql = (=)"
  using eql_prop

inductive eql :: "'a \<Rightarrow> 'a \<Rightarrow> bool" for x :: 'a
  where
eqlc: "eql x x"

find_axioms eql

lemma "(\<lambda>x. lfp (\<lambda>p xa. xa = x)) = (=)"
  unfolding lfp_const by blast

find_theorems eql

datatype 'a option =
    None
  | Some (a: 'a)

ML\<open>@{term "case x of Some y \<Rightarrow> y | None \<Rightarrow> (1 :: int)"}\<close>
term Option.option.case_option

datatype flag123 = Less | Eq | Greater

find_axioms "TYPE(flag123)"
find_axioms ctor_flag123
find_axioms Rep_flag123
find_axioms Abs_flag123

datatype 'a f456 = G | H 'a "'a f456"

find_axioms "TYPE('a f456)"
find_axioms ctor_f456
find_axioms Rep_f456

datatype (set: 'a) list =
  null: Nil ("[]")
| Cons (hd: 'a) (tl: "'a list") (infixr "#" 65)
for
  map: map
  rel: list_all2
  pred: list_all

datatype nat = Zero | Succ nat

primrec replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "replicate Zero _ = []"
| "replicate (Succ n) x = x # replicate n x"

find_axioms replicate

fun replicate2 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "replicate2 a b =
    (case (a, b) of
      (Zero, _) \<Rightarrow> []
    | (Succ n, x) \<Rightarrow> x # replicate n x)"

fun at_least_two :: "nat \<Rightarrow> bool" where
  "at_least_two (Succ (Succ _)) \<longleftrightarrow> True"
| "at_least_two _ \<longleftrightarrow> False"

find_axioms at_least_two
find_axioms at_least_two_sumC
find_axioms at_least_two_graph

datatype mynat = Zero | Succ mynat

find_axioms Succ

definition succ where "succ x = x"
definition succ_succ where "succ_succ = succ \<circ> succ"

find_axioms succ
find_theorems succ

definition Pair_Rep2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "Pair_Rep2 a b = (\<lambda>x y. x = a \<and> y = b)"

definition "prod2 = {f. \<exists>a b. f = Pair_Rep2 (a::'a) (b::'b)}"

typedef ('a, 'b) prod2 ("(_ \<times>/ _)" [21, 20] 20) = "prod2 :: ('a \<Rightarrow> 'b \<Rightarrow> bool) set"
  unfolding prod2_def by auto

definition Pair2 :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) prod2"
  where "Pair2 a b = Abs_prod2 (Pair_Rep2 a b)"

find_axioms prod2
find_axioms "TYPE(('a, 'b) prod2)"
find_axioms Abs_prod2

(*
declare [[ML_print_depth = 100000]]
ML\<open>Theory.all_axioms_of @{theory} |> List.map (fn (i, t) => (i, Syntax.unparse_term @{context} t))\<close>

ML\<open>Theory.all_axioms_of @{theory} |> List.map (fn (i, t) => (i, Syntax.unparse_term (@{context} |> Config.put ML_Print_Depth.print_depth 100) t))\<close>

ML\<open>Config.put\<close>

declare[[ML_print_depth = 10]]

ML\<open>ML_Print_Depth.print_depth\<close>

ML\<open>Theory.all_axioms_of @{theory} |> List.map (fn (i, t) => (i, Syntax.unparse_term @{context} t))\<close>

ML\<open>Thm.add_def\<close>
ML\<open>Theory.add_def\<close>

print_facts

ML\<open>Syntax.parse_term @{context} "1 :: int"\<close>
ML\<open>writeln (Syntax.string_of_term (@{context} |> Config.put show_types true) @{term "let x :: int = 1 in False"})\<close>
term "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"

lemma "(\<le>) \<noteq> (\<le>)\<inverse>\<inverse>"
  try
  sorry

lemma "((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool) \<noteq> (\<le>)\<inverse>\<inverse>"
  by (metis conversep_iff nle_le not_one_le_zero)

*)

lemma "Nil \<noteq> Cons a b"
  thm list.distinct
  thm list.simps
  thm list.nchotomy
thm flag123.distinct
thm flag123.simps
thm flag123.nchotomy

end
