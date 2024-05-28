theory ProofObligations
  imports Main
begin

(*
1 LIST FORALL PREDICATE
1.1 Definition of LibList.Forall
*)

inductive Forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" for P :: "'a \<Rightarrow> bool" where
    Forall_nil:
    "Forall P Nil"
  | Forall_cons:
    "\<And> x l.
    P x \<Longrightarrow>
    Forall P l \<Longrightarrow>
    Forall P (x # l)"

lemma Forall_nil_eq:
  "\<And>P :: 'a \<Rightarrow> bool.
  Forall P Nil = True"
  by (simp add: Forall_nil)

lemma Forall_one_eq:
  "\<And>(P :: 'a \<Rightarrow> bool) x.
  Forall P (x # Nil) = P x"
  by (metis Forall.simps list.discI list.inject)

lemma Forall_app_eq:
  "\<And>(P :: 'a \<Rightarrow> bool) l1 l2.
  Forall P (l1 @ l2) = (Forall P l1 \<and> Forall P l2)"
  subgoal for P l1 l2
    apply (induction l1)
    subgoal using Forall_nil by auto
    subgoal by (metis Forall.cases Forall_cons append_Cons list.inject list.simps(3))
    done
  done

lemma Forall_rev_eq:
  "\<And>(P :: 'a \<Rightarrow> bool) l.
  Forall P (List.rev l) = Forall P l"
  subgoal for P l
    apply (induction l)
    subgoal by simp
    subgoal by (metis Forall_app_eq append.left_neutral append_Cons rev.simps(2))
    done
  done

(*
1.2 Example goals for Forall
*)

lemma test_Forall_intro:
  "\<And>P l1 l2 l3 (x :: 'a).
  Forall P l1 \<Longrightarrow>
  P x \<Longrightarrow>
  Forall P l2 \<Longrightarrow>
  Forall P l3 \<Longrightarrow>
  Forall P (l1 @ x # l2 @ l3)"
  by (simp add: Forall_app_eq Forall_cons)

lemma test_Forall_inv_list:
  "\<And>P l1 l2 l3 (x :: 'a).
  Forall P (l1 @ x # l2 @ l3) \<Longrightarrow>
  Forall P l2"
  by (metis Forall_app_eq append_Cons append_Nil)

lemma test_Forall_inv_one:
  "\<And>P l1 l2 l3 (x :: 'a).
  Forall P (l1 @ x # l2 @ l3) \<Longrightarrow>
  P x"
  by (metis Forall_app_eq Forall_one_eq append.left_neutral append_Cons)

lemma test_Forall_inv_intro:
  "\<And>P l1 l2 l3 (x :: 'a) (y :: 'a).
  P x \<Longrightarrow>
  Forall P (l1 @ y # l2) \<Longrightarrow>
  Forall P l3 \<Longrightarrow>
  Forall P (l1 @ x # l2 @ y # l3)"
  by (metis Forall_app_eq Forall_cons append_Cons append_Nil)

lemma test_Forall_inst_intro:
  "\<And>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) l1 l2 x a.
  Forall (R a) l1 \<Longrightarrow>
  R a x \<Longrightarrow>
  Forall (R a) l2 \<Longrightarrow>
  Forall (R a) (l1 @ x # l2)"
  by (simp add: Forall_app_eq Forall_cons)

lemma test_Forall_inst_inv:
  "\<And>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) l1 l2 x a.
  Forall (R a) (l1 @ x # l2) \<Longrightarrow>
  R a x"
  by (metis append.right_neutral test_Forall_inv_one)

lemma test_Forall_inst_eta:
  "\<And>(R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (l1 :: 'a list) (l2 :: 'a list) (l3 :: 'a list) x a.
  R a x \<Longrightarrow>
  Forall (\<lambda>b. R a b) l1 \<Longrightarrow>
  Forall (\<lambda>b. R a b) (x # l1)"
  by (simp add: Forall_cons)

(*
1.3 Membership predicate
*)

inductive mem :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" for x :: 'a where
    mem_here:
    "\<And>l.
    mem x (x # l)"
  | mem_next:
    "\<And>y l.
    mem x l \<Longrightarrow>
    mem x (y # l)"

lemma Forall_eq_forall_mem:
  "\<And>P (l :: 'a list).
  Forall P l = (\<forall>x. mem x l \<longrightarrow> P x)"
  subgoal for P l
    apply (induction l)
    subgoal using Forall_nil mem.cases by fastforce
    subgoal by (metis Forall.simps list.distinct(1) list.sel(1) list.sel(3) mem.cases mem_here mem_next)
    done
  done

lemma Forall_mem_inv:
  "\<And>P l (x :: 'a).
  Forall P l \<Longrightarrow>
  mem x l \<Longrightarrow>
  P x"
  by (simp add: Forall_eq_forall_mem)

lemma test_Forall_intro_diverse:
  "\<And>P l1 l2 (x :: 'a).
  Forall P l1 \<Longrightarrow>
  P x \<Longrightarrow>
  (\<And>y. mem y l2 \<Longrightarrow> P y) \<Longrightarrow>
  Forall P (l1 @ x # l2)"
  by (metis Forall_app_eq Forall_cons Forall_eq_forall_mem)

lemma test_Forall_inv_mem:
  "\<And>P l1 l2 l3 (x :: 'a).
  mem x l2 \<Longrightarrow>
  Forall P (l1 @ l2 @ l3) \<Longrightarrow>
  P x"
  by (meson Forall_app_eq Forall_eq_forall_mem)

(*
1.4 Forall on lists of lists
*)

lemma test_Forall_nested_inv_mem:
  "\<And>P (K :: 'a list list) (L :: 'a list) x.
  mem x L \<Longrightarrow>
  mem L K \<Longrightarrow>
  Forall (Forall P) K \<Longrightarrow>
  P x"
  by (meson Forall_mem_inv)

lemma test_Forall_nested_intro_mem:
  "\<And>P (K :: 'a list list).
  (\<And>x L. mem L K \<Longrightarrow> mem x L \<Longrightarrow> P x) \<Longrightarrow>
  Forall (Forall P) K"
  by (simp add: Forall_eq_forall_mem)

(*
1.5 Predicate weakening
*)

definition pred_incl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "pred_incl P Q = (\<forall>x. P x \<longrightarrow> Q x)"

lemma Forall_pred_incl:
  "\<And>(P :: 'a \<Rightarrow> bool) (Q :: 'a \<Rightarrow> bool) l.
  Forall P l \<Longrightarrow>
  pred_incl P Q \<Longrightarrow>
  Forall Q l"
  by (simp add: Forall_eq_forall_mem pred_incl_def)

lemma pred_incl_refl:
  "\<And>(P :: 'a \<Rightarrow> bool).
  pred_incl P P"
  using pred_incl_def by blast

lemma pred_incl_trans:
  "\<And>A (Q :: 'a \<Rightarrow> bool) (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> bool).
  pred_incl P Q \<Longrightarrow>
  pred_incl Q R \<Longrightarrow>
  pred_incl P R"
  by (simp add: pred_incl_def)

consts length_le :: "nat \<Rightarrow> 'a list \<Rightarrow> bool"

axiomatization where pred_incl_length_le:
  "\<And>(n :: nat) (m :: nat).
  n \<le> m \<Longrightarrow>
  pred_incl (length_le n :: 'a list \<Rightarrow> bool) (length_le m :: 'a list \<Rightarrow> bool)"

axiomatization where pred_incl_length_le':
  "\<And>(n :: nat) (m :: nat) (L :: 'a list).
  n \<le> m \<Longrightarrow>
  length_le n L \<Longrightarrow>
  length_le m L"

lemma test_Forall_pred_incl_app:
  "\<And>P Q (l1 :: 'a list) (l2 :: 'a list).
  Forall P l1 \<Longrightarrow>
  Forall Q l2 \<Longrightarrow>
  pred_incl P Q \<Longrightarrow>
  Forall Q (l1 @ l2)"
  using Forall_app_eq Forall_pred_incl by blast

lemma test_Forall_pred_incl_trans_app:
  "\<And>P Q R (l1 :: 'a list) (l2 :: 'a list).
  Forall P l1 \<Longrightarrow>
  Forall Q l2 \<Longrightarrow>
  pred_incl P Q \<Longrightarrow>
  pred_incl Q R \<Longrightarrow>
  Forall R (l1 @ l2)"
  using Forall_pred_incl test_Forall_pred_incl_app by blast

(*
1.6 Weakening on lists of lists
*)

lemma test_Forall_length_le_intro:
  "\<And>n1 n2 n3 m (L :: 'a list) (K1 :: 'a list list) (K3 :: 'a list list).
  n1 \<le> m \<Longrightarrow>
  n2 \<le> m \<Longrightarrow>
  n3 \<le> m \<Longrightarrow>
  Forall (length_le n1) K1 \<Longrightarrow>
  length_le n2 L \<Longrightarrow>
  Forall (length_le n3) K3 \<Longrightarrow>
  Forall (length_le m) (K1 @ L # K3)"
  by (metis Forall_app_eq Forall_cons Forall_pred_incl pred_incl_length_le pred_incl_length_le')

lemma test_Forall_length_le_inv:
  "\<And>n m (L :: 'a list) (K1 :: 'a list list) (K3 :: 'a list list).
  Forall (length_le n) (K1 @ L # K3) \<Longrightarrow>
  n \<le> m \<Longrightarrow>
  length_le m L"
  using pred_incl_length_le' test_Forall_inst_inv by fastforce

(*
2 TRANSITIVE CLOSURE OF BINARY RELATIONS
2.1 Transitive Closure
*)

type_synonym 'a binary = "'a \<Rightarrow> 'a \<Rightarrow> bool"

consts rtclosure :: "'a binary \<Rightarrow> 'a binary"

axiomatization where rtclosure_once:
  "\<And>(R :: 'a binary) x y.
  R x y \<Longrightarrow>
  rtclosure R x y"

axiomatization where rtclosure_refl:
  "\<And>(R :: 'a binary) x.
  rtclosure R x x"

axiomatization where rtclosure_trans:
  "\<And>(R :: 'a binary) y x z.
  rtclosure R x y \<Longrightarrow>
  rtclosure R y z \<Longrightarrow>
  rtclosure R x z"

axiomatization where rtclosure_cases:
  "\<And>(R :: 'a binary) x z.
  R x z \<or>
  x = z \<or>
  (\<exists>y. rtclosure R x y \<and> rtclosure R y z)"

lemma test_rtclosure_r:
  "\<And>(R :: 'a binary) y x z.
  rtclosure R x y \<Longrightarrow>
  R y z \<Longrightarrow>
  rtclosure R x z"
  by (meson rtclosure_once rtclosure_trans)

lemma test_rtclosure_r_provable_eq:
  "\<And>(R :: 'a binary) P y1 y2 x z.
  (\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> a = b) \<Longrightarrow>
  rtclosure R x y1 \<Longrightarrow>
  P y1 \<Longrightarrow>
  P y2 \<Longrightarrow>
  R y2 z \<Longrightarrow>
  rtclosure R x z"
  by (metis test_rtclosure_r)

lemma test_rtclosure_r_arith_rel:
  "\<And>(x :: nat) (y :: nat) (z :: nat) (n :: nat) (m :: nat).
  let R = (\<lambda>a b. b - a \<le> n) in
  rtclosure R x y \<longrightarrow>
  z - y \<le> m \<longrightarrow>
  m \<le> n \<longrightarrow>
  rtclosure R x z"
  by (meson order_trans test_rtclosure_r)

lemma test_rtclosure_trans_arith_eq:
  "\<And>R (x :: nat) (z :: nat) (y1 :: nat) (y2 :: nat).
  rtclosure R x (y1 + y2) \<Longrightarrow>
  rtclosure R (y2 + y1) z \<Longrightarrow>
  rtclosure R x z"
  by (metis add.commute rtclosure_trans)

(*
2.2 Relation inclusion
*)

definition rel_incl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_incl R1 R2 = (\<forall>x y. R1 x y \<longrightarrow> R2 x y)"

lemma rel_incl_rtclosure:
  "\<And>(R1 :: 'a binary) (R2 :: 'a binary).
  rel_incl R1 R2 \<Longrightarrow>
  rel_incl (rtclosure R1) (rtclosure R2)"
  by (metis (full_types) rel_incl_def rtclosure_cases rtclosure_once rtclosure_refl rtclosure_trans)

lemma test_rel_incl_rtclosure:
  "\<And>(R1 :: 'a binary) (R2 :: 'a binary) x y.
  (\<And>a b. R1 a b \<Longrightarrow> R2 a b) \<Longrightarrow>
  rtclosure R1 x y \<Longrightarrow>
  rtclosure R2 x y"
  by (metis rel_incl_def rel_incl_rtclosure)

lemma test_rel_incl_rtclosure_bounded_diff:
  "\<And>(x :: nat) (y :: nat) (n :: nat) (m :: nat).
  n \<le> m \<Longrightarrow>
  rtclosure (\<lambda>a b. b - a \<le> n) x y \<Longrightarrow>
  rtclosure (\<lambda>a b. b - a \<le> m) x y"
  by (metis (no_types, lifting) le_trans test_rel_incl_rtclosure)

(*
3 LIST FILTERING
*)

lemma mem_nil_eq:
  "\<And>(x :: 'a).
  mem x Nil = False"
  using mem.cases by fastforce

lemma mem_cons_eq:
  "\<And>(x :: 'a) (y :: 'a) l.
  mem x (y # l) = (x = y \<or> mem x l)"
  using mem.cases mem_here mem_next by fastforce

consts fold_right :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"

axiomatization where fold_right_nil:
  "\<And>(f :: 'a \<Rightarrow> 'b \<Rightarrow> 'b) i.
  fold_right f i Nil = i"

axiomatization where fold_right_cons:
  "\<And>(f :: 'a \<Rightarrow> 'b \<Rightarrow> 'b) i x l.
  fold_right f i (x # l) = f x (fold_right f i l)"

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "filter P l = fold_right (\<lambda>x acc. if P x then x # acc else acc) Nil l"

lemma filter_nil:
  "\<And>(P :: 'a \<Rightarrow> bool).
  filter P Nil = Nil"
  by (simp add: filter_def fold_right_nil)

lemma filter_cons:
  "\<And>(x :: 'a) l P.
  filter P (x # l) = (if P x then x # filter P l else filter P l)"
  by (simp add: filter_def fold_right_cons)

lemma mem_filter_eq:
  "\<And>(x :: 'a) P l.
  mem x (filter P l) = (mem x l \<and> P x)"
  subgoal for x P l
    apply (induction l)
    subgoal by (simp add: filter_nil mem_nil_eq)
    subgoal by (metis filter_cons mem_cons_eq)
    done
  done

lemma Forall_filter_same:
  "\<And>P (l :: 'a list).
  Forall P (filter P l)"
  by (simp add: Forall_eq_forall_mem mem_filter_eq)

lemma filter_eq_self_of_mem_implies_P:
  "\<And>(l :: 'a list) P.
  (\<And>x. mem x l \<Longrightarrow> P x) \<Longrightarrow>
  filter P l = l"
  subgoal for l P
    apply (induction l)
    subgoal by (simp add: filter_nil)
    subgoal by (simp add: filter_cons mem_cons_eq)
    done
  done

lemma filter_eq_self_of_Forall:
  "\<And>(l :: 'a list) P.
  Forall P l \<Longrightarrow>
  filter P l = l"
  by (metis Forall_mem_inv filter_eq_self_of_mem_implies_P)

lemma Forall_filter_pred_incl:
  "\<And>P Q (l :: 'a list).
  pred_incl P Q \<Longrightarrow>
  Forall Q (filter P l)"
  using Forall_filter_same Forall_pred_incl by blast

lemma length_filter:
  "\<And>(l :: 'a list) P.
  length (filter P l) \<le> length l"
  subgoal for l P
    apply (induction l)
    subgoal by (simp add: filter_nil)
    subgoal by (simp add: filter_cons)
    done
  done

lemma test_mem_filter_eq_arith:
  "\<And>(l :: int list) d n m.
  mem n (filter (\<lambda>x. x \<le> m) l) \<Longrightarrow>
  d \<ge> 0 \<Longrightarrow>
  n \<le> m + d"
  by (simp add: mem_filter_eq)

lemma test_Forall_filter_pred_incl_arith:
  "\<And>n m (l :: int list).
  n \<le> m \<Longrightarrow>
  Forall (\<lambda>x. x \<le> m) (filter (\<lambda>x. x \<le> n) l)"
  by (simp add: Forall_eq_forall_mem mem_filter_eq)

(*
4 PREDICATES ABOUT SORTING
*)

consts sorted :: "'a binary \<Rightarrow> 'a list \<Rightarrow> bool"

axiomatization where sorted_nil:
  "\<And>(R :: 'a binary).
  sorted R Nil"

axiomatization where sorted_one:
  "\<And>(R :: 'a binary) x.
  sorted R (x # Nil)"

axiomatization where sorted_two:
  "\<And>(R :: 'a binary) L x y.
  sorted R (y # L) \<Longrightarrow>
  R x y \<Longrightarrow>
  sorted R (x # y # L)"

axiomatization where sorted_cases:
  "\<And>(R :: 'a binary) L.
  sorted R L \<Longrightarrow>
  L = Nil \<or>
  (\<exists>x. L = x # Nil) \<or>
  (\<exists>x y L'. L = x # y # L' \<and> sorted R (y # L') \<and> R x y)"

definition trans :: "'a binary \<Rightarrow> bool"
  where "trans R = (\<forall>y x z. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

definition head_le :: "'a binary \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where "head_le R x L =
    (case L of
      Nil \<Rightarrow> True
    | y # _ \<Rightarrow> R x y)"

lemma test_head_le_trans:
  "\<And>(R :: 'a binary) x y L.
  trans R \<Longrightarrow>
  head_le R x L \<Longrightarrow>
  R y x \<Longrightarrow>
  head_le R y L"
  by (metis trans_def head_le_def list.case_eq_if)

lemma test_sorted_cons2_inv_cons3:
  "\<And>(R :: 'a binary) x1 x2 x3 L.
  sorted R (x1 # x3 # L) \<Longrightarrow>
  R x1 x2 \<Longrightarrow>
  R x2 x3 \<Longrightarrow>
  sorted R (x1 # x2 # x3 # L)"
  by (metis list.distinct(1) list.sel(3) sorted_cases sorted_two)

lemma test_sorted_cons_eq:
  "\<And>(R :: 'a binary) x L.
  sorted R (x # L) = (head_le R x L \<and> sorted R L)"
  using head_le_def sorted_cases sorted_nil sorted_one sorted_two by fastforce

lemma test_Forall_le_of_sorted_head_le:
  "\<And>(R :: 'a binary) x L.
  trans R \<Longrightarrow>
  sorted R L \<Longrightarrow>
  head_le R x L \<Longrightarrow>
  Forall (R x) L"
  subgoal for R x L
    apply (induction L)
    subgoal by (simp add: Forall_nil)
    subgoal by (metis Forall_cons head_le_def list.simps(5) test_head_le_trans test_sorted_cons_eq)
    done
  done

lemma test_sorted_cons2_inv_cons3_int_with_arith:
  "\<And>x1 x2 x3 d L.
  sorted ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool) (x1 # x3 # L) \<Longrightarrow>
  x1 + d \<le> x2 \<Longrightarrow>
  x2 + d \<le> x3 \<Longrightarrow>
  d \<ge> 0 \<Longrightarrow>
  sorted ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool) (x1 # x2 # x3 # L)"
  by (simp add: test_sorted_cons2_inv_cons3)

(*
5 LOGICAL EQUIVALENCES
*)

lemma not_forall_eq:
  "\<And>(P :: 'a \<Rightarrow> bool).
  (\<not> (\<forall>x. P x)) = (\<exists>x. \<not> P x)"
  by blast

lemma test_not_forall_eq:
  "\<And>(P :: nat \<Rightarrow> bool) (Q :: nat \<Rightarrow> bool).
  \<not> (\<forall>x. Q x) \<Longrightarrow>
  (\<And>x. \<not> Q x \<Longrightarrow> P x) \<Longrightarrow>
  \<exists>a. P a"
  by blast

lemma test_not_forall_eq_arith:
  "\<And>(P :: nat \<Rightarrow> bool) (n :: nat).
  \<not> (\<forall>x. x \<ge> n) \<Longrightarrow>
  (\<And>x. x < n \<Longrightarrow> P x) \<Longrightarrow>
  \<exists>a. P a"
  by blast

lemma not_not_eq:
  "\<And>P.
  (\<not> \<not> P) = P"
  by blast

lemma not_and_eq:
  "\<And>P Q.
  (\<not> (P \<and> Q)) = (\<not> P \<or> \<not> Q)"
  by blast

lemma not_or_eq:
  "\<And>P Q.
  (\<not> (P \<or> Q)) = (\<not> P \<and> \<not> Q)"
  by auto

lemma test_tauto_exploit:
  "\<And>(P :: nat \<Rightarrow> bool) (Q :: nat \<Rightarrow> bool) (n :: nat).
  \<not> (P n \<or> (\<forall>x. \<not> Q x)) \<Longrightarrow>
  (\<forall>x. Q x \<longrightarrow> P n) \<Longrightarrow>
  False"
  by blast

lemma test_tauto_exploit_arith:
  "\<And>(P :: int \<Rightarrow> bool) (n :: int) (d :: int).
  \<not> (P n \<or> (\<forall>x. x < n)) \<Longrightarrow>
  d \<ge> 0 \<Longrightarrow>
  (\<And>x. x \<ge> n - d \<Longrightarrow> P n) \<Longrightarrow>
  False"
  by blast

end
