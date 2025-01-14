theory EPEG
  imports Main
begin
type_synonym nonterm = string
type_synonym symbol = "char list"
type_synonym name = "string list"

datatype updateExpr =
  uEmpty |
  uTerm char |
  uNonterm string |
  (* Star expr | *) (* `Star` is syntactic sugar *)
  uNot updateExpr |
  uSeq updateExpr updateExpr |
  uChoice updateExpr updateExpr |
  uBind updateExpr nonterm |
  (* Nu nonterm | *) (* removing Nu for now *)
  Lookup nonterm

datatype expr =
  Empty |
  Term char |
  Nonterm string |
  (* Star expr | *) (* `Star` is syntactic sugar *)
  Not expr |
  Seq expr expr |
  Choice expr expr |
  Bind expr nonterm |
  Mut nonterm updateExpr

fun All :: "expr list \<Rightarrow> expr" where
  "All Nil = Empty" |
  "All (x#xs) = foldl Seq x xs"

fun nontermToExpr :: " nonterm \<Rightarrow> expr" where
 "nontermToExpr nt = foldr (\<lambda> c e. expr.Seq (expr.Term c) e) nt expr.Empty"

(*These two are fundamentally the same function, just repeated for the type synonyms
 as semantic intent annotations *)
fun termListToExpr :: "char list \<Rightarrow> expr" where
 "termListToExpr nt = foldr (\<lambda> c e. expr.Seq (expr.Term c) e) nt expr.Empty"

record EPEG =
  production :: "(nonterm \<times> expr) list"
  table :: "(nonterm \<times> (symbol list)) list"
  scope :: name

fun stripUpdate :: "updateExpr \<Rightarrow> expr" where
  "stripUpdate uEmpty = Empty" |
  "stripUpdate (uTerm c) = Term c" |
  "stripUpdate (uNonterm s) = Nonterm s" |
  "stripUpdate (uNot e) = (Not (stripUpdate e))" |
  "stripUpdate (uSeq e1 e2) = (Seq (stripUpdate e1) (stripUpdate e2))" |
  "stripUpdate (uChoice e1 e2) = (Choice (stripUpdate e1) (stripUpdate e2))" |
  "stripUpdate (uBind e nt) = (Bind (stripUpdate e) nt)" |
  "stripUpdate (Lookup nt) = (Nonterm nt)" 

lemma stripUpdate_decreasing [simp]: "size (stripUpdate u) < Suc (size u)"
proof
 (induction u)
  case uEmpty
  show ?case by auto
  next
    case (uTerm x2)
    show ?case by auto
  next
    case (uNonterm x3)
    show ?case by auto
  next
    case (uNot x4)
    assume ih: "size (stripUpdate x4) < Suc (size x4)"
    show ?case using ih by auto
  next
    case (uSeq x51 x52)
    assume ih1: "size (stripUpdate x51) < Suc (size x51)"
    assume ih2: "size (stripUpdate x52) < Suc (size x52)"
    show ?case using ih1 ih2 by auto
  next
    case (uChoice x61 x62)
    assume ih1: "size (stripUpdate x61) < Suc (size x61)"
    assume ih2: "size (stripUpdate x62) < Suc (size x62)"
    show ?case using ih1 ih2 by auto
  next
    case (uBind x71 x72)
    assume ih: "size (stripUpdate x71) < Suc (size x71)"
    show ?case using ih by auto
  next
    case (Lookup x8)
    show ?case by auto
qed

function (sequential) getSubExpressions :: "expr \<Rightarrow> expr list" where
  "getSubExpressions Empty = Nil " |
  "getSubExpressions (Nonterm _) = Nil" |
  "getSubExpressions (Term _) = Nil" |
  (*"getSubExpressions (Star e) = [e] @ getSubExpressions e" | *)
  "getSubExpressions (Not e) = [e] @ getSubExpressions e" |
  "getSubExpressions (Seq e1 e2) = [e1, e2] @ getSubExpressions e1 @ getSubExpressions e2" |
  "getSubExpressions (Choice e1 e2) = [e1, e2] @ getSubExpressions e1 @ getSubExpressions e2" |
  "getSubExpressions (Mut _ u) = getSubExpressions (stripUpdate u)" |
  "getSubExpressions (Bind e _) = [e] @ getSubExpressions e"
  by pat_completeness auto

fun expressionSet :: "EPEG \<Rightarrow> expr set" where
  "expressionSet \<Gamma> = set (List.bind (map snd (production \<Gamma>)) getSubExpressions)"

fun lookup :: "EPEG \<Rightarrow> nonterm \<Rightarrow> expr" where
  "lookup \<Gamma> nt =
    (case find (\<lambda> p. (fst p) = nt) (production \<Gamma>) of
        None \<Rightarrow> Empty
      | Some p \<Rightarrow> snd p)"

inductive
  elim :: "EPEG \<Rightarrow> updateExpr \<Rightarrow> expr \<Rightarrow> bool" (* and *)
  (* elimUpdate :: "EPEG \<Rightarrow> updateExpr \<Rightarrow> updateExpr \<Rightarrow> bool" *)
where
  Empty: "elim \<Gamma> uEmpty Empty" |
  Term: "elim \<Gamma> (uTerm a) (Term a)" |
  Nonterm: "elim \<Gamma> (uNonterm A) (Nonterm A)" |
  Seq: "elim \<Gamma> e1 e1' \<Longrightarrow> elim \<Gamma> e2 e2' \<Longrightarrow> elim \<Gamma> (uSeq e1 e2) (Seq e1' e2')" |
  Choice: "elim \<Gamma> e1 e1' \<Longrightarrow> elim \<Gamma> e2 e2' \<Longrightarrow> elim \<Gamma> (uChoice e1 e2) (Choice e1' e2')" |
  Not: "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (uNot e) (Not e')" |
  (*Star: "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (Star e) (Star e')" |*)
  Bind: "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (uBind e A) (Bind e' A)" |
  (*Mut : "elimUpdate \<Gamma> P P' \<Longrightarrow> elim \<Gamma> (Mut nt P) (Mut nt P')" |*)

  (*updateExpr : "elim \<Gamma> e e' \<Longrightarrow> elimUpdate \<Gamma> (Expr e) (Expr e')" |*)
  Lookup : "lookup \<Gamma> n = e \<Longrightarrow> elim \<Gamma> (Lookup n) e"
  (*Elim2: "lookup \<Gamma> n = nontermToExpr A \<Longrightarrow> elim \<Gamma> (Nu n) (Nonterm A)" |*) (* nu case *)

code_pred elim.
(*code_pred elimUpdate.*)

(* no equations error - seems like code_pred doesn't work anymore *)
value "elim \<lparr> production = Nil, table = Nil, scope = Nil \<rparr> (uTerm (CHR ''a'')) (Term (CHR ''b''))"

datatype outcome =
  Succ0 |
  Succ1 |
  Fail

inductive
  hook :: "EPEG \<Rightarrow> expr \<Rightarrow> outcome \<Rightarrow> bool" and
  succeeds :: "EPEG \<Rightarrow> expr \<Rightarrow> bool"
where
  Empty: "hook \<Gamma> Empty Succ0" |
  Term_Succ1: "hook \<Gamma> (Term a) Succ1" |
  Term_f: "hook \<Gamma> (Term a) Fail" |
  Nonterm: "lookup \<Gamma> nt = e \<Longrightarrow> hook \<Gamma> e out \<Longrightarrow> hook \<Gamma> (Nonterm nt) out" |
  (*Star_0: "hook \<Gamma> e Fail \<Longrightarrow> hook \<Gamma> (Star e) Succ0" | *)
  (*Star_1: "hook \<Gamma> e Succ1 \<Longrightarrow> hook \<Gamma> (Star e) Succ1" | *)
  Not_0: "hook \<Gamma> e Fail \<Longrightarrow> hook \<Gamma> (Not e) Succ0" |
  Not_f: "succeeds \<Gamma> e \<Longrightarrow> hook \<Gamma> (Not e) Fail" |
  Seq_0: "hook \<Gamma> e1 Succ0 \<Longrightarrow> hook \<Gamma> e2 Succ0 \<Longrightarrow> hook \<Gamma> (Seq e1 e2) Succ0" |
  Seq_1_first: "hook \<Gamma> e1 Succ1 \<Longrightarrow> succeeds \<Gamma> e2 \<Longrightarrow> hook \<Gamma> (Seq e1 e2) Succ1" |
  Seq_1_second: "succeeds \<Gamma> e1 \<Longrightarrow> hook \<Gamma> e2 Succ1 \<Longrightarrow> hook \<Gamma> (Seq e1 e2) Succ1" |
  Seq_f_first: "hook \<Gamma> e1 Fail \<Longrightarrow> hook \<Gamma> (Seq e1 e2) Fail" |
  Seq_f_second: "succeeds \<Gamma> e1 \<Longrightarrow> hook \<Gamma> e2 Fail \<Longrightarrow> hook \<Gamma> (Seq e1 e2) Fail" |
  Choice_Succ0: "hook \<Gamma> e1 Succ0 \<Longrightarrow> hook \<Gamma> (Choice e1 e2) Succ0" |
  Choice_Succ1: "hook \<Gamma> e1 Succ1 \<Longrightarrow> hook \<Gamma> (Choice e1 e2) Succ1" |
  Choice_second: "hook \<Gamma> e1 Fail \<Longrightarrow> hook \<Gamma> e2 out \<Longrightarrow> hook \<Gamma> (Choice e1 e2) out" |
  Mut_expr: "hook \<Gamma> u out \<Longrightarrow> hook \<Gamma> (Mut A (Expr u)) out" |
  Mut_Lookup: "hook \<Gamma> (Nonterm n) out \<Longrightarrow> hook \<Gamma> (Mut A (Lookup n)) out" |
  Bind_main: "hook \<Gamma> e out \<Longrightarrow> hook \<Gamma> (Bind e i) out" |
  Bind_update_1: "(Bind e i) \<in>  (expressionSet \<Gamma>) \<Longrightarrow> hook \<Gamma> e Succ1 \<Longrightarrow> hook \<Gamma> (Nonterm i) Succ1" |
  Bind_update_f: "(Bind e i) \<in> (expressionSet \<Gamma>) \<Longrightarrow> hook \<Gamma> e Fail \<Longrightarrow> hook \<Gamma> (Nonterm i) Fail" |
  Bind_update_0: "(Bind e i) \<in> (expressionSet \<Gamma>) \<Longrightarrow> hook \<Gamma> e Succ0 \<Longrightarrow> hook \<Gamma> (Nonterm i) Succ0" |
  (* NuAnythingGoes : "hook \<Gamma> (Nu n) out" | *)

  WithoutConsuming: "hook \<Gamma> e Succ0 \<Longrightarrow> succeeds \<Gamma> e" |
  WithConsuming: "hook \<Gamma> e Succ1 \<Longrightarrow> succeeds \<Gamma> e"

code_pred hook.
code_pred succeeds.

inductive_cases EmptyE[elim!]: "hook \<Gamma> Empty out"
inductive_cases TermE[elim!]: "hook \<Gamma> (Term a) out"
inductive_cases NontermE[elim!]: "hook \<Gamma> (Nonterm nt) out"
(* inductive_cases StarE[elim!]: "hook \<Gamma> (Star e) out" *)
inductive_cases NotE[elim!]: "hook \<Gamma> (Not e) out"
inductive_cases SeqE[elim!]: "hook \<Gamma> (Seq e1 e2) out"
inductive_cases ChoiceE[elim!]: "hook \<Gamma> (Choice e1 e2) out"
inductive_cases MutE[elim!]: "hook \<Gamma> (Mut A u) out"
inductive_cases LookupE[elim!]: "hook \<Gamma> (Gamma n) out"
inductive_cases BindE[elim!]: "hook \<Gamma> (Delta e i) out"
inductive_cases SuccE[elim!]: "succeeds \<Gamma> e"

lemma "hook \<Gamma> Empty out \<Longrightarrow> out = Succ0"
by blast
lemma "hook \<Gamma> (Term a) out \<Longrightarrow> (out = Succ1 \<or> out = Fail)"
by blast
(* This needs cases corresponding to Mut and Bind_update_{1,f,0} in the conclusion to be complete. *)
(*lemma "hook \<Gamma> (Nonterm nt) out \<Longrightarrow> (hook \<Gamma> e out \<and> lookup \<Gamma> nt = e)"
by blast*)
(* lemma "hook \<Gamma> (Star e) out \<Longrightarrow> (out = Succ0 \<or> out = Succ1)"
by blast *)
lemma "hook \<Gamma> (Not e) out \<Longrightarrow> (out = Succ0 \<or> out = Fail)"
by blast
lemma "hook \<Gamma> (Seq e1 e2) Succ0 \<Longrightarrow> (hook \<Gamma> e1 Succ0 \<and> hook \<Gamma> e2 Succ0)"
by blast
lemma "hook \<Gamma> (Seq e1 e2) Succ1 \<Longrightarrow> ((hook \<Gamma> e1 Succ1 \<and> succeeds \<Gamma> e2) \<or> (succeeds \<Gamma> e1 \<and> hook \<Gamma> e2 Succ1))"
by blast
lemma "hook \<Gamma> (Seq e1 e2) Fail \<Longrightarrow> (hook \<Gamma> e1 Fail \<or> (succeeds \<Gamma> e1 \<and> hook \<Gamma> e2 Fail))"
by blast
lemma "hook \<Gamma> (Choice e1 e2) Succ0 \<Longrightarrow> (hook \<Gamma> e1 Succ0 \<or> (hook \<Gamma> e1 Fail \<and> hook \<Gamma> e2 Succ0))"
by blast
lemma "hook \<Gamma> (Choice e1 e2) Succ1 \<Longrightarrow> (hook \<Gamma> e1 Succ1 \<or> (hook \<Gamma> e1 Fail \<and> hook \<Gamma> e2 Succ1))"
by blast
lemma "hook \<Gamma> (Choice e1 e2) Fail \<Longrightarrow> (hook \<Gamma> e1 Fail \<and> hook \<Gamma> e2 Fail)"
by blast
lemma "hook \<Gamma> (Bind e i) out \<Longrightarrow> hook \<Gamma> e out"
by blast
lemma "succeeds \<Gamma> e \<Longrightarrow> (hook \<Gamma> e Succ0 \<or> hook \<Gamma> e Succ1)"
by blast

(* lemma hook_inv_elim :
  "elim \<Gamma> e e' \<Longrightarrow> (\<forall> out. hook \<Gamma> e out \<longleftrightarrow> hook \<Gamma> e' out)"
proof
  (induction rule: elim_elimUpdate.inducts(1))
    case Empty
    show ?case by auto
  next
    case Term
    show ?case by auto
  next
    case Nonterm
    show ?case by auto
  next
    case (Seq \<Gamma> e1 e1' e2 e2')
    assume ih1: "elim \<Gamma> e1 e1'"
    assume ih2: "elim \<Gamma> e2 e2'"
    assume r1: "restricted (Seq e1 e2)"
    from r1 have aux1: "restricted e1" using restricted.cases by auto
    from r1 have aux2: "restricted e2" using restricted.cases by auto
    assume r2: "restricted (Seq e1' e2')"
    from r2 have aux1': "restricted e1'" using restricted.cases by auto
    from r2 have aux2': "restricted e2'" using restricted.cases by auto
    assume "restricted e1 \<Longrightarrow> restricted e1' \<Longrightarrow> \<forall>out. hook \<Gamma> e1 out = hook \<Gamma> e1' out"
    then have ih3: "\<forall>out. hook \<Gamma> e1 out = hook \<Gamma> e1' out" using aux1 aux1' by blast
    assume "restricted e2 \<Longrightarrow> restricted e2' \<Longrightarrow> \<forall>out. hook \<Gamma> e2 out = hook \<Gamma> e2' out"
    then have ih4: "\<forall>out. hook \<Gamma> e2 out = hook \<Gamma> e2' out" using aux2 aux2' by blast
    show ?case
    proof
      fix out
      show "hook \<Gamma> (Seq e1 e2) out = hook \<Gamma> (Seq e1' e2') out"
      proof (cases out)
        assume "out = Succ0"
        thus "hook \<Gamma> (Seq e1 e2) out = hook \<Gamma> (Seq e1' e2') out" using Seq_0 ih3 ih4 by blast
      next
        assume h: "out = Succ1"
        show "hook \<Gamma> (Seq e1 e2) out = hook \<Gamma> (Seq e1' e2') out"
        proof
          assume k: "hook \<Gamma> (Seq e1 e2) out"
          from h k have "(hook \<Gamma> e1 Succ1 \<and> succeeds \<Gamma> e2) \<or> (succeeds \<Gamma> e1 \<and> hook \<Gamma> e2 Succ1)" by blast
          then have "(hook \<Gamma> e1' Succ1 \<and> succeeds \<Gamma> e2') \<or> (succeeds \<Gamma> e1' \<and> hook \<Gamma> e2' Succ1)" using ih3 ih4 succeeds.simps by auto
          thus "hook \<Gamma> (Seq e1' e2') out" by (metis Seq_1_first Seq_1_second h)
        next
          assume k: "hook \<Gamma> (Seq e1' e2') out"
          from h k have "(hook \<Gamma> e1' Succ1 \<and> succeeds \<Gamma> e2') \<or> (succeeds \<Gamma> e1' \<and> hook \<Gamma> e2' Succ1)" by blast
          then have "(hook \<Gamma> e1 Succ1 \<and> succeeds \<Gamma> e2) \<or> (succeeds \<Gamma> e1 \<and> hook \<Gamma> e2 Succ1)" using ih3 ih4 succeeds.simps by auto
          thus "hook \<Gamma> (Seq e1 e2) out" by (metis Seq_1_first Seq_1_second h)
        qed
      next
        assume h: "out = Fail"
        show "hook \<Gamma> (Seq e1 e2) out = hook \<Gamma> (Seq e1' e2') out"
        proof
          assume k: "hook \<Gamma> (Seq e1 e2) out"
          from h k have "hook \<Gamma> e1 Fail \<or> (succeeds \<Gamma> e1 \<and> hook \<Gamma> e2 Fail)" by blast
          then have "hook \<Gamma> e1' Fail \<or> (succeeds \<Gamma> e1' \<and> hook \<Gamma> e2' Fail)" using ih3 ih4 succeeds.simps by auto
          thus "hook \<Gamma> (Seq e1' e2') out" by (metis Seq_f_first Seq_f_second h)
        next
          assume k: "hook \<Gamma> (Seq e1' e2') out"
          from h k have "hook \<Gamma> e1' Fail \<or> (succeeds \<Gamma> e1' \<and> hook \<Gamma> e2' Fail)" by blast
          then have "hook \<Gamma> e1 Fail \<or> (succeeds \<Gamma> e1 \<and> hook \<Gamma> e2 Fail)" using ih3 ih4 succeeds.simps by auto
          thus "hook \<Gamma> (Seq e1 e2) out" by (metis Seq_f_first Seq_f_second h)
        qed
      qed
    qed
  next
    case (Choice \<Gamma> e1 e1' e2 e2')
    assume ih1: "elim \<Gamma> e1 e1'"
    assume ih2: "elim \<Gamma> e2 e2'"
    assume r1: "restricted (Choice e1 e2)"
    from r1 have aux1: "restricted e1" using restricted.cases by auto
    from r1 have aux2: "restricted e2" using restricted.cases by auto
    assume r2: "restricted (Choice e1' e2')"
    from r2 have aux1': "restricted e1'" using restricted.cases by auto
    from r2 have aux2': "restricted e2'" using restricted.cases by auto
    assume "restricted e1 \<Longrightarrow> restricted e1' \<Longrightarrow> \<forall>out. hook \<Gamma> e1 out = hook \<Gamma> e1' out"
    then have ih3: "\<forall>out. hook \<Gamma> e1 out = hook \<Gamma> e1' out" using aux1 aux1' by blast
    assume "restricted e2 \<Longrightarrow> restricted e2' \<Longrightarrow> \<forall>out. hook \<Gamma> e2 out = hook \<Gamma> e2' out"
    then have ih4: "\<forall>out. hook \<Gamma> e2 out = hook \<Gamma> e2' out" using aux2 aux2' by blast
    show ?case
    proof
      fix out
      show "hook \<Gamma> (Choice e1 e2) out = hook \<Gamma> (Choice e1' e2') out"
      proof (cases out)
        assume h: "out = Succ0"
        show "hook \<Gamma> (Choice e1 e2) out = hook \<Gamma> (Choice e1' e2') out"
        proof
          assume k: "hook \<Gamma> (Choice e1 e2) out"
          from h k ih3 ih4 have "hook \<Gamma> e1' Succ0 \<or> (hook \<Gamma> e1' Fail \<and> hook \<Gamma> e2' Succ0)" by blast
          thus "hook \<Gamma> (Choice e1' e2') out" by (metis Choice_Succ0 Choice_second h)
        next
          assume k: "hook \<Gamma> (Choice e1' e2') out"
          from h k ih3 ih4 have "hook \<Gamma> e1 Succ0 \<or> (hook \<Gamma> e1 Fail \<and> hook \<Gamma> e2 Succ0)" by blast
          thus "hook \<Gamma> (Choice e1 e2) out" by (metis Choice_Succ0 Choice_second h)
        qed
      next
        assume h: "out = Succ1"
        show "hook \<Gamma> (Choice e1 e2) out = hook \<Gamma> (Choice e1' e2') out"
        proof
          assume k: "hook \<Gamma> (Choice e1 e2) out"
          from h k ih3 ih4 have "hook \<Gamma> e1' Succ1 \<or> (hook \<Gamma> e1' Fail \<and> hook \<Gamma> e2' Succ1)" by blast
          thus "hook \<Gamma> (Choice e1' e2') out" by (metis Choice_Succ1 Choice_second h)
        next
          assume k: "hook \<Gamma> (Choice e1' e2') out"
          from h k ih3 ih4 have "hook \<Gamma> e1 Succ1 \<or> (hook \<Gamma> e1 Fail \<and> hook \<Gamma> e2 Succ1)" by blast
          thus "hook \<Gamma> (Choice e1 e2) out" by (metis Choice_Succ1 Choice_second h)
        qed
      next
        assume h: "out = Fail"
        thus "hook \<Gamma> (Choice e1 e2) out = hook \<Gamma> (Choice e1' e2') out" using Choice_second ih3 ih4 by blast
      qed
    qed
  next
    case (Not \<Gamma> e e')
    assume ih1: "elim \<Gamma> e e'"
    assume "restricted (Not e)"
    then have aux: "restricted e" using restricted.cases by auto
    assume "restricted (Not e')"
    then have aux': "restricted e'" using restricted.cases by auto
    assume "restricted e \<Longrightarrow> restricted e' \<Longrightarrow> \<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out"
    then have ih2: "\<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out" using aux aux' by blast
    show ?case
    proof
      fix out
      show "hook \<Gamma> (expr.Not e) out = hook \<Gamma> (expr.Not e') out"
      proof (cases out)
        assume h: "out = Succ0"
        thus "hook \<Gamma> (expr.Not e) out = hook \<Gamma> (expr.Not e') out" using Not_0 ih2 by auto
      next
        assume h: "out = Succ1"
        thus "hook \<Gamma> (expr.Not e) out = hook \<Gamma> (expr.Not e') out" by auto
      next
        assume h: "out = Fail"
        thus "hook \<Gamma> (expr.Not e) out = hook \<Gamma> (expr.Not e') out" using Not_f ih2 succeeds.simps by auto
      qed
    qed
  next
    case (Star \<Gamma> e e')
    assume ih1: "elim \<Gamma> e e'"
    assume "restricted (Star e)"
    then have aux: "restricted e" using restricted.cases by auto
    assume "restricted (Star e')"
    then have aux': "restricted e'" using restricted.cases by auto
    assume "restricted e \<Longrightarrow> restricted e' \<Longrightarrow> \<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out"
    then have ih2: "\<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out" using aux aux' by blast
    show ?case
    proof
      fix out
      show "hook \<Gamma> (expr.Star e) out = hook \<Gamma> (expr.Star e') out"
      proof (cases out)
        assume "out = Succ0"
        thus "hook \<Gamma> (expr.Star e) out = hook \<Gamma> (expr.Star e') out" using Star_0 ih2 by auto
      next
        assume "out = Succ1"
        thus "hook \<Gamma> (expr.Star e) out = hook \<Gamma> (expr.Star e') out" using Star_1 ih2 by auto
      next
        assume "out = Fail"
        thus "hook \<Gamma> (expr.Star e) out = hook \<Gamma> (expr.Star e') out" by auto
      qed
    qed
  next
    case (Delta \<Gamma> e e' A)
    assume ih1: "elim \<Gamma> e e'"
    assume "restricted (Delta e A)"
    then have aux: "restricted e" using restricted.cases by auto
    assume "restricted (Delta e' A)"
    then have aux': "restricted e'" using restricted.cases by auto
    assume "restricted e \<Longrightarrow> restricted e' \<Longrightarrow> \<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out"
    then have ih2: "\<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out" using aux aux' by blast
    show ?case
    proof
      fix out
      show "hook \<Gamma> (Delta e A) out = hook \<Gamma> (Delta e' A) out" using Bind_main ih2 by auto
    qed
  next
    case (Elim1 \<Gamma> n e)
    assume "restricted (Gamma n)"
    thus ?case using restricted.cases by auto
  next
    case (Elim2 \<Gamma> n A)
    assume "restricted (Nu n)"
    thus ?case using restricted.cases by auto
  next
    case (Mut_Nil \<Gamma> e e')
    assume ih1: "elim \<Gamma> e e'"
    assume "restricted (Mu e [])"
    then have aux: "restricted e" using restricted.cases by auto
    assume "restricted (Mu e' [])"
    then have aux': "restricted e'" using restricted.cases by auto
    assume "restricted e \<Longrightarrow> restricted e' \<Longrightarrow> \<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out"
    then have ih2: "\<forall>out. hook \<Gamma> e out = hook \<Gamma> e' out" using aux aux' by blast
    show ?case using Mut_main ih2 by auto
  next
    case (Mut_Cons \<Gamma> ni ni' ei ei' e P e' P')
    assume "restricted (Mu e ((ni, ei) # P))"
    then have "restricted e" using restricted.cases by auto
    then have ih1: "restricted (Mu e P)" using restricted.Mu by auto
    assume "restricted (Mu e' ((ni', ei') # P'))"
    then have "restricted e'" using restricted.cases by auto
    then have ih2: "restricted (Mu e' P')" using restricted.Mu by auto
    assume "restricted (Mu e P) \<Longrightarrow> restricted (Mu e' P') \<Longrightarrow> \<forall>out. hook \<Gamma> (Mu e P) out = hook \<Gamma> (Mu e' P') out"
    then have ih3: "\<forall>out. hook \<Gamma> (Mu e P) out = hook \<Gamma> (Mu e' P') out" using ih1 ih2 by auto
    show ?case by (meson MutE Mut_main ih3)
qed *)

inductive step :: "expr \<Rightarrow> char list \<Rightarrow> EPEG \<Rightarrow> string option \<Rightarrow> (nonterm \<times> expr) list \<Rightarrow> bool" where
  Term_s: "step (Term a) (a # x) \<Gamma> (Some [a]) (production \<Gamma>)" |
  Term_f_neq: "a \<noteq> b \<Longrightarrow> step (Term a) (b # x) \<Gamma> None (production \<Gamma>)" |
  Term_f_empty: "step (Term _) [] \<Gamma> None (production \<Gamma>)" |
  Nonterm: "lookup \<Gamma> A = e \<Longrightarrow> step e x \<Gamma> out R \<Longrightarrow> step (Nonterm A) x \<Gamma> out R" |
  Empty: "step Empty x \<Gamma> (Some []) (production \<Gamma>)" |
  Seq_s: "step e1 (x1 @ x2 @ y) \<Gamma> (Some x1) R1 \<Longrightarrow>
          step e2 (x2 @ y) (\<Gamma>\<lparr>production := R1\<rparr>) (Some x2) R2 \<Longrightarrow>
          step (Seq e1 e2) (x1 @ x2 @ y) \<Gamma> (Some (x1 @ x2)) R2" |
  Seq_f_fst: "step e1 x \<Gamma> None R \<Longrightarrow> step (Seq e1 e2) x \<Gamma> None (production \<Gamma>)" |
  Seq_f_snd: "step e1 (x @ y) \<Gamma> (Some x) R1 \<Longrightarrow>
              step e2 y (\<Gamma>\<lparr>production := R1\<rparr>) None R2 \<Longrightarrow>
              step (Seq e1 e2) (x @ y) \<Gamma> None (production \<Gamma>)" |
  Choice_s_fst: "step e1 (x @ y) \<Gamma> (Some x) R \<Longrightarrow> step (Choice e1 e2) (x @ y) \<Gamma> (Some x) R" |
  Choice_s_snd: "step e1 (x @ y) \<Gamma> None R1 \<Longrightarrow>
                 step e2 (x @ y) \<Gamma> (Some x) R2 \<Longrightarrow>
                 step (Choice e1 e2) (x @ y) \<Gamma> (Some x) R2" |
  Choice_f: "step e1 x \<Gamma> None R1 \<Longrightarrow>
             step e2 x \<Gamma> None R2 \<Longrightarrow>
             step (Choice e1 e2) x \<Gamma> None (production \<Gamma>)" |
  Not_s: "step e x \<Gamma> None R \<Longrightarrow> step (Not e) x \<Gamma> (Some []) (production \<Gamma>)" |
  Not_f: "step e (x @ y) \<Gamma> (Some x) R \<Longrightarrow> step (Not e) (x @ y) \<Gamma> None (production \<Gamma>)" |
  (*Star_base: "step e x \<Gamma> None R \<Longrightarrow> step (Star e) x \<Gamma> (Some []) (production \<Gamma>)" |
  Star_ind: "step e (x1 @ x2 @ y) \<Gamma> (Some x1) R1 \<Longrightarrow>
             step (Star e) (x2 @ y) (\<Gamma>\<lparr>production := R1\<rparr>) (Some x2) R2 \<Longrightarrow>
             step (Star e) (x1 @ x2 @ y) \<Gamma> (Some (x1 @ x2)) R2" | *)
  Bind_s: "step e (x @ y) \<Gamma> (Some x) R \<Longrightarrow>
           step (Bind e i) (x @ y) \<Gamma> (Some x) ((i,termListToExpr x)#R)" |
  Bind_f: "step e x \<Gamma> None R \<Longrightarrow> step (Bind e i) x \<Gamma> None (production \<Gamma>)" |
  Mod: "elim \<Gamma> e e' \<Longrightarrow>
        step (Mut nt u) x \<Gamma> (Some []) ((nt, e') # (filter (\<lambda> p . fst p \<noteq> nt) (production \<Gamma>)))"

code_pred step.

(* Lemma 5.8 *)
lemma assumes hStep : "step e i \<Gamma> res R"
      shows "hook \<Gamma> e' out \<longleftrightarrow> hook (\<Gamma> \<lparr> production := R\<rparr>) e' out"
      (*induction on the proof witness hStep *)
      using hStep
      apply(induct rule: step.induct)
      apply(simp_all) (* prove all cases with immutable \<Gamma> *)
    proof
      (* Bind_s forward case *)
      fix e x y \<Gamma> R i
      assume "step e (x @ y) \<Gamma> (Some x) R"
      assume ih : "hook \<Gamma> e' out = hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      assume h : "hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      show "hook (\<Gamma>\<lparr>production := (i, foldr (\<lambda>c. Seq (Term c)) x Empty) # R\<rparr>) e' out" sorry
    next
      (* Bind_s backward case *)
      fix e x y \<Gamma> R i
      assume "step e (x @ y) \<Gamma> (Some x) R"
      assume ih : "hook \<Gamma> e' out = hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      assume h : "hook (\<Gamma>\<lparr>production := (i, foldr (\<lambda>c. Seq (Term c)) x Empty) # R\<rparr>) e' out"
      have "hook \<Gamma> e' out" sorry
      thus "hook (\<Gamma>\<lparr>production := R\<rparr>) e' out" by (simp add: ih)
    next
      (* Mod case *)
      show "\<And>\<Gamma> e e'a nt. elim \<Gamma> e e'a \<Longrightarrow> hook \<Gamma> e' out = hook (\<Gamma>\<lparr>production := (nt, e'a) # filter (\<lambda>p. fst p \<noteq> nt) (production \<Gamma>)\<rparr>) e' out" sorry
    qed
end
