theory EPEG
  imports Main
begin
type_synonym nonterm = string
type_synonym identifier = string
type_synonym symbol = "char list"
type_synonym name = "string list"

datatype expr =
  Empty |
  Term char |
  Nonterm string |
  Star expr |
  Not expr |
  Seq expr expr |
  Choice expr expr |
  Mu expr "((nonterm \<times> expr) list)" |
  Delta expr nonterm |
  Nu nonterm |
  Gamma nonterm

fun All :: "expr list \<Rightarrow> expr" where
  "All Nil = Empty" |
  "All (x#xs) = foldl Seq x xs"

fun nontermToExpr :: " nonterm \<Rightarrow> expr" where
 "nontermToExpr nt = foldr (\<lambda> c e. expr.Seq (expr.Term c) e) nt expr.Empty"

(*These two are fundamentally the same function, just repeated for the type synonyms
 as semantic intent annotations *)
fun termListToExpr :: "char list \<Rightarrow> expr" where
 "termListToExpr nt = foldr (\<lambda> c e. expr.Seq (expr.Term c) e) nt expr.Empty"

(* We only allow Nu and Gamma to appear in the 
  list of updates for a Mu. This ensures this
  property by omitting constructors for these two
  combinators, and checking recursively that they
  are restricted *except* for the expressions
  appearing in the update list P for Mu *)
inductive restricted :: "expr \<Rightarrow> bool" where
  Empty: "restricted Empty" |
  Term: "restricted (Term a)" |
  Nonterm: "restricted (Nonterm A)" |
  Star: "restricted e \<Longrightarrow> restricted (Star e)" |
  Not: "restricted e \<Longrightarrow> restricted (Not e)" |
  Seq: "restricted e1 \<Longrightarrow> restricted e2 \<Longrightarrow> restricted (Seq e1 e2)" |
  Choice: "restricted e1 \<Longrightarrow> restricted e2 \<Longrightarrow> restricted (Choice e1 e2)" |
  Mu: "restricted e \<Longrightarrow> restricted (Mu e P)" |
  Delta: "restricted e \<Longrightarrow> restricted (Delta e A)"

code_pred restricted.

record EPEG =
  production :: "(nonterm \<times> expr) list"
  table :: "(nonterm \<times> (symbol list)) list"
  scope :: name

fun getSubExpressions :: "expr \<Rightarrow> expr list" where
  "getSubExpressions Empty = Nil " |
  "getSubExpressions (Nonterm _) = Nil" |
  "getSubExpressions (Term _) = Nil" |
  "getSubExpressions (Star e) = [e] @ getSubExpressions e" |
  "getSubExpressions (Not e) = [e] @ getSubExpressions e" |
  "getSubExpressions (Seq e1 e2) = [e1, e2] @ getSubExpressions e1 @ getSubExpressions e2" |
  "getSubExpressions (Choice e1 e2) = [e1, e2] @ getSubExpressions e1 @ getSubExpressions e2" |
  "getSubExpressions (Mu e us) = (e # map snd us) @ getSubExpressions e @ concat (map getSubExpressions (map snd us))" |
  "getSubExpressions (Delta e _) = [e] @ getSubExpressions e" |
  "getSubExpressions (Gamma _) = Nil" |
  "getSubExpressions (Nu _) = Nil"

fun expressionSet :: "EPEG \<Rightarrow> expr set" where
  "expressionSet \<Gamma> = set (List.bind (map snd (production \<Gamma>)) getSubExpressions)"

definition restrictedEPEG :: "EPEG \<Rightarrow> bool" where
  "restrictedEPEG \<Gamma> \<equiv> \<forall> e \<in> (expressionSet \<Gamma>). restricted e"

fun lookup :: "EPEG \<Rightarrow> nonterm \<Rightarrow> expr" where
  "lookup \<Gamma> nt =
    (case find (\<lambda> p. (fst p) = nt) (production \<Gamma>) of
        None \<Rightarrow> Empty
      | Some p \<Rightarrow> snd p)"

inductive elim :: "EPEG \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" where
  Empty: "elim \<Gamma> Empty Empty" |
  Term: "elim \<Gamma> (Term a) (Term a)" |
  Nonterm: "elim \<Gamma> (Nonterm A) (Nonterm A)" |
  Seq: "elim \<Gamma> e1 e1' \<Longrightarrow> elim \<Gamma> e2 e2' \<Longrightarrow> elim \<Gamma> (Seq e1 e2) (Seq e1' e2')" |
  Choice: "elim \<Gamma> e1 e1' \<Longrightarrow> elim \<Gamma> e2 e2' \<Longrightarrow> elim \<Gamma> (Choice e1 e2) (Choice e1' e2')" |
  Not: "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (Not e) (Not e')" |
  Star: "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (Star e) (Star e')" |
  Delta: "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (Delta e A) (Delta e' A)" |
  Elim1: "lookup \<Gamma> n = e \<Longrightarrow> elim \<Gamma> (Gamma n) e" |
  Elim2: "lookup \<Gamma> n = nontermToExpr A \<Longrightarrow> elim \<Gamma> (Nu n) (Nonterm A)" |
  Mut_Nil : "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (Mu e Nil) (Mu e' Nil)" |
  Mut_Cons : "elim \<Gamma> (Nonterm ni) (Nonterm ni') \<Longrightarrow>
              elim \<Gamma> ei ei' \<Longrightarrow> elim \<Gamma> (Mu e P) (Mu e' P') \<Longrightarrow>
              elim \<Gamma> (Mu e ((ni,ei)#P)) (Mu e' ((ni',ei')#P'))"

code_pred elim.

value "elim \<lparr> production = Nil, table = Nil, scope = Nil \<rparr> (Term (CHR ''a'')) (Term (CHR ''b''))"

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
  Star_0: "hook \<Gamma> e Fail \<Longrightarrow> hook \<Gamma> (Star e) Succ0" |
  Star_1: "hook \<Gamma> e Succ1 \<Longrightarrow> hook \<Gamma> (Star e) Succ1" |
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
  Mut_main: "hook \<Gamma> e out \<Longrightarrow> hook \<Gamma> (Mu e us) out" |
  Mut_update: "(Mu e us) \<in> (expressionSet \<Gamma>) \<Longrightarrow> List.member us (n, u) \<Longrightarrow> hook \<Gamma> u out \<Longrightarrow> hook \<Gamma> (Nonterm n) out" |
  Lookup: "hook \<Gamma> (Nonterm n) out \<Longrightarrow> hook \<Gamma> (Gamma n) out" |
  Bind_main: "hook \<Gamma> e out \<Longrightarrow> hook \<Gamma> (Delta e i) out" |
  Bind_update_1: "(Delta e i) \<in>  (expressionSet \<Gamma>) \<Longrightarrow> hook \<Gamma> e Succ1 \<Longrightarrow> hook \<Gamma> (Nonterm i) Succ1" |
  Bind_update_f: "(Delta e i) \<in> (expressionSet \<Gamma>) \<Longrightarrow> hook \<Gamma> e Fail \<Longrightarrow> hook \<Gamma> (Nonterm i) Fail" |
  Bind_update_0: "(Delta e i) \<in> (expressionSet \<Gamma>) \<Longrightarrow> hook \<Gamma> e Succ0 \<Longrightarrow> hook \<Gamma> (Nonterm i) Succ0" |
  NuAnythingGoes : "hook \<Gamma> (Nu n) out" |
  WithoutConsuming: "hook \<Gamma> e Succ0 \<Longrightarrow> succeeds \<Gamma> e" |
  WithConsuming: "hook \<Gamma> e Succ1 \<Longrightarrow> succeeds \<Gamma> e"

code_pred hook.
code_pred succeeds.

inductive_cases EmptyE[elim!]: "hook \<Gamma> Empty out"
inductive_cases TermE[elim!]: "hook \<Gamma> (Term a) out"
inductive_cases NontermE[elim!]: "hook \<Gamma> (Nonterm nt) out"
inductive_cases StarE[elim!]: "hook \<Gamma> (Star e) out"
inductive_cases NotE[elim!]: "hook \<Gamma> (Not e) out"
inductive_cases SeqE[elim!]: "hook \<Gamma> (Seq e1 e2) out"
inductive_cases ChoiceE[elim!]: "hook \<Gamma> (Choice e1 e2) out"
inductive_cases MutE[elim!]: "hook \<Gamma> (Mu e us) out"
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
lemma "hook \<Gamma> (Star e) out \<Longrightarrow> (out = Succ0 \<or> out = Succ1)"
by blast
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
lemma "hook \<Gamma> (Mu e us) out \<Longrightarrow> hook \<Gamma> e out"
by blast
lemma "hook \<Gamma> (Gamma n) out \<Longrightarrow> hook \<Gamma> (Nonterm n) out"
by blast
lemma "hook \<Gamma> (Delta e i) out \<Longrightarrow> hook \<Gamma> e out"
by blast
lemma "succeeds \<Gamma> e \<Longrightarrow> (hook \<Gamma> e Succ0 \<or> hook \<Gamma> e Succ1)"
by blast


lemma hook_inv_elim :
  "elim \<Gamma> e e' \<Longrightarrow> restricted e \<Longrightarrow> restricted e' \<Longrightarrow> (\<forall> out. hook \<Gamma> e out \<longleftrightarrow> hook \<Gamma> e' out)"
proof
  (induction rule: elim.induct)
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
qed

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
  Star_base: "step e x \<Gamma> None R \<Longrightarrow> step (Star e) x \<Gamma> (Some []) (production \<Gamma>)" |
  Star_ind: "step e (x1 @ x2 @ y) \<Gamma> (Some x1) R1 \<Longrightarrow>
             step (Star e) (x2 @ y) (\<Gamma>\<lparr>production := R1\<rparr>) (Some x2) R2 \<Longrightarrow>
             step (Star e) (x1 @ x2 @ y) \<Gamma> (Some (x1 @ x2)) R2" |
  Bind_s: "step e (x @ y) \<Gamma> (Some x) R \<Longrightarrow>
           step (Delta e i) (x @ y) \<Gamma> (Some x) ((i,termListToExpr x)#R)" |
  Bind_f: "step e x \<Gamma> None R \<Longrightarrow> step (Delta e i) x \<Gamma> None (production \<Gamma>)" |
  Mod_s_nil: "step e (x@y) \<Gamma> (Some x) R
            \<Longrightarrow> step (Mu e Nil) (x@y) \<Gamma> (Some x) R" |
  Mod_s_cons: "step e (x@y) \<Gamma> (Some x) R
            \<Longrightarrow> elim \<Gamma> ei ei'
            \<Longrightarrow> step (Mu e ((n,ei)#us)) (x@y) \<Gamma> (Some x) ((n,ei')#R)" |
  Mod_f : "step e x \<Gamma> None R \<Longrightarrow> step (Mu e p) x \<Gamma> None (production \<Gamma>)"

code_pred step.


(* Lemma 5.8 *)
lemma assumes hStep : "step e i \<Gamma> res R"
      assumes "restricted e"
      assumes "restricted e'"
      shows "hook \<Gamma> e' out \<longleftrightarrow> hook (\<Gamma> \<lparr> production := R\<rparr>) e' out"
      (*induction on the proof witness hStep *)
      defer
      using hStep
      apply(induct rule: step.induct)
      apply(auto)
      proof -
      fix e x y \<Gamma> R i
      assume "step e (x @ y) \<Gamma> (Some x) R"
      assume hhook : "hook \<Gamma> e' out"
      assume "hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      show "hook (\<Gamma>\<lparr>production := (i, foldr (\<lambda>c. Seq (Term c)) x Empty) # R\<rparr>) e' out"
        proof (cases e')
        case hempty : Empty
        hence  hout : "out = Succ0" using hhook  by blast
        thus ?thesis using hout hempty by (simp add: hook_succeeds.Empty)
        next case (Term)
        from this show ?thesis
          using Term_Succ1 Term_f hhook by blast
        next case (Nonterm)
        from this show ?thesis
          sorry (*...*)
        next case (Star)
        from this show ?thesis
          sorry (*...*)
        next case (Not)
        from this show ?thesis
          sorry (*...*)
        next case (Seq)
        from this show ?thesis
          sorry (*...*)
        next case (Choice)
        from this show ?thesis
          sorry (*...*)
        next case (Mu)
        from this show ?thesis
          sorry (*...*)
        next case (Delta)
        from this show ?thesis
          sorry (*...*)
        next case (Nu)
        from this show ?thesis
          sorry (*...*)
        next case (Gamma)
        from this show ?thesis
          sorry (*...*)
        qed
      next
      fix e x y \<Gamma> R i
      assume "step e (x @ y) \<Gamma> (Some x) R"
      assume "\<not> hook \<Gamma> e' out"
      assume "\<not> hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      assume "hook (\<Gamma>\<lparr>production := (i, foldr (\<lambda>c. Seq (Term c)) x Empty) # R\<rparr>) e' out"
      show "False"
        sorry
      next
      fix e x y \<Gamma> R ei ei' n
      assume "step e (x @ y) \<Gamma> (Some x) R"
      assume "elim \<Gamma> ei ei'"
      assume "hook \<Gamma> e' out"
      assume "hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      show "hook (\<Gamma>\<lparr>production := (n, ei') # R\<rparr>) e' out"
        sorry
      next
      fix e x y \<Gamma> R ei ei' n
      assume "step e (x @ y) \<Gamma> (Some x) R"
      assume "elim \<Gamma> ei ei'"
      assume "\<not> hook \<Gamma> e' out"
      assume "\<not> hook (\<Gamma>\<lparr>production := R\<rparr>) e' out"
      assume "hook (\<Gamma>\<lparr>production := (n, ei') # R\<rparr>) e' out"
      show "False"
        sorry
      qed
end