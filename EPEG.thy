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

record EPEG =
  production :: "(nonterm \<times> expr) list"
  table :: "(nonterm \<times> (symbol list)) list" 
  scope :: name


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
  Elim2: "lookup \<Gamma> n = Nonterm A \<Longrightarrow> elim \<Gamma> (Nu n) (Nonterm A)" |
  Mut_Nil : "elim \<Gamma> e e' \<Longrightarrow> elim \<Gamma> (Mu e Nil) (Mu e' Nil)" |
  Mut_Cons : "elim \<Gamma> (Nonterm ni) (Nonterm ni') \<Longrightarrow> 
              elim \<Gamma> ei ei' \<Longrightarrow> elim \<Gamma> (Mu e P) (Mu e' P') \<Longrightarrow>
              elim \<Gamma> (Mu e ((ni,ei)#P)) (Mu e' ((ni',ei')#P'))"

code_pred elim.

value "elim \<lparr> production = Nil, table = Nil, scope = Nil \<rparr> (Term (CHR ''a'')) (Term (CHR ''b''))" 

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

fun expressionSet :: "EPEG \<Rightarrow> expr list" where
  "expressionSet \<Gamma> = List.bind (map snd (production \<Gamma>)) getSubExpressions"

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
  Mut_update: "(List.member (expressionSet \<Gamma>) (Mu e us)) \<Longrightarrow> List.member us (n, u) \<Longrightarrow> hook \<Gamma> u out \<Longrightarrow> hook \<Gamma> (Nonterm n) out" | 
  Lookup: "hook \<Gamma> (Nonterm n) out \<Longrightarrow> hook \<Gamma> (Gamma n) out" | 
  Bind_main: "hook \<Gamma> e out \<Longrightarrow> hook \<Gamma> (Delta e i) out" | 
  Bind_update_1: "(List.member  (expressionSet \<Gamma>) (Delta e i)) \<Longrightarrow> hook \<Gamma> e Succ1 \<Longrightarrow> hook \<Gamma> (Nonterm i) Succ1" | 
  Bind_update_f: "(List.member (expressionSet \<Gamma>) (Delta e i)) \<Longrightarrow> hook \<Gamma> e Fail \<Longrightarrow> hook \<Gamma> (Nonterm i) Fail" | 
  Bind_update_0: "(List.member (expressionSet \<Gamma>) (Delta e i)) \<Longrightarrow> hook \<Gamma> e Succ0 \<Longrightarrow> hook \<Gamma> (Nonterm i) Succ0" | 
  WithoutConsuming: "hook \<Gamma> e Succ0 \<Longrightarrow> succeeds \<Gamma> e" |
  WithConsuming: "hook \<Gamma> e Succ1 \<Longrightarrow> succeeds \<Gamma> e"

code_pred hook.
code_pred succeeds.

inductive step :: "expr \<Rightarrow> char list \<Rightarrow> EPEG \<Rightarrow> string option \<Rightarrow> (nonterm \<times> expr) list \<Rightarrow> bool" where
  Term_s: "step (Term a) (a # x) \<Gamma> (Some [a]) (production \<Gamma>)" |
  Term_f_neq: "a \<noteq> b \<Longrightarrow> step (Term a) (b # x) \<Gamma> None (production \<Gamma>)" |
  Term_f_empty: "step (Term a) [] \<Gamma> None (production \<Gamma>)" |
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
  (*Bind_s: "step e (x @ y) \<Gamma> (Some x) R1 \<Longrightarrow>
           step (Delta e i) (x @ y) \<Gamma> (Some x) (s, expr.Choice (All (map x expr.Term)) (lookup R1 i))#R1" |*)
  Bind_f: "s step e x \<Gamma> None R \<Longrightarrow> step (Delta e i) x \<Gamma> None (production \<Gamma>)" |
  (*
   Mod_s: "step e (x@y) \<Gamma> (Some x) R₁
            (* u is the original update list, and v is the one with \<gamma> and \<nu> removed.*)
            (* still not entirely translated from Lean: \<Longrightarrow> \<forall> uv \<in> u.zip v, (uv.fst.fst = uv.snd.fst \<and> elimRefs uv.fst.snd = uv.fst.snd) *)
            \<Longrightarrow> step (Mu e u) (x@y) \<Gamma> (Some x) (v@R)
   *)
  Mod_f : "step e x \<Gamma> None R \<Longrightarrow> step (mu e p) x \<Gamma> None (production \<Gamma>)"


end