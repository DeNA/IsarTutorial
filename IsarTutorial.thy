theory IsarTutorial
imports Main
begin

lemma "apply": "(\<not>P \<and> \<not>Q) \<longrightarrow> \<not>(P \<or> Q)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule notI)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule_tac P="Q" in notE)
  apply assumption
  done


lemma "Isar": "(\<not>P \<and> \<not>Q) \<longrightarrow> \<not>(P \<or> Q)"
proof
  assume "\<not> P \<and> \<not> Q"
  then show "\<not> (P \<or> Q)"
  proof (rule conjE)
    assume np: "\<not>P" and nq: "\<not>Q"
    show "\<not> (P \<or> Q)"
    proof (rule notI)
      assume "P \<or> Q"
      then show "False"
      proof (rule disjE)
        assume "P"
        with np show "False" by (rule notE)
      next
        assume "Q"
        with nq show "False" by (rule notE)
      qed
    qed
  qed
qed


lemma "com_backward": "A \<and> B \<longrightarrow> B \<and> A" 
proof (rule impI) 
  assume ab: "A \<and> B" 
  from this  show "B \<and> A" 
  proof (rule conjE) 
    assume a: "A" and b: "B"
    from b a show "B \<and> A" by (rule conjI)
  qed
qed

thm conjI       (* ?P \<Longrightarrow> ?Q \<Longrightarrow> ?P \<and> ?Q *)
thm conjE       (* ?P \<and> ?Q \<Longrightarrow> (?P \<Longrightarrow> ?Q \<Longrightarrow> ?R) \<Longrightarrow> ?R *)
thm conjunct1   (* ?P \<and> ?Q \<Longrightarrow> ?P *)
thm conjunct2   (* ?P \<and> ?Q \<Longrightarrow> ?Q *)
thm disjI1      (* ?P \<Longrightarrow> ?P \<or> ?Q *)
thm disjI2      (* ?Q \<Longrightarrow> ?P \<or> ?Q *)
thm disjE       (* ?P \<or> ?Q \<Longrightarrow> (?P \<Longrightarrow> ?R) \<Longrightarrow> (?Q \<Longrightarrow> ?R) \<Longrightarrow> ?R *)
thm impI        (* (?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q *)
thm mp          (* ?P \<longrightarrow> ?Q \<Longrightarrow> ?P \<Longrightarrow> ?Q *)
thm rev_mp      (* ?P \<Longrightarrow> ?P \<longrightarrow> ?Q \<Longrightarrow> ?Q *)
thm iffI        (* (?P \<Longrightarrow> ?Q) \<Longrightarrow> (?Q \<Longrightarrow> ?P) \<Longrightarrow> ?P = ?Q *)
thm notI        (* (?P \<Longrightarrow> False) \<Longrightarrow> \<not> ?P *)
thm ccontr      (* (\<not> ?P \<Longrightarrow> False) \<Longrightarrow> ?P *)
thm notE        (* \<not> ?P \<Longrightarrow> ?P \<Longrightarrow> ?R *)
thm classical   (* (\<not> ?P \<Longrightarrow> ?P) \<Longrightarrow> ?P *)
thm subst       (* ?s = ?t \<Longrightarrow> ?P ?s \<Longrightarrow> ?P ?t *)
thm ssubst      (* ?t = ?s \<Longrightarrow> ?P ?s \<Longrightarrow> ?P ?t *)
thm refl        (* ?t = ?t *)
thm allI        (* (\<And>x. ?P x) \<Longrightarrow> \<forall>x. ?P x *)
thm spec        (* \<forall>x. ?P x \<Longrightarrow> ?P ?x *)
thm exI         (* ?P ?x \<Longrightarrow> \<exists>x. ?P x *)
thm exE         (* \<exists>x. ?P x \<Longrightarrow> (\<And>x. ?P x \<Longrightarrow> ?Q) \<Longrightarrow> ?Q *)


lemma 
  "com_backward_show_fail_ex1": 
  "A \<and> B \<longrightarrow> B \<and> A"
proof (rule impI)
  assume ab: "A \<and> B"
  from this show "P \<longrightarrow> Q" 
    oops


lemma 
  "com_backward_show_fail_ex2":
  "A \<and> B \<longrightarrow> B \<and> A"
proof (rule impI)
  assume "A \<and> B" "A"
  show "B \<and> A" 
    oops


lemma "rule_elim_fail_1_ex": "A \<and> B \<Longrightarrow> C \<longrightarrow> A \<and> C" 
proof (rule impI)
  assume ab: "A \<and> B" and c: "C"
  from ab show "A \<and> C"
  proof (rule conjE)
    oops


lemma "rule_elim_fail_2_ex": "A \<Longrightarrow> B \<longrightarrow> B \<and> A" 
proof (rule impI)
  assume a: "A" and b: "B"
  from b a show "B \<and> A"
  proof (rule conjI) qed
qed
    

lemma "com_backward_assume_B_A": 
  shows "A \<and> B \<longrightarrow> B \<and> A" 
proof (rule impI) 
  assume ab: "A \<and> B"
  from this show "B \<and> A" 
  proof (rule conjE) 
    assume "B" "A"
    from this show "B \<and> A" by (rule conjI) 
  qed
qed


lemma "com_backward_backquote": "A \<and> B \<longrightarrow> B \<and> A" 
proof (rule impI) 
  assume "A \<and> B" 
  from `A \<and> B` show "B \<and> A" 
  proof (rule conjE) 
    assume "A" "B"
    from `B` `A` show "B \<and> A" by (rule conjI) 
  qed
qed


lemma "Exer1-2_hint": "P \<and> Q \<longrightarrow> R \<Longrightarrow> P \<longrightarrow> (Q \<longrightarrow> R)"
proof (rule impI)
  assume pqr: "P \<and> Q \<longrightarrow> R"
  assume p: "P"
  show "Q \<longrightarrow> R"
  proof (rule impI)
    assume q: "Q"
    from pqr show "R"
    proof (rule mp)
      from p q show "P \<and> Q" by (rule conjI)
    qed
  qed
qed


lemma "Exer1-1": "Q \<Longrightarrow> (P \<longrightarrow> Q)"
  oops


lemma "Exer1-2": "(P \<and> Q) \<and> R \<longrightarrow> Q"
  oops


lemma "com_forward": "A \<and> B \<longrightarrow> B \<and> A"
proof (rule impI)
  assume ab: "A \<and> B"
  from ab have a: "A" by (rule conjunct1)
  from ab have b: "B" by (rule conjunct2)
  from b a show "B \<and> A" by (rule conjI)
qed


lemma "assumes_shows":
  assumes "A \<and> B" "C"
  shows "B \<and> C"
  using assms(1)
proof (rule conjE)
  assume "B"
  from this assms(2) show "B \<and> C" by (rule conjI)
qed


lemma "not_use_assumes_shows": "A \<and> B \<Longrightarrow> C \<Longrightarrow> B \<and> C"
proof -
  assume "C"
  assume "A \<and> B"
  from this show "B \<and> C"
  proof (rule conjE)
    assume "B"
    from this `C` show "B \<and> C" by (rule conjI)
  qed
qed


lemma "next": 
  assumes "\<not>P \<or> Q" "P"
  shows "P \<and> Q"
  using assms(1)
proof (rule disjE) 
  assume "\<not>P"
  from this assms(2) show "P \<and> Q" by (rule notE)
next
  assume "Q"
  from assms(2) this show "P \<and> Q" by (rule conjI)
qed


lemma "next_share_fact": "\<not>P \<or> Q \<Longrightarrow> P \<Longrightarrow> P \<and> Q"
proof (rule conjI)
  assume "P"
  show "P" by (rule `P`)
next
  assume 1: "\<not>P \<or> Q" and 2: "P"
  from 1 show "Q"
  proof (rule disjE)
    assume "\<not>P"
    from this 2 show "Q" by (rule notE)
  qed
qed


lemma "block": 
  assumes "\<not>P \<or> Q" "P"
  shows "P \<and> Q"
  using assms(1)
proof (rule disjE) 
  {
    assume "\<not>P"
    from this assms(2) show "P \<and> Q" by (rule notE)
  }
  {
    assume "Q"
    from assms(2) this show "P \<and> Q" by (rule conjI)
  }
qed


notepad begin
  have a: "A" sorry
  have b: "B" sorry
  thm conjI                    (* ?P \<Longrightarrow> ?Q \<Longrightarrow> ?P \<and> ?Q *)

  thm conjI[of A B]            (* A \<Longrightarrow> B \<Longrightarrow> A \<and> B *)
  thm conjI[where P=A and Q=B] (* A \<Longrightarrow> B \<Longrightarrow> A \<and> B *)
  
  thm conjI[OF a b]            (* A \<and> B *)
end


lemma "tips_standard_then_thesis_dot": "P \<and> Q \<Longrightarrow> P \<longrightarrow> Q"
proof (* = "proof standard" *)
  assume a: "P \<and> Q"
  from a show "Q"
  proof (rule conjE)
    assume c: "Q"
    then (* = from this *) show ?thesis (* = Q *) . (* = "by this" *)
  qed
qed

lemma "tips_standard_with_doubledots": "P \<and> Q \<longrightarrow> R \<Longrightarrow> P \<longrightarrow> (Q \<longrightarrow> R)"
proof (* = proof standard *)
  assume a: "P \<and> Q \<longrightarrow> R" and b: "P"
  show "Q \<longrightarrow> R"
  proof
    assume c: "Q"
    from b c have "P \<and> Q" .. (* = "by standard" *)
    with a show "R" ..
  qed
qed


lemma tips_of_where: "P \<and> Q \<longrightarrow> R \<Longrightarrow> P \<longrightarrow> (Q \<longrightarrow> R)"
proof (rule impI)
  assume pqr: "P \<and> Q \<longrightarrow> R"
  assume p: "P"
  show "Q \<longrightarrow> R"
  proof (rule impI)
    assume q: "Q"
    from pqr show "R"
    thm mp[of "P \<and> Q"] (* P \<and> Q \<longrightarrow> ?Q \<Longrightarrow> P \<and> Q \<Longrightarrow> ?Q *)
    thm mp[where P="P \<and> Q"] (* P \<and> Q \<longrightarrow> ?Q \<Longrightarrow> P \<and> Q \<Longrightarrow> ?Q *)
    proof (rule mp[of "P \<and> Q"]) (* = "proof (rule_tac P="P \<and> Q" in mp)" *)
      from p q show "P \<and> Q" by (rule conjI)
    qed
  qed
qed

lemma "comma": "P \<longleftrightarrow> P"
proof (rule iffI)
  (* goal (2 subgoals):
     1. P \<Longrightarrow> P
     2. P \<Longrightarrow> P
  *)
  oops

lemma "comma": "P \<longleftrightarrow> P"
proof (rule iffI, assumption, assumption) qed


lemma "semicolon": "P \<longleftrightarrow> P"
proof (rule iffI; assumption) qed


lemma "Exer2-1": "P \<longrightarrow> (P \<longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q"
  oops


lemma "Exer2-2": "P \<or> Q \<longrightarrow> R \<Longrightarrow> P \<Longrightarrow> R"
  oops


lemma "Exer2-3": "(P \<longrightarrow> Q) \<longrightarrow> (\<not>Q \<longrightarrow> \<not>P)"
  oops


lemma "Exer2-4": 
  assumes "P \<or> Q" "\<not>P"
  shows "Q"
  oops


lemma "Exer2-5": 
  assumes "(P \<or> Q) \<longrightarrow> R"
  shows "(P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"
  oops


lemma "fix": "\<forall>x::nat. P x \<Longrightarrow> \<forall>y. P y"
proof (rule allI)
  fix a::nat
  assume "\<forall>x. P x"
  thm spec
  then show "P a" by (rule spec)
qed


lemma "obtain": "\<exists>x. P x \<Longrightarrow> \<exists>x. P x \<or> Q x"
proof -
  assume "\<exists>x. P x"
  then obtain x where "P x"  by (rule exE)
  then have "P x \<or> Q x" by (rule disjI1)
  then show ?thesis by (rule exI)
qed


lemma "Exer3-1": 
  assumes "\<forall>x. P x" and "\<forall>x. P x \<longrightarrow> Q x"
  shows "\<forall>x. Q x"
  oops


lemma "Exer3-2": 
  assumes "\<forall>x. (P x \<longrightarrow> (\<exists>y. Q y))"
  shows "(\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)"
  oops


lemma "Exer3-3(don't use obtain)": 
  assumes "\<exists>x. P x"
  shows "\<exists>x. (P x \<or> Q x)"
  oops


lemma "Exer3-4": "x \<in> \<Union>C \<Longrightarrow> \<exists>A\<in>C. x \<in> A"
(* hint *)
thm UnionE (* ?A \<in> \<Union> ?C \<Longrightarrow> (\<And>X. ?A \<in> X \<Longrightarrow> X \<in> ?C \<Longrightarrow> ?R) \<Longrightarrow> ?R *)
thm bexI   (* ?P ?x \<Longrightarrow> ?x \<in> ?A \<Longrightarrow> \<exists>x\<in>?A. ?P x *)
  oops


lemma "moreover": "(P \<longrightarrow> Q) \<Longrightarrow> (P \<longrightarrow> R) \<Longrightarrow> (P \<longrightarrow> S) \<Longrightarrow> P \<Longrightarrow> Q \<and> R \<and> S"
proof -
  assume p: "P"
  assume "P \<longrightarrow> Q"
  with p have "Q" by (rule rev_mp)
  moreover
  assume "P \<longrightarrow> R"
  with p have "R" by (rule rev_mp)
  moreover
  assume "P \<longrightarrow> S"
  with p have "S" by (rule rev_mp)
  ultimately
  show ?thesis by (intro conjI)  (* TODO: intro ?thesis *)
qed


lemma "without-moreover": "(P \<longrightarrow> Q) \<Longrightarrow> (P \<longrightarrow> R) \<Longrightarrow> (P \<longrightarrow> S) \<Longrightarrow> P \<Longrightarrow> Q \<and> R \<and> S"
proof -
  assume p: "P"
  assume "P \<longrightarrow> Q"
  with p have a: "Q" by (rule rev_mp)
  assume "P \<longrightarrow> R"
  with p have b: "R" by (rule rev_mp)
  assume "P \<longrightarrow> S"
  with p have "S" by (rule rev_mp)
  with a b show ?thesis by (intro conjI)
qed


lemma "case": "P \<or> \<not>P"
proof (cases "P")
  case True
  then show ?thesis by (rule disjI1)
next
  case False
  then show ?thesis by (rule disjI2)
qed


notepad begin
  fix a b c::nat
  assume "a = b"
  have "a = c" unfolding `a = b`
    (* new goal: b = c *)
    sorry
end


notepad begin
  fix a b c::nat
  assume "b = a"
  have "a = c" unfolding `b = a` [symmetric]
    (* new goal: b = c *)
    sorry
end


notepad begin
  fix a b c::nat
  assume "a = b"
  have "a = c"
  proof (subst `a = b`)
    (* new goal *) show "b = c" sorry
  qed
end


notepad begin
  fix a b c d::nat
  assume "a = b"
  have "a = c \<and> d = a"
  proof (subst (2) `a = b`) 
    (* new goal *) show "a = c \<and> d = b" sorry
  qed
end


notepad begin
  fix a b c d::nat
  assume 1: "a = b" and 2: "a = c"
  from 1 have "b = c"
  proof (subst (asm) `a = c`) 
    (* new goal *) show "c = b \<Longrightarrow> b = c" sorry
  qed
end


notepad begin
  fix a b c d::nat
  assume 1: "a = b" and 2: "a = c" and 3: "a = d"
  from 1 2 have "b = c"
  proof (subst (asm) (2) `a = d`)
    (* new goal *) show "a = b \<Longrightarrow> d = c \<Longrightarrow> b = c" sorry
  qed
end


lemma "Exer4-1(use moreover, ultimately)": "A \<and> B \<Longrightarrow> B \<and> A"
  oops


lemma "Exer4-2(use moreover, ultimately)": 
  assumes "(P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> Q)"
  shows "Q"
  using assms
proof(rule conjE)
  assume 1: "P \<longrightarrow> Q" and 2: "\<not>P \<longrightarrow> Q"
  {
    assume "P"
    (* write proof *)
  }
  moreover
  {
    assume "\<not>P"
    (* write proof *)
  }
  ultimately show "Q" by ( (* write proof *) )
  oops


lemma "Exer4-3": "(P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> Q) \<Longrightarrow> Q"
  oops


lemma "Exer4-4": "\<forall>x. P \<or> Q x \<Longrightarrow> P \<or> (\<forall>x. Q x)"
  oops


lemma "Exer4-5": "if y \<le> x then z = x else z = y \<Longrightarrow> z = x \<or> z = y"
(* hint *)
thm if_P      (* ?P \<Longrightarrow> (if ?P then ?x else ?y) = ?x *)
thm if_not_P  (* \<not> ?P \<Longrightarrow> (if ?P then ?x else ?y) = ?y *)
  oops


lemma "induction":
  assumes "a 0 = 1" "\<forall>n::nat. a (Suc n) = a n + 2"
  shows "a n = 2 * n + 1"
proof (induction n)
  case 0
  from assms(1) show ?case by simp
next
  case (Suc n)
  with assms show ?case by auto
qed


lemma "induction_also": 
  assumes "a 0 = 1" "\<forall>n::nat. a (Suc n) = a n + 2"
  shows "a n = 2 * n + 1"
proof (induction n)
  case 0
  from assms(1) show ?case by simp
next
  case (Suc n)
  then show ?case
  proof -
    from assms(2) have "a (Suc n) = a n + 2" by (rule spec)
    also have "... = 2 * n + 1 + 2"
      by (subst Suc) (rule refl)
    also have "... = 2 * n + 2 + 1" 
      by (subst semiring_normalization_rules(23)) (rule refl)
    also have "... = n * 2 + 2 + 1" 
      by (subst semiring_normalization_rules(7)) (rule refl)
    also have "... = (n + 1) * 2 + 1" 
      by (subst semiring_normalization_rules(2)) (rule refl)
    also have "... = 2 * (n + 1) + 1" 
      by (subst semiring_normalization_rules(7)) (rule refl)
    also have "... = 2 * (Suc n) + 1" 
      by (subst Nat.Suc_eq_plus1[symmetric]) (rule refl)
    finally show ?thesis .
  qed
qed


notepad begin
  have "a = b" sorry
  also have "... = c" sorry
  also have "... = d" sorry
  also have "... = e" sorry
  finally have "a = e" .
end


thm trans (* ?r = ?s \<Longrightarrow> ?s = ?t \<Longrightarrow> ?r = ?t *)
print_trans_rules

notepad begin
  have "a = b" sorry
  note cal = this have "... = c" sorry
  thm trans[OF cal this] (* a = c *)
  note cal = trans[OF cal this] have c: "... = d" sorry
  thm trans[OF cal this] (* a = d *)
  note cal = trans[OF cal this] have d: "... = e" sorry
  thm trans[OF cal this] (* a = e *)
  note cal = trans[OF cal this]
  from cal have "a = e" .
end


primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0 = m" |
"add m (Suc n) = add (Suc m) n"


lemma "Exer8-1": "\<forall>m. add m n = m + n"
(* hint *)
thm add.simps(1) (* add ?m 0 = ?m *)
thm add.simps(2) (* add ?m (Suc ?n) = add (Suc ?m) ?n *)
thm add_0_right  (* ?a + 0 = ?a *)
thm add_Suc_shift (* Suc ?m + ?n = ?m + Suc ?n *)
  oops
