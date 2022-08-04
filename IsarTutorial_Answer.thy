theory IsarTutorial_Answer
imports Main
begin


lemma "Exer1-1_Answer_pattern_1": "Q \<Longrightarrow> (P \<longrightarrow> Q)"
proof (rule impI)
  assume q: "Q"
  show "Q" by (rule q)
qed


lemma "Exer1-1_Answer_pattern_2": "Q \<Longrightarrow> (P \<longrightarrow> Q)"
proof (rule impI) qed


lemma "Exer1-1_Answer_pattern_3": "Q \<Longrightarrow> (P \<longrightarrow> Q)"
proof (rule impI)
  assume q: "Q"
  from this show "Q" by assumption
qed


lemma "Exer1-2": "(P \<and> Q) \<and> R \<longrightarrow> Q"
proof (rule impI)
  assume pqr: "(P \<and> Q) \<and> R"
  from pqr show "Q"
  proof (rule conjE)
    assume pq: "P \<and> Q" and r: "R"
    from pq show "Q" by (rule conjunct2)
  qed
qed


lemma "Exer2-1": "P \<longrightarrow> (P \<longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q"
proof (rule impI)
  assume "P \<longrightarrow> (P \<longrightarrow> Q)" "P"
  then have "P \<longrightarrow> Q" by (rule mp)
  with `P` show "Q" by (rule rev_mp)
qed


lemma "Exer2-2": "P \<or> Q \<longrightarrow> R \<Longrightarrow> P \<Longrightarrow> R"
proof -
  assume "P"
  then have "P \<or> Q" by (rule disjI1)
  assume "P \<or> Q \<longrightarrow> R"
  with `P \<or> Q` show "R" by (rule rev_mp)
qed


lemma "Exer2-3": "(P \<longrightarrow> Q) \<longrightarrow> (\<not>Q \<longrightarrow> \<not>P)"
proof ((rule impI)+, rule notI)
  assume "P \<longrightarrow> Q" "P"
  then have "Q" by (rule mp)
  assume "\<not>Q"
  from this `Q` show "False" by (rule notE)
qed


lemma "Exer2-4": 
  assumes "P \<or> Q" "\<not>P"
  shows "Q"
  using assms(1)
proof (rule disjE)
  assume "P"
  with assms(2) show "Q" by (rule notE)
next
  assume "Q"
  show "Q" by (rule `Q`)
qed


lemma "Exer2-5": 
  assumes "(P \<or> Q) \<longrightarrow> R"
  shows "(P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"
proof (rule conjI)
  show "P \<longrightarrow> R"
  proof (rule impI)
    assume "P"
    then have "P \<or> Q" by (rule disjI1)
    with assms(1) show "R" by (rule mp)
  qed
next
  show "Q \<longrightarrow> R"
  proof (rule impI)
    assume "Q"
    then have "P \<or> Q" by (rule disjI2)
    with assms(1) show "R" by (rule mp)
  qed
qed


lemma "Exer3-1": 
  assumes "\<forall>x. P x" and "\<forall>x. P x \<longrightarrow> Q x"
  shows "\<forall>x. Q x"
proof (rule allI)
  fix x
  from assms(1) have 1: "P x" by (rule spec)
  from assms(2) have 2: "P x \<longrightarrow> Q x" by (rule spec)
  from 2 1 show "Q x" by (rule mp)
qed


lemma "Exer3-2": 
  assumes "\<forall>x. (P x \<longrightarrow> (\<exists>y. Q y))"
  shows "(\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)"
proof (rule impI)
  assume "\<exists>x. P x"
  then obtain x where 1: "P x" by (rule exE)
  from assms(1) have 2: "P x \<longrightarrow> (\<exists>y. Q y)" by (rule spec)
  from 2 1 show "\<exists>x. Q x" by (rule mp)
qed


lemma "Exer3-3(don't use obtain)": 
  assumes "\<exists>x. P x"
  shows "\<exists>x. (P x \<or> Q x)"
  using assms
proof (rule exE)
  fix x
  assume "P x"
  then have "P x \<or> Q x" by (rule disjI1)
  then show "\<exists>x. (P x \<or> Q x)" by (rule exI)
qed


lemma "Exer3-4": "x \<in> \<Union>C \<Longrightarrow> \<exists>A\<in>C. x \<in> A"
(* hint *)
thm UnionE (* ?A \<in> \<Union> ?C \<Longrightarrow> (\<And>X. ?A \<in> X \<Longrightarrow> X \<in> ?C \<Longrightarrow> ?R) \<Longrightarrow> ?R *)
thm bexI   (* ?P ?x \<Longrightarrow> ?x \<in> ?A \<Longrightarrow> \<exists>x\<in>?A. ?P x *)
proof -
  assume "x \<in> \<Union>C"
  then obtain "A" where "x \<in> A" and "A \<in> C"  by (rule UnionE)
  then show "\<exists>A\<in>C. x \<in> A" by (rule bexI)
qed


lemma "Exer4-1(use moreover, ultimately)": "A \<and> B \<Longrightarrow> B \<and> A"
proof -
  assume a: "A \<and> B"
  then have "B" by (rule conjunct2)
  moreover
  from a have "A" by (rule conjunct1)
  ultimately show "B \<and> A" by (rule conjI)
qed


lemma "Exer4-2(use moreover, ultimately)": 
  assumes "(P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> Q)"
  shows "Q"
  using assms
proof(rule conjE)
  assume 1: "P \<longrightarrow> Q" and 2: "\<not>P \<longrightarrow> Q"
  {
    assume "P"
    with 1 have "Q" by (rule mp)
  }
  moreover
  {
    assume "\<not>P"
    with 2 have "Q" by (rule mp)
  }
  ultimately show "Q" by (cases "P")
qed


lemma "Exer4-3": "(P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> Q) \<Longrightarrow> Q"
proof (cases "P")
  case True
  assume "(P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> Q)"
  then show ?thesis
  proof (rule conjE)
    assume "P \<longrightarrow> Q"
    with True show ?thesis by (rule rev_mp)
  qed
next
  case False
  assume "(P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> Q)"
  then show ?thesis
  proof (rule conjE)
    assume "\<not>P \<longrightarrow> Q"
    with False show ?thesis by (rule rev_mp)
  qed
qed


lemma "Exer4-4": "\<forall>x. P \<or> Q x \<Longrightarrow> P \<or> (\<forall>x. Q x)"
proof (cases "P")
  case True
  then show ?thesis by (rule disjI1)
next
  case False
  assume 1: "\<forall>x. P \<or> Q x"
  show ?thesis
  proof (rule disjI2)
    show "\<forall>x. Q x"
    proof (rule allI)
      fix x      
      from 1 have 2:"P \<or> Q x" by (rule spec)
      from 2 show "Q x"
      proof (rule disjE)
        assume "P"
        with False show ?thesis by (rule notE)
      qed
    qed
  qed
qed


lemma "Exer4-5": "if y \<le> x then z = x else z = y \<Longrightarrow> z = x \<or> z = y"
(* hint *)
thm if_P      (* ?P \<Longrightarrow> (if ?P then ?x else ?y) = ?x *)
thm if_not_P  (* \<not> ?P \<Longrightarrow> (if ?P then ?x else ?y) = ?y *)
proof (cases "y \<le> x")
  case True
  assume a: "if y \<le> x then z = x else z = y"
  show ?thesis
  proof (rule disjI1)
    from True have 1: "(if y \<le> x then z = x else z = y) = (z = x)" by (rule if_P)
    from a show "z = x" by (subst (asm) 1)
  qed
next
  case False
  assume a: "if y \<le> x then z = x else z = y"
  show ?thesis 
  proof (rule disjI2)
    from False have 1: "(if y \<le> x then z = x else z = y) = (z = y)" by (rule if_not_P)
    from a show "z = y" by (subst (asm) 1)
  qed
qed


primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0 = m" |
"add m (Suc n) = add (Suc m) n"


lemma "Exer8-1": "\<forall>m. add m n = m + n"
(* hint *)
thm add.simps(1) (* add ?m 0 = ?m *)
thm add.simps(2) (* add ?m (Suc ?n) = add (Suc ?m) ?n *)
thm add_0_right  (* ?a + 0 = ?a *)
thm add_Suc_shift (* Suc ?m + ?n = ?m + Suc ?n *)
proof (induction n)
  case 0
  then show ?case
  proof (rule allI)
    fix m
    show "add m 0 = m + 0"
      by (subst add.simps(1), subst add_0_right, rule refl)
  qed
next
  case (Suc n)
  show ?case
  proof (rule allI)
    fix m
    have "add m (Suc n) = add (Suc m) n" by (rule add.simps(2))
    also have "... = (Suc m) + n" by (subst Suc) (rule refl)
    also have "... = m + Suc n" by (rule add_Suc_shift)
    finally show "add m (Suc n) = m + Suc n" .
  qed
qed
