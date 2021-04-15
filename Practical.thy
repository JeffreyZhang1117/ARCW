theory Practical
imports Main
begin

section \<open>Part 1\<close>

(* 1 mark *)
lemma disjunction_idempotence:
  "A \<or> A \<longleftrightarrow> A"
  apply (rule iffI)
  apply (erule disjE)
  apply assumption+
  apply (rule disjI1)
  apply assumption
  done

(* 1 mark *)
lemma conjunction_idempotence:
  "A \<and> A \<longleftrightarrow> A"
  apply (rule iffI)
  apply (erule conjE)
  apply assumption
  apply (rule conjI)
  apply assumption+
  done

(* 1 mark *)
lemma disjunction_to_conditional:
  "(\<not> P \<or> R) \<longrightarrow> (P \<longrightarrow> R)"
  apply (rule impI)+
  apply (erule disjE)
  apply (erule notE)
  apply assumption+ 
  done

(* 1 mark *)
lemma
  "(\<exists>x. P x \<and> Q x) \<longrightarrow> (\<exists>x. P x) \<and> (\<exists>x. Q x)"
  apply (rule impI)
  apply (erule exE)
  apply (erule conjE)
  apply (rule conjI)
  apply (erule exI)+
  done

(* 1 mark *)
lemma
  "(\<not> (\<exists>x. \<not>P x) \<or> R) \<longrightarrow> ((\<exists>x. \<not> P x) \<longrightarrow> R)"
  apply (rule impI)+
  apply (erule disjE)
  apply (erule notE)
  apply assumption+
  done

(* 2 marks *)
lemma
  "(\<forall>x. P x) \<longrightarrow> \<not> (\<exists>x. \<not> P x)"  
  apply (rule impI)
 
  apply (rule notI)
  apply (erule exE)
  apply (erule notE)
  apply (erule allE)
  apply assumption
  done

(* 3 marks *)
text \<open>Prove using ccontr\<close>
lemma excluded_middle:
  "P \<or> \<not> P"
  apply (rule ccontr)
  apply (rule ccontr)
  apply (rule_tac P = "P \<or> \<not> P" in notE)
  apply assumption
  apply (rule disjI1)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption 
  done

(* 3 marks *)
text \<open>Prove using excluded middle\<close>
lemma notnotD:
  "\<not>\<not> P \<Longrightarrow> P"
  apply (cut_tac P = "P" in  excluded_middle)
  apply (erule disjE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

(* 3 marks *)
text \<open>Prove using double-negation (rule notnotD)\<close>
lemma classical:
  "(\<not> P \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule impI)
  apply (rule notnotD)
  apply (rule notI)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done


(* 3 marks *)
text \<open>Prove using classical\<close>
lemma ccontr:
  "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P"
  apply (drule impI)
  apply (rule classical)
  apply (erule impE)
  apply assumption
  apply (rule_tac P = "\<not> P" in notE)
  apply (rule notI)
  apply assumption+
  done

(* 3 marks *)
lemma
  "(\<not> (\<forall>x. P x \<or> R x)) = (\<exists>x. \<not> P x \<and> \<not> R x)"
  apply (rule iffI)

  apply (rule classical)
  apply (erule notE)
  apply (rule allI)
  apply (rule classical)
  apply (erule notE)
  apply (rule exI)
 
  apply(rule conjI)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption

  apply (erule exE)
  apply (rule notI)
  apply (erule allE)
  apply (erule disjE)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  apply (erule conjE)
  apply (erule notE)
  apply (erule notE)
  apply assumption
  done   
 
(* 3 marks *)
lemma
  "(\<exists>x. P x \<or> R x) = (\<not>((\<forall>x. \<not> P x) \<and> \<not> (\<exists>x. R x)))"
  apply (rule iffI)
  
  apply (erule exE)
  apply (rule notI)
  apply (erule conjE)
  apply (erule allE)
  apply (erule disjE)
  apply (erule notE)
  apply (erule notE)
  apply assumption
  apply (erule notE)
  apply (rule exI)
  apply assumption

  apply (rule classical)
  apply (erule notE)
  apply (rule conjI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule exI)
  apply (rule disjI1)
  apply assumption
  apply (rule notI)
  apply (erule exE)
  apply (erule notE)
  apply (rule exI)
  apply (rule disjI2)
  apply assumption
  done

section \<open>Part 2.1\<close>

locale partof =
  fixes partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
begin

(* 1 mark *)
definition properpartof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubset>" 100) where
  "x \<sqsubset> y \<equiv>  x \<sqsubseteq> y \<and> x \<noteq> y "

(* 1 mark *)
definition overlaps :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<frown>" 100) where
  "x \<frown> y \<equiv> \<exists>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y"

definition disjoint :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<asymp>" 100) where
  "x \<asymp> y \<equiv> \<not> x \<frown> y"

(* 1 mark *)
definition partialoverlap :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "~\<frown>" 100) where
  "x ~\<frown> y \<equiv> x \<frown> y \<and> \<not>x \<sqsubseteq> y \<and> \<not>y \<sqsubseteq> x"

(* 1 mark *)
definition sumregions :: "'region set \<Rightarrow> 'region \<Rightarrow> bool" ("\<Squnion> _ _" [100, 100] 100) where
  "\<Squnion> \<alpha> x \<equiv> (\<forall>y \<in> \<alpha>. y \<sqsubseteq> x) \<and> (\<forall>y. y \<sqsubseteq> x \<longrightarrow> (\<exists>z \<in> \<alpha>. y \<frown> z))"

end

(* 1+1+1=3 marks *)
locale mereology = partof +
  assumes A1: "\<forall>x y z. x\<sqsubseteq>y \<and> y\<sqsubseteq>z \<longrightarrow> x\<sqsubseteq>z"
      and A2: "\<forall>\<alpha>. \<alpha> \<noteq>  {} \<longrightarrow> (\<exists>x. \<Squnion> \<alpha> x)"
      and A2': "\<forall>\<alpha> x y. \<Squnion> \<alpha> x \<and>  \<Squnion>\<alpha> y \<longrightarrow> (x = y)"
begin

section \<open>Part 2.2\<close>

(* 2 marks *)
theorem overlaps_sym:
  "(x \<frown> y) = (y \<frown> x)"
   apply (unfold overlaps_def)
   apply (rule iffI)

   apply (erule exE)+
   apply (erule conjE)+
   apply (rule exI)+
   apply (rule conjI)+
   apply assumption+

   apply (erule exE)+
   apply (erule conjE)+
   apply (rule exI)+
   apply (rule conjI)+
   apply assumption+

  done

(* 1 mark *)
theorem in_sum_set_partof:
  "\<forall>x. x \<in> \<alpha> \<and>  \<Squnion> \<alpha> y \<longrightarrow>  x \<sqsubseteq> y"
proof-
  show "\<forall>x. x \<in> \<alpha> \<and>  \<Squnion> \<alpha> y \<longrightarrow>  x \<sqsubseteq> y" by (simp add: partof.sumregions_def)
qed


(* 3 marks *)
theorem overlaps_refl:
  "x \<frown> x"
proof- 
  have "\<exists>z. \<Squnion> {x} z" 
  using A2  by auto
  then obtain z where "\<Squnion> {x} z" by blast
  then show "x \<frown> x"
  using sumregions_def by auto
qed

(* 1 mark *)
theorem all_has_partof:
    "\<forall>x.\<exists>y. y \<sqsubseteq> x"
proof-
  show "\<forall>x.\<exists>y. y \<sqsubseteq> x" using overlaps_def overlaps_refl by auto
qed


(* 2 marks *)
theorem partof_overlaps:
  assumes "x \<sqsubseteq> y" 
  shows "x \<frown> y"
proof-
  obtain p where "p \<sqsubseteq> x \<and> p \<sqsubseteq> y"
  using A1 all_has_partof assms by blast 
  then show "x \<frown> y"
    using overlaps_def by blast 
qed



(* 1 mark *)
theorem sum_parts_eq:
  "\<Squnion> {a. a \<sqsubseteq> x} x"
proof -
   show "\<Squnion> {a. a \<sqsubseteq> x} x" using overlaps_refl sumregions_def by auto
qed

(* 2 marks *)
theorem sum_relation_is_same':
  assumes "\<And>c. r y c \<Longrightarrow> c \<sqsubseteq> y"
      and "\<And>f. y \<frown> f \<Longrightarrow> \<exists>g. r y g \<and> g \<frown> f"
      and "\<Squnion> {y} x"
    shows "\<Squnion> {k. r y k} x"
proof-
  have "\<And>k. r y k \<Longrightarrow> k \<sqsubseteq> y"  by (simp add: assms(1))
  then have "y \<sqsubseteq> x" using assms(3) in_sum_set_partof  by blast 
  then have a: "\<forall>k. r y k \<longrightarrow> k \<sqsubseteq> x" using A1 assms(1) by blast 
  then have b: "\<forall>q. q \<sqsubseteq> x \<longrightarrow> (\<exists>z \<in> {k. r y k}. q \<frown> z)"
  using assms(2) assms(3) overlaps_sym sumregions_def by auto
  from a and b show "\<Squnion> {k. r y k} x"
  using sumregions_def by auto  
qed
   
  
(* 1 mark *)
theorem overlap_has_partof_overlap:
  assumes a: "e \<frown> f"
  shows "\<exists>g. g \<sqsubseteq> e \<and> g \<frown> f"
proof-
  from a have b :  "\<exists>g. g \<sqsubseteq> e \<and> g \<sqsubseteq> f" using overlaps_def by blast
  from b show "\<exists>g. g \<sqsubseteq> e \<and> g \<frown> f"   using partof_overlaps by blast
qed
  

(* 1 marks *)
theorem sum_parts_of_one_eq:
  assumes "\<Squnion> {y} x"
  shows "\<Squnion> {k. k\<sqsubseteq>y} x"
proof-
  note sum_relation_is_same' [where r = "\<lambda>y k. k \<sqsubseteq> y"]
  show ?thesis
    using assms sum_relation_is_same' overlap_has_partof_overlap by fastforce
qed

(* 5 marks *)
theorem both_partof_eq:
  assumes "x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
  shows "x = y"
proof-
  have "\<Squnion> {k. k \<sqsubseteq> x} y" 
  proof (rule ccontr)
    assume "\<not> \<Squnion> {k. k \<sqsubseteq> x} y"
    then have " (\<exists>p. p \<sqsubseteq> x \<and> \<not>(p \<sqsubseteq> y)) \<or> (\<exists>w. w \<sqsubseteq> y \<and> (\<forall>p. p \<sqsubseteq> x \<longrightarrow> w \<asymp> p))"
      using assms partof_overlaps sumregions_def by auto
     then show "False" 
    proof 
      assume a1: " (\<exists>p. p \<sqsubseteq> x \<and> \<not>(p \<sqsubseteq> y))"
      then  show "False"
      using A1 assms by blast 
    next
      assume a: "\<exists>w. w \<sqsubseteq> y \<and> (\<forall>p. p \<sqsubseteq> x \<longrightarrow> w \<asymp> p)"
      obtain w where b : "w \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<longrightarrow> w \<asymp> z)"
        using a by auto
       have c:" y \<sqsubseteq> x "
         by (simp add: assms)
       then have " y \<asymp> w"
         using b disjoint_def partof_overlaps by blast
      then show "False"
        by (simp add: b disjoint_def overlaps_sym partof_overlaps)
    qed
  qed
  then show  "x = y"
    using A2' sum_parts_eq by blast 
qed

(* 4 marks *)
theorem sum_all_with_parts_overlapping:
  assumes "\<Squnion> {z. \<forall>a. a \<sqsubseteq> z \<longrightarrow> a \<frown> y} x"
  shows "\<Squnion> {y} x"
proof-
  show  "\<Squnion> {y} x"
  proof (rule ccontr)
   assume "\<not> \<Squnion> {y} x"
   then have "\<not>(y \<sqsubseteq> x) \<or> (\<exists>w. w \<sqsubseteq> x \<and> w \<asymp> y) "
   by (simp add: disjoint_def partof.sumregions_def)
   then show "False" 
   proof 
     assume a: "\<not>(y \<sqsubseteq> x)"
     then have b: " y \<in> {k .k\<frown>y} "
       by (simp add: overlaps_refl)
     have "y \<sqsubseteq> x"
       using assms partof_overlaps sumregions_def by auto 
     then show "False"
       using a by blast
   next
     assume a: "\<exists>w. w \<sqsubseteq> x \<and> w \<asymp> y" 
     obtain w where b:"w \<sqsubseteq> x \<and> w \<asymp> y"
       using a by blast 
     obtain a where c: "a \<in> {z. \<forall>p. p \<sqsubseteq> z \<longrightarrow> p\<frown>y} \<and> w \<frown> a"
       using assms b sumregions_def by auto
     obtain wz where d :"wz \<sqsubseteq> w \<and> wz \<sqsubseteq> a"
       using c overlaps_def by auto 
     have 0 : "wz \<frown> y"  
       using c d by blast 
     obtain wzy where 1:"wzy \<sqsubseteq> wz \<and> wzy \<sqsubseteq> y"
       using "0" overlaps_def by blast
     have "wzy \<sqsubseteq> w"
       using "1" A1 d by blast  
     then have "w \<frown> y"
       using "0" A1 d overlaps_def by blast    
      then show "False"
        using b disjoint_def by blast  
    qed
  qed
qed

(* 2 marks *)
theorem sum_one_is_self:
  "\<Squnion> {x} x"
proof-
  obtain y where a: "\<Squnion> {x} y "
    using A2 by blast
  then have b: "\<Squnion> {a. a \<sqsubseteq> x} y"
    using sum_parts_of_one_eq by blast
  have c : "\<Squnion> {a. a \<sqsubseteq> x} x"
    by (simp add: sum_parts_eq) 
  from b and c have "x = y"
    using A2' by blast
  then show ?thesis
    using a by blast 
qed

(* 2 marks *)
theorem sum_all_with_parts_overlapping_self:
  "\<Squnion> {z. \<forall>a. a \<sqsubseteq> z \<longrightarrow> a \<frown> x} x"
proof-
  have "{z. \<forall>a. a \<sqsubseteq> z \<longrightarrow> a \<frown> x} \<noteq> {}" using partof_overlaps by force 
  then have "\<exists>y. \<Squnion> {z. \<forall>a. a \<sqsubseteq> z \<longrightarrow> a \<frown> x} y"
    by (simp add: A2)
  then obtain y where a:"\<Squnion> {z. \<forall>a. a \<sqsubseteq> z \<longrightarrow> a \<frown> x} y"
    by blast
  then have b: "x = y"
    using A2' sum_all_with_parts_overlapping sum_one_is_self by blast
  then show ?thesis
  proof -
    show ?thesis
      using a b by blast
  qed
qed
(* 4 marks *)
theorem proper_have_nonoverlapping_proper:
  assumes "s \<sqsubset> r "
  shows "\<exists>a. a \<sqsubset> r \<and> a \<asymp> s"
proof(rule ccontr)
  assume 0 :"\<nexists>a. a \<sqsubset>r \<and> a \<asymp> s"
  then show "False"
  proof-
    have "\<forall>a. a \<sqsubset> r \<longrightarrow> a \<frown> s"
      using 0 disjoint_def by blast
    then have 1: "\<forall>a. a \<sqsubseteq> r \<longrightarrow> a \<frown> s"
      using assms overlaps_sym partof_overlaps properpartof_def by blast 
    have "\<Squnion> {r. \<forall>a. a \<sqsubseteq> r \<longrightarrow> a \<frown> s} s"
      using sum_all_with_parts_overlapping_self by blast 
    then have 2 :"r \<sqsubseteq> s"
      by (simp add: "1" partof.sumregions_def) 
    have 3: "s \<sqsubseteq> r"
      using assms properpartof_def by blast 
    from 2 and 3 have "s = r"
      by (simp add: both_partof_eq) 
    then show "False"
      using assms properpartof_def by blast   
  qed
qed

(* 1 mark *)
sublocale parthood_partial_order: order "(\<sqsubseteq>)" "(\<sqsubset>)"
proof
  show "\<And>x y. x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
    using both_partof_eq properpartof_def by auto
next
  show "\<And>x. x \<sqsubseteq> x"
    using in_sum_set_partof sum_one_is_self by auto    
next
  show "\<And>x y z. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    using A1 by blast
next
  show "\<And>x y. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    by (simp add: both_partof_eq)    
qed

end

section \<open>Part 2.3\<close>

locale sphere =
  fixes sphere :: "'a \<Rightarrow> bool"
begin

abbreviation AllSpheres :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<degree>" 10) where
  "\<forall>\<degree>x. P x \<equiv> \<forall>x. sphere x \<longrightarrow> P x"

abbreviation ExSpheres :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>\<degree>" 10) where
  "\<exists>\<degree>x. P x \<equiv> \<exists>x. sphere x \<and> P x"

end

locale mereology_sphere = mereology partof + sphere sphere
  for partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
  and sphere :: "'region \<Rightarrow> bool"
begin

definition exttan :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "exttan a b \<equiv> sphere a \<and> sphere b \<and> a \<asymp> b \<and> (\<forall>\<degree>x y. a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> b \<asymp> x \<and> b \<asymp> y
                                                        \<longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

definition inttan :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "inttan a b \<equiv> sphere a \<and> sphere b \<and> a \<sqsubset> b \<and> (\<forall>\<degree>x y. a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> x \<sqsubseteq> b \<and> y \<sqsubseteq> b
                                                        \<longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

definition extdiam :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "extdiam a b c \<equiv> exttan a c \<and> exttan b c
                 \<and> (\<forall>\<degree>x y. x \<asymp> c \<and> y \<asymp> c \<and> a \<sqsubseteq> x \<and> b \<sqsubseteq> y \<longrightarrow> x \<asymp> y)"

definition intdiam :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "intdiam a b c \<equiv> inttan a c \<and> inttan b c
                 \<and> (\<forall>\<degree>x y. x \<asymp> c \<and> y \<asymp> c \<and> exttan a x \<and> exttan b y \<longrightarrow> x \<asymp> y)"

abbreviation properconcentric :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "properconcentric a b \<equiv> a \<sqsubset> b
                        \<and> (\<forall>\<degree>x y. extdiam x y a \<and> inttan x b \<and> inttan y b \<longrightarrow> intdiam x y b)"

definition concentric :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<odot>" 100) where
  "a \<odot> b \<equiv> sphere a \<and> sphere b \<and> (a = b \<or> properconcentric a b \<or> properconcentric b a)"

definition onboundary :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "onboundary s r \<equiv> sphere s \<and> (\<forall>s'. s' \<odot> s \<longrightarrow> s' \<frown> r \<and> \<not> s' \<sqsubseteq> r)"

definition equidistant3 :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "equidistant3 x y z \<equiv> \<exists>\<degree>z'. z' \<odot> z \<and> onboundary y z' \<and> onboundary x z'"

definition betw :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("[_ _ _]" [100, 100, 100] 100) where
  "[x y z] \<equiv> sphere x \<and> sphere z
             \<and> (x \<odot> y \<or> y \<odot> z
                \<or> (\<exists>x' y' z' v w. x' \<odot> x \<and> y' \<odot> y \<and> z' \<odot> z
                                  \<and> extdiam x' y' v \<and> extdiam v w y' \<and> extdiam y' z' w))"

definition mid :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "mid x y z \<equiv> [x y z] \<and> (\<exists>\<degree>y'. y' \<odot> y \<and> onboundary x y' \<and> onboundary z y')"

definition equidistant4 :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100) where
  "x y \<doteq> z w \<equiv> \<exists>\<degree>u v. mid w u y \<and> mid x u v \<and> equidistant3 v z y"

definition oninterior :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "oninterior s r \<equiv> \<exists>s'. s' \<odot> s \<and> s' \<sqsubseteq> r"

definition nearer :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "nearer w x y z \<equiv> \<exists>\<degree>x'. [w x x'] \<and> \<not> x \<odot> x' \<and> w x' \<doteq> y z"

end

locale partial_region_geometry = mereology_sphere partof sphere
  for partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
  and sphere :: "'region \<Rightarrow> bool" +
  assumes A4: "\<lbrakk>x \<odot> y; y \<odot> z\<rbrakk> \<Longrightarrow> x \<odot> z"
      and A5: "\<lbrakk>x y \<doteq> z w; x' \<odot> x\<rbrakk> \<Longrightarrow> x' y \<doteq> z w"
      and A6: "\<lbrakk>sphere x; sphere y; \<not> x \<odot> y\<rbrakk>
               \<Longrightarrow> \<exists>\<degree>s. \<forall>\<degree>z. oninterior z s = nearer x z x y"
      and A7: "sphere x \<Longrightarrow> \<exists>\<degree>y. \<not> x \<odot> y \<and> (\<forall>\<degree>z. oninterior z x = nearer x z x y)"
      and A8: "x \<sqsubseteq> y = (\<forall>s. oninterior s x \<longrightarrow> oninterior s y)"
      and A9: "\<exists>\<degree>s. s \<sqsubseteq> r"
begin

(* 2 marks *)
thm equiv_def
theorem conc_equiv:
  "equiv {A. sphere A} {(x,y). x \<odot> y}"
proof- 
  have "\<forall>x\<in>{A. sphere A}. x \<odot> x"
    using concentric_def by auto 
  then have a:"refl_on {A. sphere A}{(x,y). x \<odot> y}"
    by (simp add: concentric_def refl_on_def')
  have "\<forall> y\<in>{A. sphere A}. x \<odot> y \<longrightarrow> y \<odot> x "
    using concentric_def by auto
  have b: "sym {(x,y). x \<odot> y}"
    using concentric_def sym_def by fastforce
  have "\<forall> z\<in>{A. sphere A}. (x \<odot> y \<and> y \<odot> z) \<longrightarrow> x \<odot> z"
    using A4 by blast
  have c:"trans {(x,y). x \<odot> y}"
    using concentric_def Relation.transp_trans A4 transp_def by blast 
  from a and b and c show ?thesis
    using equiv_def by blast
qed

(* 6 marks *)
theorem region_is_spherical_sum:
  "\<Squnion> {A. sphere A \<and> A \<sqsubseteq> x} x"
proof-
    have a: "\<exists>a. \<Squnion>{A. sphere A \<and> A \<sqsubseteq> x} a" using A2 A9 by simp
    then obtain a where a: "\<Squnion>{A. sphere A \<and> A \<sqsubseteq> x} a" by blast
    show ?thesis
proof (rule ccontr)
  assume b: "\<not>\<Squnion> {A. sphere A \<and> A \<sqsubseteq> x} x "
  show "False"
  proof-
   have c: "(\<forall>s. oninterior s x \<longrightarrow> oninterior s a)"
     using a concentric_def oninterior_def sumregions_def by auto
    then have d: "\<forall>s.(oninterior s a \<longleftrightarrow> oninterior s x)"
      using A8 a b sumregions_def by auto
    then have e:" \<forall>s.(oninterior s a \<longrightarrow> oninterior s x)"
      by simp

    then have 0: "x \<sqsubseteq> a"
      using A8 c by blast 
    then have 1:"a \<sqsubseteq> x"
      using A8 d by blast
    from 0 and 1 have "a = x"
      by auto
    then show ?thesis
      using a b by blast
  qed
 qed
qed
       
(* 1 mark *)
theorem region_spherical_interior:
  " sphere s \<and> oninterior s r \<longleftrightarrow> (\<exists>s'. sphere s' \<and> s' \<sqsubseteq> r \<and> oninterior s s')"
proof- 
  have "sphere s \<and>oninterior s r \<longleftrightarrow> (\<exists>a. a \<sqsubseteq> r \<and> oninterior s a)"
    using concentric_def oninterior_def by auto
  then obtain a where "\<exists>s. sphere s \<and> oninterior s r \<longleftrightarrow> (a \<sqsubseteq> r \<and> oninterior s a)"
    by auto
  then have "\<exists>\<degree>s'. s' \<sqsubseteq> a"
    by (simp add: A9) 
  show ?thesis
    using concentric_def oninterior_def by auto
qed

(* 2 marks *)
(*as we assume x and y have equal interiors, so according to A8, we could get x is part of y 
  and y is part of x, so use both_partof_eq leamma, we could know x=y. *)
theorem equal_interiors_equal_regions:
  assumes "\<forall>s. oninterior s x = oninterior s y "
  shows "x = y"
proof- 
  show ?thesis
    by (simp add: A8 assms both_partof_eq)
qed

(* 2 marks *)
theorem proper_have_nonoverlapping_proper_sphere:
  assumes "s \<sqsubset> r"
  shows "\<exists>\<degree>a. a \<sqsubset> r \<and> a \<asymp> s"
proof-
  have "\<exists>k.  k \<sqsubset> r \<and> k \<asymp> s"
    using assms proper_have_nonoverlapping_proper by blast
  then obtain k where 0:" k \<sqsubset> r \<and> k \<asymp> s" by blast
  then have 1: "\<exists>\<degree>a. a \<sqsubseteq> k"
    by (simp add: A9)
  then obtain a where "a \<sqsubseteq> k"
    by blast
  then show "\<exists>\<degree>a. a \<sqsubset> r \<and> a \<asymp> s"
    using "0" "1" disjoint_def overlaps_def by auto
  qed


(* 4 marks *)
theorem not_sphere_spherical_parts_gt1:
  assumes "\<not>sphere x"
      and "sphere s \<and>  s \<sqsubseteq> x"
    shows "\<exists>\<degree>a. a \<sqsubset> x \<and> a \<asymp> s"
proof-
  have 1:"s \<sqsubset> x"
  using assms(1) assms(2) parthood_partial_order.le_imp_less_or_eq by blast
  obtain s where "sphere s \<and>  s \<sqsubset> x"
    using "1" assms(2) by blast 
  then have "s \<sqsubset> x"
    by blast
  then show ?thesis
    using "1" proper_have_nonoverlapping_proper_sphere by blast 
qed

end

section \<open>Part 3\<close>

context mereology_sphere
begin

(* 3 marks *)
lemma
  assumes T4: "\<And>x y. \<lbrakk>sphere x; sphere y\<rbrakk> \<Longrightarrow> x y \<doteq> y x"
      and A9: "\<exists>\<degree>s. s \<sqsubseteq> r"
  shows False
oops

(* 3 marks *)
definition equidistant3' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "equidistant3' x y z \<equiv> undefined"

no_notation equidistant4 ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100)

definition equidistant4' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100) where
  "x y \<doteq> z w \<equiv> \<exists>\<degree>u v. mid w u y \<and> mid x u v \<and> equidistant3' v z y"

end

datatype two_reg = Left | Right | Both

(* 2 marks *)
definition tworeg_partof :: "two_reg \<Rightarrow> two_reg \<Rightarrow> bool" (infix "\<sqsubseteq>" 100) where
  "x \<sqsubseteq> y \<equiv> undefined"

(* 12 marks *)
interpretation mereology "(\<sqsubseteq>)"
oops


end