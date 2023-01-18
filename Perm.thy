theory Perm
imports Complex_Main VHelper Lang
begin

text \<open> This file contains a soundness proof for CSL with multiple resources
  and permissions. \<close>

text \<open> (Adapted to Isabelle 2016-1 by Qin Yu and James Brotherston) \<close>

subsection \<open> Permission model \<close>

text \<open> Fractional permissions are rational numbers in the range (0,1]. \<close>

typedef myfrac = "{x::rat. 0 < x \<and> x \<le> 1}" 
by (rule_tac x="0.5" in exI, simp)

definition "pfull \<equiv> Abs_myfrac 1"        (*r Full permission *)

type_synonym pheap  = "(nat \<rightharpoonup> nat * myfrac)"       (*r Permission heaps *)
type_synonym pstate = "stack \<times> pheap"               (*r Permission states *)

text \<open> Definition when two permission heaps are composable. \<close>

definition
  pdisj :: "pheap \<Rightarrow> pheap \<Rightarrow> bool"
where
  "pdisj h1 h2 \<equiv> (\<forall>x. case h1 x of None \<Rightarrow> True | Some y1 \<Rightarrow>
                      (case h2 x of None \<Rightarrow> True | Some y2 \<Rightarrow>
                       fst y1 = fst y2 \<and>
                       Rep_myfrac (snd y1) + Rep_myfrac (snd y2) \<le> 1))"

text \<open> Composition of two permission heaps. \<close>

definition
  padd :: "pheap \<Rightarrow> pheap \<Rightarrow> pheap"
where
  "padd h1 h2 \<equiv> 
     (\<lambda>x. case h1 x of None \<Rightarrow> h2 x | Some y1 \<Rightarrow>
          (case h2 x of None \<Rightarrow> h1 x | Some y2 \<Rightarrow>
           Some (fst y1, Abs_myfrac (Rep_myfrac (snd y1) + Rep_myfrac (snd y2)))))"

text \<open> Composition of two permission heaps, better for automation. \<close>

definition
  mypadd :: "pheap option \<Rightarrow> pheap option \<Rightarrow> pheap option"
  (infixr "\<oplus>" 100)
where
  "xo \<oplus> yo \<equiv> case xo of None \<Rightarrow> None | Some x \<Rightarrow>
             (case yo of None \<Rightarrow> None | Some y \<Rightarrow> 
              if pdisj x y then Some (padd x y) else None)"

text \<open> Full-permission domain of a permission heap \<close>

definition "fpdom h \<equiv> {x. \<exists>v. h x = Some (v, pfull)}"

text \<open> Mapping from permission heaps to normal heaps \<close>

definition
  ptoheap :: "pheap option \<Rightarrow> heap \<Rightarrow> bool"
where
  "ptoheap ho h \<equiv> case ho of None \<Rightarrow> False | Some ha \<Rightarrow>
                  (\<forall>x. case ha x of None \<Rightarrow> h x = None | Some y \<Rightarrow> 
                   snd y = pfull \<and> h x = Some (fst y))"

text \<open> Basic properties of fractions in the range (0,1] \<close>

lemmas rat_simps = 
  add_rat eq_rat one_rat zero_rat mult_rat le_rat minus_rat diff_rat

lemmas frac_simps =
  Rep_myfrac_inverse Rep_myfrac Abs_myfrac_inverse Abs_myfrac_inject

lemma frac_contra[simp]: 
  "\<not> (Rep_myfrac pfull + Rep_myfrac b \<le> 1)"
  "\<not> (Rep_myfrac b + Rep_myfrac pfull \<le> 1)"
by (case_tac b, auto simp add: pfull_def frac_simps)+

lemma frac_pos: "0 < Rep_myfrac x" 
by (case_tac x, simp add: frac_simps)

lemma frac_pos2[simp]: 
  "0 < Rep_myfrac x + Rep_myfrac y"
  "0 < Rep_myfrac x + (Rep_myfrac y + Rep_myfrac z)"
by (case_tac x, (case_tac y)?, (case_tac z)?, simp add: frac_simps)+

text \<open> Properties of permission-heaps \<close>

lemma pdisj_empty[simp]:
  "pdisj x Map.empty"
  "pdisj Map.empty x"
by (clarsimp simp add: pdisj_def split: option.splits)+

lemma pdisj_upd: "h x = Some (w, pfull) \<Longrightarrow> pdisj (h(x \<mapsto> (v, pfull))) h' = pdisj h h'"
by (simp add: pdisj_def, rule iff_allI, auto split: option.splits)

lemma pdisj_comm: "pdisj h1 h2 = pdisj h2 h1"
by (fastforce split: option.splits simp add: pdisj_def)

lemma padd_empty[simp]:
  "padd x Map.empty = x"
  "padd Map.empty x = x"
by (rule ext, clarsimp simp add: padd_def split: option.splits)+

lemma padd_comm[simp]: "pdisj x y \<Longrightarrow> padd y x = padd x y"
by (fastforce split: option.splits simp add: padd_def pdisj_def algebra_simps)

lemma pdisj_padd: "\<lbrakk> pdisj y z ; pdisj x (padd y z) \<rbrakk> \<Longrightarrow> (pdisj x y \<and> pdisj x z)"
apply (clarsimp simp add: pdisj_def padd_def all_conj_distrib [symmetric])
apply (drule_tac a=xa in allD)+
apply (auto split: option.splits simp add: algebra_simps frac_simps)
apply (cut_tac x=be in frac_pos, simp)
apply (cut_tac x=bd in frac_pos, simp)
done

lemma pdisjE[elim]: 
  "\<lbrakk> pdisj x (padd y z) ; pdisj y z \<rbrakk> \<Longrightarrow> pdisj x y"
  "\<lbrakk> pdisj x (padd y z) ; pdisj y z \<rbrakk> \<Longrightarrow> pdisj x z"
by (drule (1) pdisj_padd, simp)+

lemma pdisj_padd_comm: "\<lbrakk> pdisj y (padd x z); pdisj x z \<rbrakk> \<Longrightarrow> pdisj x (padd y z)"
apply (clarsimp simp add: pdisj_def padd_def all_conj_distrib [symmetric])
apply (drule_tac a=xa in allD)+
apply (auto split: option.splits simp add: algebra_simps frac_simps)
apply (subst Abs_myfrac_inverse, simp add: frac_simps)
apply (cut_tac x=bf in frac_pos, simp)
apply (cut_tac x=bd in frac_pos, simp)
done

lemma pdisj_padd_expand:
  "pdisj x y \<Longrightarrow> pdisj (padd x y) z = (pdisj x (padd y z) \<and> pdisj y z)"
apply (simp add: pdisj_comm, rule iffI)
 apply (frule (1) pdisj_padd_comm)
 apply (drule (1) pdisj_padd, subst padd_comm, simp_all add: pdisj_comm) 
apply (clarify, rule pdisj_padd_comm, simp_all add: pdisj_comm)
done

lemma padd_assoc: "\<lbrakk> pdisj x (padd y z) ; pdisj y z \<rbrakk> \<Longrightarrow> padd (padd x y) z = padd x (padd y z)"
apply (clarsimp simp add: pdisj_def padd_def all_conj_distrib [symmetric], rule ext)
apply (drule_tac a=xa in allD)+
apply (auto split: option.splits simp add: algebra_simps frac_simps)
apply (subst Abs_myfrac_inverse, simp_all add: frac_simps)
apply (cut_tac x=be in frac_pos, simp)
done

lemma padd_left_comm: "\<lbrakk> pdisj x (padd y z) ; pdisj y z \<rbrakk> \<Longrightarrow> padd x (padd y z) = padd y (padd x z)"
apply (clarsimp simp add: pdisj_def padd_def all_conj_distrib [symmetric], rule ext)
apply (drule_tac a=xa in allD)+
apply (auto split: option.splits simp add: algebra_simps frac_simps)
apply (subst Abs_myfrac_inverse, simp_all add: frac_simps)
apply (cut_tac x=bf in frac_pos, simp)
done

lemma padd_cancel: "\<lbrakk> padd x y = padd x z ; pdisj x y; pdisj x z \<rbrakk> \<Longrightarrow> y = z"
apply (clarsimp simp add: pdisj_def padd_def all_conj_distrib [symmetric], rule ext)
apply (drule_tac a=xa in allD |drule_tac x=xa in fun_cong)+
apply (auto split: option.splits simp add: algebra_simps frac_simps)
apply (case_tac b, case_tac ba, clarsimp simp add: frac_simps)
apply (case_tac b, case_tac ba, clarsimp simp add: frac_simps)
apply (case_tac b, case_tac ba, clarsimp simp add: frac_simps)
done

lemma dom_padd[simp]: "dom (padd x y) = dom x \<union> dom y"
by (rule set_eqI, simp add: padd_def dom_def split: option.splits)

lemma fpdom_padd[elim]:
  "pdisj h1 h2 \<Longrightarrow> fpdom h1 \<subseteq> fpdom (padd h1 h2)"
  "pdisj h1 h2 \<Longrightarrow> fpdom h2 \<subseteq> fpdom (padd h1 h2)"
apply (auto simp add: fpdom_def pdisj_def padd_def disjoint_def split: option.splits)
apply (drule_tac a=x in allD, fastforce)+
done

lemma pa_empty[simp]:
  "x \<oplus> Some Map.empty = x"
  "Some Map.empty \<oplus> x = x"
by (auto simp add: mypadd_def split: option.splits)

lemma pa_none[simp]:
  "x \<oplus> None = None"
  "None \<oplus> x = None"
by (auto simp add: mypadd_def split: option.splits)

lemma pa_comm: "y \<oplus> x = x \<oplus> y"
by (auto simp add: mypadd_def pdisj_comm split: option.splits)

lemma pa_assoc: "(x \<oplus> y) \<oplus> z = x \<oplus> y \<oplus> z"
apply (auto simp add: mypadd_def padd_assoc pdisj_padd_expand split: option.splits)
apply (erule notE, fast)
done

lemma pa_left_comm: "y \<oplus> x \<oplus> z = x \<oplus> y \<oplus> z"
apply (auto simp add: mypadd_def padd_left_comm split: option.splits)
apply (erule_tac[!] notE, (erule (1) pdisj_padd_comm |erule (1) pdisjE)+)
done

lemma some_padd: "pdisj h1 h2 \<Longrightarrow> Some (padd h1 h2) = Some h1 \<oplus> Some h2"
by (simp add: mypadd_def)

lemmas pa_ac = pa_comm pa_assoc pa_left_comm some_padd

lemma pa_cancel: 
  "\<lbrakk> x \<oplus> y = x \<oplus> z;  x \<oplus> y \<noteq> None \<rbrakk> \<Longrightarrow> y = z"
apply (simp add: mypadd_def split: option.splits if_splits) 
apply (clarify, erule (2) padd_cancel)
done

lemma ptoD: "\<lbrakk> ptoheap x z; ptoheap y z \<rbrakk> \<Longrightarrow> x = y"
apply (clarsimp simp add: ptoheap_def split: option.splits)
apply (rule ext)
apply ((drule_tac a=xa in allD)+, auto)
apply (case_tac "x2a xa", case_tac "x2 xa", simp_all, fast+)
done

lemma pdisj_search1: 
  "ptoheap (Some x \<oplus> Some y) hh             \<Longrightarrow> pdisj x y"
  "ptoheap (Some x \<oplus> Some y \<oplus> z) hh         \<Longrightarrow> pdisj x y"
  "ptoheap (Some x \<oplus> z \<oplus> Some y) hh         \<Longrightarrow> pdisj x y"
  "ptoheap (Some x \<oplus> z \<oplus> Some y \<oplus> w) hh     \<Longrightarrow> pdisj x y"
  "ptoheap (Some x \<oplus> z \<oplus> w \<oplus> Some y) hh     \<Longrightarrow> pdisj x y"
  "ptoheap (Some x \<oplus> z \<oplus> w \<oplus> Some y \<oplus> v) hh \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> Some x \<oplus> Some y) hh         \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> Some x \<oplus> Some y \<oplus> w) hh     \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> Some x \<oplus> w \<oplus> Some y) hh     \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> Some x \<oplus> w \<oplus> Some y \<oplus> v) hh \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> Some x \<oplus> w \<oplus> v \<oplus> Some y) hh \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> w \<oplus> Some x \<oplus> Some y) hh     \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> w \<oplus> Some x \<oplus> Some y \<oplus> v) hh \<Longrightarrow> pdisj x y"
  "ptoheap (z \<oplus> w \<oplus> Some x \<oplus> v \<oplus> Some y) hh \<Longrightarrow> pdisj x y"
apply (simp_all add: ptoheap_def mypadd_def, case_tac[!] "pdisj x y", simp_all) 
apply (auto split: option.splits if_split_asm)
apply (erule notE | fast | erule pdisjE [rotated])+
done

lemma pdisj_comm_implies: "pdisj h1 h2 \<Longrightarrow> pdisj h2 h1"
by (fastforce split: option.splits simp add: pdisj_def)

lemmas pdisj_search[elim] = 
  pdisj_search1 pdisj_search1[THEN pdisj_comm_implies]

subsection \<open> Assertions with permissions \<close>

datatype assn = 
    Aemp                                           (*r Empty heap *)
  | Apsto myfrac exp exp                           (*r Singleton heap *)
  | Astar assn assn      (infixl "**" 100)         (*r Separating conjunction *)
  | Awand assn assn                                (*r Separating implication *)
  | Apure bexp                                     (*r Pure assertion *)
  | Aconj assn assn                                (*r Conjunction *)
  | Adisj assn assn                                (*r Disjunction *)
  | Aex "(nat \<Rightarrow> assn)"                            (*r Existential quantification *)

text \<open> Separating conjunction of a finite list of assertions is 
  just a derived assertion. \<close>

primrec 
  Aistar :: "assn list \<Rightarrow> assn"
where
  "Aistar [] = Aemp"
| "Aistar (P # Ps) = Astar P (Aistar Ps)"

primrec
  sat :: "pstate \<Rightarrow> assn \<Rightarrow> bool" (infixl "\<Turnstile>" 60)
where
  "(\<sigma> \<Turnstile> Aemp)      = (snd \<sigma> = empty)" 
| "(\<sigma> \<Turnstile> Apsto k E E') = (dom (snd \<sigma>) = { edenot E (fst \<sigma>) } \<and> (snd \<sigma>) (edenot E (fst \<sigma>)) = Some (edenot E' (fst \<sigma>), k))" 
| "(\<sigma> \<Turnstile> P ** Q)    = (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> P \<and> (fst \<sigma>, h2) \<Turnstile> Q \<and> snd \<sigma> = padd h1 h2 \<and> pdisj h1 h2)" 
| "(\<sigma> \<Turnstile> Awand P Q) = (\<forall>h. disjoint (dom (snd \<sigma>)) (dom h) \<and> (fst \<sigma>, h) \<Turnstile> P \<longrightarrow> (fst \<sigma>, snd \<sigma> ++ h) \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Apure B)   = bdenot B (fst \<sigma>)" 
| "(\<sigma> \<Turnstile> Aconj P Q) = (\<sigma> \<Turnstile> P \<and> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Adisj P Q) = (\<sigma> \<Turnstile> P \<or> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Aex PP)    = (\<exists>v. \<sigma> \<Turnstile> PP v)" 

text \<open> Shorthand for full permission \<close>

definition 
  Aptsto :: "exp \<Rightarrow> exp \<Rightarrow> assn"  (infixl "\<longmapsto>" 200)
where
  "E \<longmapsto> E' \<equiv> Apsto pfull E E'"

lemma sat_Aptsto[simp]: 
  "(\<sigma> \<Turnstile> E \<longmapsto> E') = (dom (snd \<sigma>) = { edenot E (fst \<sigma>) }
                      \<and> (snd \<sigma>) (edenot E (fst \<sigma>)) = Some (edenot E' (fst \<sigma>), pfull))" 
by (simp add: Aptsto_def)

definition 
  implies :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixl "\<sqsubseteq>" 60)
where
  "P \<sqsubseteq> Q \<equiv> (\<forall>\<sigma>. \<sigma> \<Turnstile> P \<longrightarrow> \<sigma> \<Turnstile> Q)"

lemma sat_istar_map_expand:
  "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<Turnstile> Aistar (map f l)
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> f r
              \<and> (fst \<sigma>, h2) \<Turnstile> Aistar (map f (remove1 r l))
              \<and> snd \<sigma> = padd h1 h2 \<and> pdisj h1 h2)"
apply (case_tac \<sigma>, rename_tac s h, clarify)
apply (induct l arbitrary: \<sigma>, simp_all, clarsimp, safe)
apply (intro exI conjI, simp+)
 apply (drule pdisj_padd, simp, clarsimp)
apply (rule padd_left_comm, simp_all)
apply (rule pdisj_padd_comm, simp_all)

apply (intro exI conjI, simp+)
apply (drule pdisj_padd, simp, clarsimp)
apply (rule padd_left_comm, simp_all)
apply (rule pdisj_padd_comm, simp_all)
done

subsubsection \<open> Precision \<close>

text \<open> We say that an assertion is precise if for any given heap, there is at
most one subheap that satisfies the formula. (The formal definition below says 
that if there are two such subheaps, they must be equal.) \<close>

definition
  precise :: "assn \<Rightarrow> bool"
where
  "precise P \<equiv> \<forall>h1 h2 h1' h2' s. pdisj h1 h2 \<and> pdisj h1' h2'
                   \<and> padd h1 h2 = padd h1' h2' \<and> (s, h1) \<Turnstile> P \<and> (s, h1') \<Turnstile> P 
               \<longrightarrow> h1 = h1'"

text \<open> A direct consequence of the definition that is more useful in
Isabelle, because unfolding the definition slows down Isabelle's simplifier
dramatically. \<close>

lemma preciseD:
  "\<lbrakk> precise P; (s, x) \<Turnstile> P; (s, x') \<Turnstile> P; padd x y = padd x' y'; 
     pdisj x y; pdisj x' y' \<rbrakk> \<Longrightarrow>
    x = x' \<and> y = y'"
unfolding precise_def
by (drule all5_impD, (erule conjI)+, simp_all, drule padd_cancel)

text \<open> The separating conjunction of precise assertions is precise: \<close>

lemma precise_istar:
  "\<forall>x \<in> set l. precise x \<Longrightarrow> precise (Aistar l)"
apply (induct l, simp_all (no_asm) add: precise_def)
apply (clarsimp simp add: padd_assoc pdisj_padd_expand)
apply (drule (3) preciseD, simp_all, clarsimp)
apply (drule (3) preciseD, simp_all)
done

subsubsection \<open> Auxiliary definition for resource environments \<close>

definition
  envs :: "('a \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> assn"
where
  "envs \<Gamma> l l' \<equiv> Aistar (map \<Gamma> (list_minus l l'))"

lemma sat_envs_expand:
  "\<lbrakk> r \<in> set l; r \<notin> set l'; distinct l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<Turnstile> envs \<Gamma> l l' 
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> \<Gamma> r 
              \<and> (fst \<sigma>, h2) \<Turnstile> envs \<Gamma> (removeAll r l) l'
              \<and> snd \<sigma> = padd h1 h2 \<and> pdisj h1 h2)" 
apply (simp add: envs_def distinct_remove1_removeAll [THEN sym] add: list_minus_remove1)
apply (subst sat_istar_map_expand [where f=\<Gamma> and r=r], simp_all)
done

lemma envs_upd:
  "r \<notin> set l \<Longrightarrow> envs (\<Gamma>(r := R)) l l' = envs \<Gamma> l l'"
  "r \<in> set l' \<Longrightarrow> envs (\<Gamma>(r := R)) l l' = envs \<Gamma> l l'"
by (simp_all add: envs_def)

lemma envs_removeAll_irr: 
  "r \<notin> set l \<Longrightarrow> envs \<Gamma> l (removeAll r l') = envs \<Gamma> l l'"
by (simp add: envs_def list_minus_removeAll_irr)

lemma envs_removeAll2:
  "r \<in> set l' \<Longrightarrow> envs \<Gamma> (removeAll r l) (removeAll r l') = envs \<Gamma> l l'"
by (simp add: envs_def list_minus_removeAll2)

lemma envs_app:
  "disjoint (set x) (set z) \<Longrightarrow> envs \<Gamma> (x @ z) (y @ z) = envs \<Gamma> x y"
  "disjoint (set z) (set x) \<Longrightarrow> envs \<Gamma> (z @ x) (z @ y) = envs \<Gamma> x y"
by (simp_all add: envs_def list_minus_appl list_minus_appr)

subsubsection \<open> Free variables and substitutions \<close>

primrec
  fvA :: "assn \<Rightarrow> var set"
where
  "fvA (Aemp)      = {}"
| "fvA (Apure B)   = fvB B"
| "fvA (Apsto k e1 e2) = (fvE e1 \<union> fvE e2)"
| "fvA (P ** Q)    = (fvA P \<union> fvA Q)"
| "fvA (Awand P Q) = (fvA P \<union> fvA Q)"
| "fvA (Aconj P Q) = (fvA P \<union> fvA Q)"
| "fvA (Adisj P Q) = (fvA P \<union> fvA Q)"
| "fvA (Aex P)     = (\<Union>x. fvA (P x))"

definition
  fvAs :: "('a \<Rightarrow> assn) \<Rightarrow> var set"
where
  "fvAs \<Gamma> = (\<Union>x. fvA (\<Gamma> x))"

primrec
  subA :: "var \<Rightarrow> exp \<Rightarrow> assn \<Rightarrow> assn"
where
  "subA x E (Aemp)      = Aemp"
| "subA x E (Apure B)   = Apure (subB x E B)"
| "subA x E (Apsto k e1 e2) = (Apsto k (subE x E e1) (subE x E e2))"
| "subA x E (P ** Q)    = (subA x E P ** subA x E Q)"
| "subA x E (Awand P Q) = Awand (subA x E P) (subA x E Q)"
| "subA x E (Aconj P Q) = Aconj (subA x E P) (subA x E Q)"
| "subA x E (Adisj P Q) = Adisj (subA x E P) (subA x E Q)"
| "subA x E (Aex PP)    = Aex (\<lambda>n. subA x E (PP n))"

lemma subAptsto[simp]:
  "subA x E (e1 \<longmapsto> e2) = (subE x E e1 \<longmapsto> subE x E e2)"
by (simp add: Aptsto_def)

lemma subA_assign:
 "(s,h) \<Turnstile> subA x E P \<longleftrightarrow> (s(x := edenot E s), h) \<Turnstile> P"
by (induct P arbitrary: h, simp_all add: subE_assign subB_assign fun_upd_def)

lemma fvA_istar[simp]: "fvA (Aistar Ps) = (\<Union>P \<in> set Ps. fvA P)"
by (induct Ps, simp_all)

text \<open> Proposition 4.2 for assertions \<close>

lemma assn_agrees: "agrees (fvA P) s s' \<Longrightarrow> (s, h) \<Turnstile> P \<longleftrightarrow> (s', h) \<Turnstile> P"
apply (induct P arbitrary: h, simp_all add: bexp_agrees)
apply (clarsimp, (subst exp_agrees, simp_all)+ )
apply (rule iff_exI, simp add: agrees_def)
done

text \<open> Corollaries of Proposition 4.2, useful for automation. \<close>

lemma assns_agrees:
  "agrees (fvAs J) s s' \<Longrightarrow> (s, h) \<Turnstile> envs J l1 l2 \<longleftrightarrow> (s', h) \<Turnstile> envs J l1 l2"
apply (clarsimp simp add: envs_def, subst assn_agrees, simp_all)
apply (erule agrees_search, auto simp add: fvAs_def)
done

corollary assns_agreesE[elim]:
  "\<lbrakk> (s, h) \<Turnstile> envs J l1 l2 ; agrees (fvAs J) s s' \<rbrakk> \<Longrightarrow> (s',h) \<Turnstile> envs J l1 l2"
by (simp add: assns_agrees)

corollary assn_agrees2[simp]:
  "x \<notin> fvA P \<Longrightarrow> (s(x := v), h) \<Turnstile> P \<longleftrightarrow> (s, h) \<Turnstile> P"
by (rule assn_agrees, simp add: agrees_def)

corollary assns_agrees2[simp]:
  "x \<notin> fvAs J \<Longrightarrow> (s(x := v), h) \<Turnstile> envs J l l' \<longleftrightarrow> (s, h) \<Turnstile> envs J l l'"
by (rule assns_agrees, simp add: agrees_def)

subsection \<open> Meaning of CSL judgments \<close>

text \<open> Definition 5.1: Configuration safety. \<close>

primrec
  safe :: "nat \<Rightarrow> cmd \<Rightarrow> stack \<Rightarrow> pheap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "safe 0       C s h \<Gamma> Q = True"
| "safe (Suc n) C s h \<Gamma> Q = (
(* Condition (i) *)
            (C = Cskip \<longrightarrow> (s, h) \<Turnstile> Q)
(* Condition (ii) *)
          \<and> (\<forall>hF hh. ptoheap (Some h \<oplus> hF) hh \<longrightarrow> \<not> aborts C (s, hh))
(* Condition (iii) *)
          \<and> accesses C s \<subseteq> dom h
          \<and> writes C s \<subseteq> fpdom h
(* Condition (iv) *)
          \<and> (\<forall>hJ hF hh C' \<sigma>'.
                  red C (s, hh) C' \<sigma>'
                 \<longrightarrow> ptoheap (Some h \<oplus> Some hJ \<oplus> hF) hh
                 \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (llocked C') (llocked C)
                 \<longrightarrow> (\<exists>h' hJ'.
                         ptoheap (Some h' \<oplus> Some hJ' \<oplus> hF) (snd \<sigma>')
                       \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (llocked C) (llocked C')
                       \<and> safe n C' (fst \<sigma>') h' \<Gamma> Q)))"

text \<open> The predicate @{text "safe n C s h \<Gamma> Q"} says that the command @{text C} and the logical state
  @{text "(s, h)"} are safe with respect to the resource environment @{text \<Gamma>} and the 
  postcondition @{text Q} for @{text n} execution steps. 
  Intuitively, any configuration is safe for zero steps.
  For @{text "n + 1"} steps, it must 
  (i) satisfy the postcondition if it is a terminal configuration,
  (ii) not abort, 
  (iii) access memory only inside its footprint, and 
  (iv) after any step it does, re-establish the resource invariant and be safe for 
  another @{text n} steps. \<close>

text \<open> Definition 5.2: The meaning of CSL judgements. \<close>

definition
  CSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> cmd \<Rightarrow> assn \<Rightarrow> bool"
  ("_ \<turnstile> { _ } _ { _ }")
where
  "\<Gamma> \<turnstile> {P} C {Q} \<equiv> (user_cmd C \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> safe n C s h \<Gamma> Q))" 

subsubsection \<open> Basic properties of Definition 5.1 \<close>

text \<open> Proposition 4.3: Monotonicity with respect to the step number. \<close>

lemma safe_mon:
  "\<lbrakk> safe n C s h J Q; m \<le> n \<rbrakk> \<Longrightarrow> safe m C s h J Q"
apply (induct m arbitrary: C s n h l, simp) 
apply (case_tac n, clarify)
apply (simp only: safe.simps, clarsimp)
apply (drule all5D, drule (2) all_imp2D, clarsimp)
apply (rule_tac x="h'" in exI, rule_tac x="hJ'" in exI, simp)
done

text \<open> Proposition 4.4: Safety depends only the free variables
        of @{term "C"}, @{term "Q"}, and @{term "\<Gamma>"}. \<close>

lemma safe_agrees: 
  "\<lbrakk> safe n C s h \<Gamma> Q ; 
     agrees (fvC C \<union> fvA Q \<union> fvAs \<Gamma>) s s' \<rbrakk>
   \<Longrightarrow> safe n C s' h \<Gamma> Q"
apply (induct n arbitrary: C s s' h bl, simp, simp only: safe.simps, clarify)
apply (rule conjI, clarsimp, subst assn_agrees, subst agreesC, assumption+)
apply (rule conjI, clarsimp)
 apply (drule_tac aborts_agrees, simp, fast, simp, simp)
apply (rule conjI, subst (asm) accesses_agrees, simp_all)
apply (rule conjI, subst (asm) writes_agrees, simp_all)
apply (clarify, drule_tac X="fvC C \<union> fvAs \<Gamma> \<union> fvA Q" in red_agrees, 
       simp (no_asm), fast, simp (no_asm), fast, clarify)
apply (drule allD, drule (1) all5_impD, clarsimp)
apply (drule imp2D, erule_tac[2] assns_agreesE, simp_all add: agreesC, clarify)
apply (rule_tac x="h'a" and y="hJ'" in ex2I, simp add: pa_ac)
apply (rule conjI, erule assns_agreesE, subst agreesC, assumption)
apply (erule (1) mall4_imp2D, simp add: agreesC)
apply (drule red_properties, auto)
done

subsection \<open> Soundness of the proof rules \<close>

subsubsection \<open> Skip \<close>

lemma safe_skip[intro!]:
  "(s,h) \<Turnstile> Q \<Longrightarrow> safe n Cskip s h J Q"
by (induct n, simp_all)

theorem rule_skip: 
  "\<Gamma> \<turnstile> {P} Cskip {P}"
by (auto simp add: CSL_def)

subsubsection \<open> Parallel composition \<close>

lemma disj_conv:
  "pdisj h1 h2 \<Longrightarrow> disjoint (fpdom h1) (dom h2)"
  "pdisj h1 h2 \<Longrightarrow> disjoint (dom h1) (fpdom h2)"
by (simp add: fpdom_def pdisj_def disjoint_def, rule set_eqI, drule_tac a=x in allD, clarsimp)+

lemma safe_par:
 "\<lbrakk> safe n C1 s h1 J Q1; safe n C2 s h2 J Q2;
    wf_cmd (Cpar C1 C2);
    pdisj h1 h2;
    disjoint (fvC C1 \<union> fvA Q1 \<union> fvAs J) (wrC C2);
    disjoint (fvC C2 \<union> fvA Q2 \<union> fvAs J) (wrC C1)\<rbrakk>
  \<Longrightarrow> safe n (Cpar C1 C2) s (padd h1 h2) J (Q1 ** Q2)"
apply (induct n arbitrary: C1 C2 s h1 h2 bl1 bl2, simp, clarsimp)
apply (rule conjI, clarify)
 -- \<open> no aborts \<close>
 apply (erule aborts.cases, simp_all add: pa_ac)
   apply (clarify, drule_tac a="Some h2 \<oplus> hF" in all2_impD, simp add: pa_ac, clarsimp)
   apply (clarify, drule_tac a="Some h1 \<oplus> hF" in all2_impD, simp add: pa_ac, clarsimp)
 -- \<open> no races \<close>
 apply (clarsimp, erule notE, (erule disjoint_search [rotated])+, erule disj_conv)+
-- \<open> accesses \<close>
apply (rule conjI, erule order_trans, simp)+
apply (rule conjI, erule order_trans, erule fpdom_padd)+
-- \<open> step \<close>
 apply (clarsimp, erule red_par_cases, simp_all)
 -- \<open> C1 does a step \<close>
  apply (clarify, drule_tac a="hJ" and b="Some h2 \<oplus> hF" in all2D, drule all4_impD, 
         simp_all add: envs_app locked_eq, clarsimp simp add: pa_ac)
  apply (subgoal_tac "pdisj h' h2", erule_tac[2] pdisj_search)
  apply (rule_tac x="padd h' h2" and y="hJ'" in ex2I, simp add: pa_ac)
  apply (frule (1) red_wf_cmd, drule red_properties, clarsimp)
  apply (drule_tac a=C1' and b=C2 in mall2D, simp add: hsimps)
  apply (drule mall3_imp2D, erule_tac[3] mimp3D, simp_all add: hsimps)
  apply (rule_tac s="s" in safe_agrees)
  apply (rule_tac n="Suc n" in safe_mon, simp add: pa_ac, simp)
  apply (fastforce simp add: agreesC disjoint_commute)
  apply (intro conjI | erule (1) disjoint_search)+
 -- \<open> C2 does a step \<close>
  apply (clarify, drule_tac a="hJ" and b="Some h1 \<oplus> hF" in all2D, drule all4_imp2D, 
         simp_all add: hsimps envs_app pa_ac, clarsimp)
  apply (subgoal_tac "pdisj h1 h'", erule_tac[2] pdisj_search)
  apply (rule_tac x="padd h1 h'" and y="hJ'" in ex2I, simp add: pa_ac)
  apply (frule (1) red_wf_cmd, drule red_properties, clarsimp)
  apply (drule_tac a=C1 and b=C2' in mall2D, simp add: hsimps)
  apply (drule mall3_imp2D, erule_tac[3] mimp3D, simp_all add: hsimps)
  apply (rule_tac s="s" in safe_agrees)
   apply (rule_tac n="Suc n" in safe_mon, simp add: pa_ac, simp)
  apply (subst agreesC, bestsimp, bestsimp, bestsimp)
-- \<open> Par skip skip \<close> 
apply (clarify)
apply (rule_tac x="padd h1 h2" and y="hJ" in ex2I, simp add: pa_ac)
apply (rule_tac safe_skip, simp, (rule exI, erule conjI)+, simp)
done

theorem rule_par:
 "\<lbrakk> \<Gamma> \<turnstile> {P1} C1 {Q1} ; \<Gamma> \<turnstile> {P2} C2 {Q2};
    disjoint (fvC C1 \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrC C2);
    disjoint (fvC C2 \<union> fvA Q2 \<union> fvAs \<Gamma>) (wrC C1) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P1 ** P2} (Cpar C1 C2) {Q1 ** Q2}"
by (auto simp add: CSL_def intro!: safe_par)

subsubsection \<open> Resource declaration \<close>

lemma safe_resource:
 "\<lbrakk> safe n C s h (\<Gamma>(r := R)) Q; wf_cmd C; disjoint (fvA R) (wrC C) \<rbrakk> \<Longrightarrow>
     (\<forall>hR. r \<notin> locked C \<longrightarrow> pdisj h hR \<longrightarrow> (s,hR) \<Turnstile> R \<longrightarrow> safe n (Cresource r C) s (padd h hR) \<Gamma> (Q ** R))
   \<and> (r \<in> locked C \<longrightarrow> safe n (Cresource r C) s h \<Gamma> (Q ** R))"
apply (induct n arbitrary: C s h, simp, clarsimp simp add: pa_ac)
apply (rule conjI, clarify)
 apply (rule conjI, clarify)
  -- \<open> no aborts \<close>
  apply (erule aborts.cases, simp_all, clarsimp)
  apply (drule_tac a="Some hR \<oplus> hF" in all2_impD, simp add: pa_ac, simp)
 -- \<open> accesses \<close>
 apply (rule conjI, erule order_trans, simp)
 apply (rule conjI, erule order_trans, erule fpdom_padd)
 -- \<open> step \<close>
 apply (clarify, frule red_properties, clarsimp)
 apply (erule red.cases, simp_all, clarsimp, rename_tac C s hh C' s' hh')
 -- \<open> normal step \<close>
apply (subgoal_tac "pdisj hR hJ", erule_tac[2] pdisj_search)
  apply (case_tac "r \<in> set (llocked C')", simp_all add: locked_eq)
   apply (drule_tac a="padd hJ hR" and b="hF" and c="hh" in all3D, 
          drule_tac a=C' and b=s' and c=hh' in all3D, simp_all add: pa_ac)
   apply (drule impD, subst sat_envs_expand [where r=r], simp_all)
     apply (rule wf_cmd_distinct_locked, erule (1) red_wf_cmd)
    apply (intro exI conjI, simp, simp_all add: envs_upd)
   apply (clarsimp simp add: envs_removeAll_irr) 
   apply (drule (1) mall3_imp2D, erule (1) red_wf_cmd)
   apply (drule mimpD, fast, clarsimp) 
   apply (intro exI conjI, simp+)
  -- \<open> @{term "r \<notin> locked C'"} \<close>
  apply (drule_tac a="hJ" and b="Some hR \<oplus> hF" and c=hh in all3D, drule_tac a=C' and b=s' and c=hh' in all3D,
         simp add: pa_ac)
  apply (clarsimp simp add: envs_upd)
  apply (drule (1) mall3_imp2D, erule (1) red_wf_cmd)
  apply (drule mimpD, fast, clarsimp) 
  apply (subgoal_tac "pdisj h' hR", erule_tac[2] pdisj_search)
  apply (rule_tac x="padd h' hR" and y="hJ'" in ex2I, simp add: pa_ac) 
  apply (drule_tac a=hR in all_imp2D, simp_all add: hsimps)
  apply (subst assn_agrees, simp_all, fastforce)
 -- \<open> skip \<close>
 apply (clarsimp simp add: envs_def)
 apply (rule_tac x="padd h hR" in exI, simp add: pa_ac, rule safe_skip, simp, fast)
-- \<open> not user cmd \<close>
apply (clarsimp)
apply (rule conjI, clarsimp, erule aborts.cases, simp_all, clarsimp, clarsimp)
apply (frule red_properties, clarsimp)
apply (erule red.cases, simp_all, clarsimp, rename_tac C s hh C' s' hh')
apply (drule_tac a="hJ" and b="hF" and c=hh in all3D, drule_tac a=C' and b=s' and c=hh' in all3D,
       simp add: pa_ac)
apply (clarsimp simp add: envs_upd envs_removeAll2)
apply (drule (1) mall3_imp2D, erule (1) red_wf_cmd)
apply (drule mimpD, fast, clarsimp) 
apply (case_tac "r \<in> set (llocked C')", simp_all add: locked_eq envs_removeAll2 envs_upd)
 apply (intro exI conjI, simp+)
apply (subst (asm) sat_envs_expand [where r=r], simp_all add: wf_cmd_distinct_locked, 
       clarsimp simp add: pa_ac, rename_tac hR' hJ')
apply (subgoal_tac "pdisj h' hR'", erule_tac[2] pdisj_search)
apply (drule (2) all_imp2D, rule_tac x="padd h' hR'" and y=hJ' in ex2I, simp add: pa_ac envs_upd)
done

theorem rule_resource:
 "\<lbrakk> \<Gamma>(r := R) \<turnstile> {P} C {Q} ; disjoint (fvA R) (wrC C) \<rbrakk> \<Longrightarrow> 
    \<Gamma> \<turnstile> {P ** R} (Cresource r C) {Q ** R}"
by (clarsimp simp add: CSL_def, drule (1) all3_impD)
   (auto simp add: locked_eq dest!: safe_resource)

subsubsection \<open> Frame rule \<close>

text \<open> The safety of the frame rule can be seen as a special case of the parallel composition
  rule taking one thread to be the empty command. \<close>

lemma safe_frame:
 "\<lbrakk> safe n C s h J Q; 
    pdisj h hR;
    disjoint (fvA R) (wrC C);
    (s,hR) \<Turnstile> R\<rbrakk>
  \<Longrightarrow> safe n C s (padd h hR) J (Q ** R)"
apply (induct n arbitrary: C s h hR, simp, clarsimp simp add: pa_ac)
apply (rule conjI, clarify, fast)
apply (rule conjI, clarify)
 -- \<open> no aborts \<close>
 apply (drule_tac a="Some hR \<oplus> hF" in all2_impD, simp add: pa_ac, simp)
-- \<open> accesses \<close>
apply (rule conjI, erule order_trans, simp)
apply (rule conjI, erule order_trans, erule fpdom_padd)
-- \<open> step \<close>
apply (clarify, frule red_properties, clarsimp)
apply (drule_tac a="hJ" and b="Some hR \<oplus> hF" in all3D, simp add: pa_ac, drule (1) all3_impD, clarsimp)
apply (subgoal_tac "pdisj h' hR", erule_tac[2] pdisj_search)
apply (rule_tac y="hJ'" and x="padd h' hR" in ex2I, clarsimp simp add: pa_ac)
apply (drule mall4D, erule mimp4D, simp_all add: hsimps)
 apply (erule (1) disjoint_search)
apply (subst assn_agrees, simp_all, fastforce)
done

theorem rule_frame:
 "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ; disjoint (fvA R) (wrC C) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P ** R} C {Q ** R}"
by (auto simp add: CSL_def intro: safe_frame)

subsubsection \<open> Conditional critical regions \<close>

lemma safe_inwith:
  "\<lbrakk>safe n C s h \<Gamma> (Q ** \<Gamma> r); wf_cmd (Cinwith r C) \<rbrakk>
  \<Longrightarrow> safe n (Cinwith r C) s h \<Gamma> Q"
apply (induct n arbitrary: C s h, simp_all, clarify)
apply (rule conjI)
 apply (clarify, erule aborts.cases, simp_all, clarsimp)
apply (clarify, erule_tac red.cases, simp_all, clarify)
 apply (frule (1) red_wf_cmd)
 apply (drule allD, drule (1) all5_imp2D, simp_all)
 apply (simp add: envs_def list_minus_removeAll [THEN sym] locked_eq)+
 apply fast
apply (clarsimp simp add: envs_def, rename_tac hQ hJ)
apply (rule_tac x="hQ" and y="hJ" in ex2I, simp add: pa_ac, fast)
done

theorem rule_with:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj (P ** \<Gamma> r) (Apure B)} C {Q ** \<Gamma> r} \<rbrakk>
   \<Longrightarrow> \<Gamma> \<turnstile> {P} Cwith r B C {Q}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI, clarify, erule aborts.cases, simp_all)
apply (clarify, erule red.cases, simp_all, clarsimp)
apply (subgoal_tac "pdisj h hJ", erule_tac[2] pdisj_search)
apply (simp add: envs_def, rule_tac x="padd h hJ" in exI, simp add: pa_ac)
apply (rule safe_inwith, erule all3_impD, auto dest: user_cmdD)
done

subsubsection \<open> Sequential composition \<close>

lemma safe_seq:
 "\<lbrakk> safe n C s h J Q; user_cmd C2;
    \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Q \<longrightarrow> safe m C2 s' h' J R \<rbrakk>
  \<Longrightarrow> safe n (Cseq C C2) s h J R"
apply (induct n arbitrary: C s h l, simp, clarsimp)
apply (rule conjI, clarsimp)
 apply (erule aborts.cases, simp_all, clarsimp)
apply (clarsimp, erule red.cases, simp_all)
 -- \<open> Seq1 \<close>
 apply (clarify, rule_tac x="h" and y="hJ" in ex2I, simp)
-- \<open> Seq2 \<close>
apply (clarify, drule all3D, drule (2) all3_imp2D, clarsimp)
apply (drule (1) mall3_impD, rule_tac x="h'" and y="hJ'" in ex2I, simp)
done

theorem rule_seq:
  "\<lbrakk> \<Gamma> \<turnstile> {P} C1 {Q} ; \<Gamma> \<turnstile> {Q} C2 {R} \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> {P} Cseq C1 C2 {R}"
by (auto simp add: CSL_def intro!: safe_seq)

subsubsection \<open> Conditionals (if-then-else) \<close>

theorem rule_if:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj P (Apure B)} C1 {Q} ; 
     \<Gamma> \<turnstile> {Aconj P (Apure (Bnot B))} C2 {Q} \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P} Cif B C1 C2 {Q}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
apply (erule red.cases, simp_all)
apply (clarsimp, intro exI, (rule conjI, simp)+, simp)+
done

subsubsection \<open> While \<close>

lemma safe_while:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj P (Apure B)} C {P} ; (s, h) \<Turnstile> P \<rbrakk>
  \<Longrightarrow> safe n (Cwhile B C) s h \<Gamma> (Aconj P (Apure (Bnot B)))"
apply (induct n arbitrary: s h, simp, clarsimp)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
apply (erule red.cases, simp_all)
apply (clarsimp, intro exI, (rule conjI, simp)+)
apply (subgoal_tac "\<forall>m s h. m \<le> n \<and> (s, h) \<Turnstile> P \<longrightarrow> safe m (Cwhile B C) s h \<Gamma> (Aconj P (Apure (Bnot B)))")
 apply (case_tac n, simp, clarsimp)
 apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
 apply (erule red.cases, simp_all)
  apply (clarsimp, intro exI, (rule conjI, simp)+)
  apply (clarsimp simp add: CSL_def, rule safe_seq, blast, simp, clarsimp)
 apply (clarsimp, intro exI, (rule conjI, simp)+, rule safe_skip, simp)
apply (clarsimp, drule (1) mall2_impD, erule (1) safe_mon) 
done

theorem rule_while:
  "\<Gamma> \<turnstile> {Aconj P (Apure B)} C {P}
  \<Longrightarrow> \<Gamma> \<turnstile> {P} Cwhile B C {Aconj P (Apure (Bnot B))}"
by (auto simp add: CSL_def intro: safe_while)

subsubsection \<open> Local variable declaration \<close>

lemma safe_inlocal:
  "\<lbrakk> safe n C (s(x:=v)) h \<Gamma> Q ; x \<notin> fvA Q \<union> fvAs \<Gamma> \<rbrakk>
  \<Longrightarrow> safe n (Cinlocal x v C) s h \<Gamma> Q"
apply (induct n arbitrary: s h v C, simp, clarsimp)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all, clarsimp)
apply (erule red.cases, simp_all)
 apply (clarsimp, drule allD, drule (1) all5_imp2D, simp)
 apply (clarsimp, intro exI, (rule conjI, simp)+, simp)
apply (fastforce simp add: safe_skip)
done

theorem rule_local:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj P (Apure (Beq (Evar x) E))} C {Q} ; 
     x \<notin> fvA P \<union> fvA Q \<union> fvAs \<Gamma> \<union> fvE E \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P} Clocal x E C {Q}"
apply (auto simp add: CSL_def intro: safe_inlocal)
apply (case_tac n, simp_all)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
apply (erule red.cases, simp_all, clarsimp)
apply (intro exI conjI, simp_all, rule safe_inlocal, simp_all)
done

subsubsection \<open> Basic commands (Assign, Read, Write, Alloc, Free) \<close>

theorem rule_assign:
  "x \<notin> fvAs \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> {subA x E Q} Cassign x E {Q}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI, clarsimp, erule aborts.cases, simp_all)
apply (clarsimp, erule red.cases, simp_all)
apply (rule_tac x="h" in exI, rule_tac x="hJ" in exI, 
       clarsimp simp add: subA_assign) 
done

lemma ptoheap_read:
 "\<lbrakk> ptoheap (Some h \<oplus> hF) hh; h x = Some (v, k) \<rbrakk> \<Longrightarrow> hh x = Some v"
apply (case_tac hF, (simp add: ptoheap_def mypadd_def split: if_split_asm)+)
apply (drule_tac a="x" in allD, fastforce simp add: padd_def split: option.splits)
done

theorem rule_read:
  "\<lbrakk> x \<notin> fvE E \<union> fvE E' \<union> fvAs \<Gamma> \<rbrakk> \<Longrightarrow>
    \<Gamma> \<turnstile> {Apsto k E E'} Cread x E {Aconj (Apsto k E E') (Apure (Beq (Evar x) E'))}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp, intro conjI allI impI notI)
 apply (erule aborts.cases, simp_all, fastforce dest: ptoheap_read)
apply (erule red.cases, simp_all, fastforce dest: ptoheap_read)
done

lemma pdisj_upd2: "h x = Some (w, pfull) \<Longrightarrow> pdisj (h(x \<mapsto> (v, pfull))) h' = pdisj h h'"
by (simp add: pdisj_def, rule iff_allI, auto split: option.splits)
 
lemma write_helper:
 "\<lbrakk> ptoheap (Some h \<oplus> hF) hh; h x = Some (v, pfull) \<rbrakk> \<Longrightarrow> 
  ptoheap (Some (h(x\<mapsto> (w, pfull))) \<oplus> hF) (hh(x\<mapsto>w))"
apply (case_tac hF, simp_all add: ptoheap_def mypadd_def split: if_split_asm)
apply (clarsimp simp add: pdisj_upd2, simp add: pdisj_def, (drule_tac a=xa in allD)+)
apply (clarsimp simp add: pdisj_def padd_def split: option.splits)
done

theorem rule_write:
  "\<Gamma> \<turnstile> {E \<longmapsto> E0} Cwrite E E' {E \<longmapsto> E'}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp simp add: fpdom_def, intro conjI allI impI notI)
apply (erule aborts.cases, simp_all, fastforce dest: ptoheap_read)
apply (erule red.cases, simp_all, fastforce elim: write_helper)
done

lemma alloc_helper:
 "\<lbrakk>ptoheap h hh; x \<notin> dom hh\<rbrakk> \<Longrightarrow> 
  ptoheap (Some [x \<mapsto> (v, pfull)] \<oplus> h) (hh(x \<mapsto> v))"
apply (auto simp add: ptoheap_def mypadd_def pdisj_def padd_def split: option.splits)
apply (drule_tac a=xa in allD, simp)
done

theorem rule_alloc:
  "\<lbrakk> x \<notin> fvE E \<union> fvAs \<Gamma> \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {Aemp} Calloc x E {Evar x \<longmapsto> E}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp, intro conjI allI impI notI)
apply (erule aborts.cases, simp_all)
apply (erule red.cases, simp_all, fastforce elim: alloc_helper)
done

lemma free_helper:
 "\<lbrakk> ptoheap (Some h \<oplus> hF) hh; h x = Some (v, pfull) \<rbrakk> \<Longrightarrow> 
  ptoheap (Some (h(x:=None)) \<oplus> hF) (hh(x:=None))"
apply (case_tac hF, simp_all add: ptoheap_def mypadd_def split: if_split_asm)
apply (clarsimp simp add: pdisj_def, (drule_tac a=xa in allD)+)
apply (clarsimp simp add: padd_def split: option.splits)
done

theorem rule_free:
  "\<Gamma> \<turnstile> {E \<longmapsto> E0} Cdispose E {Aemp}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp simp add: fpdom_def, intro conjI allI impI notI)
 apply (erule aborts.cases, simp_all, fastforce dest: ptoheap_read)
apply (erule red.cases, simp_all, fastforce elim: free_helper dom_eqD)
done

subsubsection \<open> Simple structural rules (Conseq, Disj, Ex) \<close>

lemma safe_conseq:
 "\<lbrakk> safe n C s h \<Gamma> Q ; Q \<sqsubseteq> Q' \<rbrakk> \<Longrightarrow> safe n C s h \<Gamma> Q'"
apply (induct n arbitrary: C s h, simp, clarsimp simp add: implies_def)
apply (drule allD, drule (2) all5_imp2D, simp_all, clarsimp)
apply (drule (1) mall3_impD, rule_tac x="h'" and y="hJ'" in ex2I, simp)
done

theorem rule_conseq:
 "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ; P' \<sqsubseteq> P ; Q \<sqsubseteq> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> {P'} C {Q'}"
by (fastforce simp add: CSL_def implies_def elim!: safe_conseq)

theorem rule_disj:
 "\<lbrakk> \<Gamma> \<turnstile> {P1} C {Q1}; \<Gamma> \<turnstile> {P2} C {Q2} \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> {Adisj P1 P2} C {Adisj Q1 Q2}"
by (clarsimp simp add: CSL_def, safe)
   (rule safe_conseq, simp_all add: implies_def, drule (2) all3_impD, force)+

theorem rule_ex:
 "\<lbrakk> \<forall>n. (\<Gamma> \<turnstile> {P n} C {Q n}) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> {Aex P} C {Aex Q}"
by (clarsimp simp add: CSL_def, rule_tac Q = "Q v" in safe_conseq, 
    auto simp add: implies_def)

subsubsection \<open> Conjunction rule \<close>

lemma safe_conj:
  "\<lbrakk> safe n C s h \<Gamma> Q1; 
     safe n C s h \<Gamma> Q2;
     \<forall>r. precise (\<Gamma> r) \<rbrakk> 
  \<Longrightarrow> safe n C s h \<Gamma> (Aconj Q1 Q2)"
apply (induct n arbitrary: C s h, simp, clarsimp)
apply (drule allD, drule (2) all5_imp2D, clarsimp)+
apply (rule_tac x=h' and y=hJ' in ex2I, simp) 
apply (erule mall3_imp2D, simp_all)
apply (subgoal_tac "Some hJ' \<oplus> Some h' = Some hJ'a \<oplus> Some h'a")
 apply (subst (asm) (8 9) mypadd_def, simp split: if_split_asm)
  apply (erule_tac[2] notE, erule_tac[2] pdisj_search)
 apply (drule_tac s="a" and y="h'" and y'="h'a" in preciseD [rotated], simp_all
        add: envs_def precise_istar, fast)
apply (case_tac hF, simp add: ptoheap_def, clarsimp, rename_tac hR)
apply (drule (1) ptoD, rule_tac x="Some hR" in pa_cancel, simp add: pa_ac)
apply (rule notI, simp add: pa_ac ptoheap_def)
done

theorem rule_conj:
 "\<lbrakk> \<Gamma> \<turnstile> {P1} C {Q1}; 
    \<Gamma> \<turnstile> {P2} C {Q2}; 
    \<forall>r. precise (\<Gamma> r) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {Aconj P1 P2} C {Aconj Q1 Q2}"
by (auto simp add: CSL_def intro: safe_conj)

subsubsection \<open> Auxiliary variables \<close>

lemma safe_aux:
  "\<lbrakk> safe n C s h \<Gamma> Q; disjoint X (fvC (rem_vars X C) \<union> fvA Q \<union> fvAs \<Gamma>) \<rbrakk>
  \<Longrightarrow> safe n (rem_vars X C) s h \<Gamma> Q"
apply (induct n arbitrary: C s h, simp_all)
apply (intro conjI impI allI, clarsimp)
apply (fastforce intro: aborts_remvars)
apply (elim conjE, erule order_trans [OF accesses_remvars])
apply (clarsimp, frule red_properties, drule aux_red, simp_all)
apply (drule_tac a="Some hJ \<oplus> hF" in allD, simp add: pa_ac)
apply (clarsimp, drule allD, drule (2) all5_imp2D, clarsimp)
apply (intro exI conjI, simp+)
apply (fastforce simp add: disjoint_commute agreesC)
apply (drule (1) mall3_imp2D, fast) 
apply (erule safe_agrees, fastforce simp add: disjoint_commute agreesC)
done

text \<open> The proof rule for eliminating auxiliary variables. Note that a
  set of variables, @{term X}, is auxiliary for a command @{term C}
  iff it disjoint from @{term "fvC (rem_vars X C)"}. \<close>

theorem rule_aux:
  "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ;
     disjoint X (fvA P \<union> fvA Q \<union> fvAs \<Gamma> \<union> fvC (rem_vars X C)) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P} rem_vars X C {Q}"
by (auto simp add: CSL_def safe_aux disjoint_commute)

end