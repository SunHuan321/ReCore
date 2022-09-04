theory CSLsound
imports Main VHelper Lang
begin

text {* This file contains a soundness proof for CSL (with multiple resources)
  as presented by O'Hearn and Brookes including the data-race freedom property
  of CSL.  For simplicity, there is a slight difference regarding variable
  side-conditions: we do not allow resource-owned variables. *}

text {* (Adapted to Isabelle 2016-1 by Qin Yu and James Brotherston) *}

subsection {* Separation logic assertions *}          

text {* A deep embedding of separation logic assertions. *}

datatype assn = 
    Aemp                                           (*r Empty heap *)
  | Apointsto exp exp    (infixl "\<longmapsto>" 200)        (*r Singleton heap *)
  | Astar assn assn      (infixl "**" 100)         (*r Separating conjunction *)
  | Awand assn assn                                (*r Separating implication *)
  | Apure bexp                                     (*r Pure assertion *)
  | Aconj assn assn                                (*r Conjunction *)
  | Adisj assn assn                                (*r Disjunction *)
  | Aex "(nat \<Rightarrow> assn)"                            (*r Existential quantification *)

text {* Separating conjunction of a finite list of assertions is 
  just a derived assertion. *}

primrec 
  Aistar :: "assn list \<Rightarrow> assn"
where
  "Aistar [] = Aemp"
| "Aistar (P # Ps) = Astar P (Aistar Ps)"

primrec
  sat :: "state \<Rightarrow> assn \<Rightarrow> bool" (infixl "\<Turnstile>" 60)
where
  "(\<sigma> \<Turnstile> Aemp)      = (snd \<sigma> = Map.empty)" 
| "(\<sigma> \<Turnstile> E \<longmapsto> E')  = (dom (snd \<sigma>) = { edenot E (fst \<sigma>) } \<and> (snd \<sigma>) (edenot E (fst \<sigma>)) = Some (edenot E' (fst \<sigma>)))" 
| "(\<sigma> \<Turnstile> P ** Q)    = (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> P \<and> (fst \<sigma>, h2) \<Turnstile> Q \<and> snd \<sigma> = (h1 ++ h2) \<and> disjoint (dom h1) (dom h2))" 
| "(\<sigma> \<Turnstile> Awand P Q) = (\<forall>h. disjoint (dom (snd \<sigma>)) (dom h) \<and> (fst \<sigma>, h) \<Turnstile> P \<longrightarrow> (fst \<sigma>, snd \<sigma> ++ h) \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Apure B)   = bdenot B (fst \<sigma>)" 
| "(\<sigma> \<Turnstile> Aconj P Q) = (\<sigma> \<Turnstile> P \<and> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Adisj P Q) = (\<sigma> \<Turnstile> P \<or> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Aex PP)    = (\<exists>v. \<sigma> \<Turnstile> PP v)" 

definition 
  implies :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixl "\<sqsubseteq>" 60)
where
  "P \<sqsubseteq> Q \<equiv> (\<forall>\<sigma>. \<sigma> \<Turnstile> P \<longrightarrow> \<sigma> \<Turnstile> Q)"

lemma sat_istar_map_expand:
  "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<Turnstile> Aistar (map f l)
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> f r
              \<and> (fst \<sigma>, h2) \<Turnstile> Aistar (map f (remove1 r l))
              \<and> snd \<sigma> = (h1 ++ h2)
              \<and> disjoint (dom h1) (dom h2))"
apply (case_tac \<sigma>, rename_tac s h, clarify)
apply (induction l arbitrary: \<sigma>, auto)
apply (intro exI conjI, (simp add: hsimps)+)+
done

subsubsection {* Precision *}

text {* We say that an assertion is precise if for any given heap, there is at
most one subheap that satisfies the formula. (The formal definition below says 
that if there are two such subheaps, they must be equal.) *}

definition
  precise :: "assn \<Rightarrow> bool"
where
  "precise P \<equiv> \<forall>h1 h2 h1' h2' s. disjoint (dom h1) (dom h2) \<and> disjoint (dom h1') (dom h2')
                   \<and> h1 ++ h2 = h1' ++ h2' \<and> (s, h1) \<Turnstile> P \<and> (s, h1') \<Turnstile> P 
               \<longrightarrow> h1 = h1'"

text {* A direct consequence of the definition that is more useful in
Isabelle, because unfolding the definition slows down Isabelle's simplifier
dramatically. *}

lemma preciseD:
  "\<lbrakk> precise P; (s, x) \<Turnstile> P; (s, x') \<Turnstile> P; x ++ y = x' ++ y'; 
     disjoint (dom x) (dom y); disjoint (dom x') (dom y') \<rbrakk> \<Longrightarrow>
    x = x' \<and> y = y'"
unfolding precise_def
by (drule all5_impD, (erule conjI)+, simp_all, rule map_add_cancel)
   (subst (1 2) map_add_comm, auto simp add: disjoint_def)

text {* The separating conjunction of precise assertions is precise: *}

lemma precise_istar:
  "\<forall>x \<in> set l. precise x \<Longrightarrow> precise (Aistar l)"
apply (induct l, simp_all (no_asm) add: precise_def)
apply (clarsimp simp add: map_add_assoc [THEN sym])
apply (drule (3) preciseD, simp_all, clarsimp?)+
done

subsubsection {* Auxiliary definition for resource environments *}

definition
  envs :: "('a \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> assn"
where
  "envs \<Gamma> l l' \<equiv> Aistar (map \<Gamma> (list_minus l l'))"

lemma sat_envs_expand:
  "\<lbrakk> r \<in> set l; r \<notin> set l'; distinct l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<Turnstile> envs \<Gamma> l l' 
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> \<Gamma> r 
              \<and> (fst \<sigma>, h2) \<Turnstile> envs \<Gamma> (removeAll r l) l'
              \<and> snd \<sigma> = h1 ++ h2 \<and> disjoint (dom h1) (dom h2))" 
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

subsubsection {* Free variables, substitutions *}

primrec
  fvA :: "assn \<Rightarrow> var set"
where
  "fvA (Aemp)      = {}"
| "fvA (Apure B)   = fvB B"
| "fvA (e1 \<longmapsto> e2) = (fvE e1 \<union> fvE e2)"
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
| "subA x E (e1 \<longmapsto> e2) = (subE x E e1 \<longmapsto> subE x E e2)"
| "subA x E (P ** Q)    = (subA x E P ** subA x E Q)"
| "subA x E (Awand P Q) = Awand (subA x E P) (subA x E Q)"
| "subA x E (Aconj P Q) = Aconj (subA x E P) (subA x E Q)"
| "subA x E (Adisj P Q) = Adisj (subA x E P) (subA x E Q)"
| "subA x E (Aex PP)    = Aex (\<lambda>n. subA x E (PP n))"

lemma subA_assign:
 "(s,h) \<Turnstile> subA x E P \<longleftrightarrow> (s(x := edenot E s), h) \<Turnstile> P"
by (induct P arbitrary: h, simp_all add: subE_assign subB_assign fun_upd_def)

lemma fvA_istar[simp]: "fvA (Aistar Ps) = (\<Union>P \<in> set Ps. fvA P)"
by (induct Ps, simp_all)

text {* Proposition 4.2 for assertions *}

lemma assn_agrees: "agrees (fvA P) s s' \<Longrightarrow> (s, h) \<Turnstile> P \<longleftrightarrow> (s', h) \<Turnstile> P"
apply (induct P arbitrary: h, simp_all add: bexp_agrees)
apply (clarsimp, (subst exp_agrees, simp_all)+ )
apply (rule iff_exI, simp add: agrees_def)
done

text {* Corollaries of Proposition 4.2, useful for automation. *}

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

subsection {* Meaning of CSL judgments *}

text {* Definition 5.1: Configuration safety. *}

primrec
  safe :: "nat \<Rightarrow> cmd \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "safe 0       C s h \<Gamma> Q = True"
| "safe (Suc n) C s h \<Gamma> Q = (
(* Condition (i) *)
            (C = Cskip \<longrightarrow> (s, h) \<Turnstile> Q)
(* Condition (ii) *)
          \<and> (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> aborts C (s, h ++ hF))
(* Condition (iii) *)
          \<and> accesses C s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>hJ hF C' \<sigma>'.
                  red C (s,h ++ hJ ++ hF) C' \<sigma>'
                 \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (llocked C') (llocked C)
                 \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
                 \<longrightarrow> (\<exists>h' hJ'.
                         snd \<sigma>' = h' ++ hJ' ++ hF 
                       \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
                       \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (llocked C) (llocked C')
                       \<and> safe n C' (fst \<sigma>') h' \<Gamma> Q)))"

text {* The predicate @{text "safe n C s h \<Gamma> Q"} says that the command @{text C} and the logical state
  @{text "(s, h)"} are safe with respect to the resource environment @{text \<Gamma>} and the 
  postcondition @{text Q} for @{text n} execution steps. 
  Intuitively, any configuration is safe for zero steps.
  For @{text "n + 1"} steps, it must 
  (i) satisfy the postcondition if it is a terminal configuration,
  (ii) not abort, 
  (iii) access memory only inside its footprint, and 
  (iv) after any step it does, re-establish the resource invariant and be safe for 
  another @{text n} steps. *}

text {* Definition 5.2: The meaning of CSL judgements. *}

definition
  CSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> cmd \<Rightarrow> assn \<Rightarrow> bool"
  ("_ \<turnstile> { _ } _ { _ }")
where
  "\<Gamma> \<turnstile> {P} C {Q} \<equiv> (user_cmd C \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> safe n C s h \<Gamma> Q))" 

subsubsection {* Basic properties of Definition 5.1 *}

text {* Proposition 4.3: Monotonicity with respect to the step number. *}
lemma safe_mon:
  "\<lbrakk> safe n C s h J Q; m \<le> n \<rbrakk> \<Longrightarrow> safe m C s h J Q"
apply (induct m arbitrary: C s n h l, simp) 
apply (case_tac n, clarify)
apply (simp only: safe.simps, clarsimp)
apply (drule all5D, drule (2) imp3D, simp, clarsimp)
apply (rule_tac x="h'" in exI, rule_tac x="hJ'" in exI, simp)
done

text {* Proposition 4.4: Safety depends only the free variables
        of @{term "C"}, @{term "Q"}, and @{term "\<Gamma>"}. *}
                                                      
lemma safe_agrees: 
  "\<lbrakk> safe n C s h \<Gamma> Q ; 
     agrees (fvC C \<union> fvA Q \<union> fvAs \<Gamma>) s s' \<rbrakk>
   \<Longrightarrow> safe n C s' h \<Gamma> Q"
apply (induct n arbitrary: C s s' h bl, simp, simp only: safe.simps, clarify)
apply (rule conjI, clarsimp, subst assn_agrees, subst agreesC, assumption+)
apply (rule conjI, clarsimp)
 apply (drule_tac aborts_agrees, simp, fast, simp, simp)
apply (rule conjI, subst (asm) accesses_agrees, simp_all)
apply (clarify, drule_tac X="fvC C \<union> fvAs \<Gamma> \<union> fvA Q" in red_agrees, 
       simp (no_asm), fast, simp (no_asm), fast, clarify)
apply (drule (1) all5_impD, clarsimp)
apply (drule impD, erule assns_agreesE, simp add: agreesC, clarify)
apply (rule_tac x="h'" and y="hJ'" in ex2I, simp add: hsimps)
apply (rule conjI, erule assns_agreesE, subst agreesC, assumption)
apply (erule (1) mall4_imp2D, simp add: agreesC)
apply (drule red_properties, auto)
done

subsection {* Soundness of the proof rules *}

subsubsection {* Skip *}

lemma safe_skip[intro!]:
  "(s,h) \<Turnstile> Q \<Longrightarrow> safe n Cskip s h J Q"
by (induct n, simp_all)

theorem rule_skip: 
  "\<Gamma> \<turnstile> {P} Cskip {P}"
by (auto simp add: CSL_def)

subsubsection {* Parallel composition *}

lemma safe_par:
 "\<lbrakk> safe n C1 s h1 J Q1; safe n C2 s h2 J Q2;
    wf_cmd (Cpar C1 C2);
    disjoint (dom h1) (dom h2);
    disjoint (fvC C1 \<union> fvA Q1 \<union> fvAs J) (wrC C2);
    disjoint (fvC C2 \<union> fvA Q2 \<union> fvAs J) (wrC C1)\<rbrakk>
  \<Longrightarrow> safe n (Cpar C1 C2) s (h1 ++ h2) J (Q1 ** Q2)"
apply (induct n arbitrary: C1 C2 s h1 h2 bl1 bl2, simp, clarsimp)
apply (rule conjI, clarify)
(*no aborts *)
 apply (erule aborts.cases, simp_all add: hsimps)
    apply (clarify, drule_tac a="h2 ++ hF" in all_impD, simp_all add: hsimps)
   apply (clarify, drule_tac allD, drule_tac a="h1 ++ hF" in all_impD, simp_all add: hsimps)
(*no races *)
 apply (clarsimp, erule notE, erule disjoint_search [rotated], erule disjoint_search,
        erule order_trans [OF writes_accesses])+
(*accesses *)
apply (rule conjI, erule order_trans, simp)+
(* step *)
 apply (clarsimp, erule red_par_cases) 
(* C1 does a step *)
  apply (clarify, drule_tac a="hJ" and b="h2 ++ hF" in all2D, drule all3_impD, 
         simp_all add: hsimps envs_app locked_eq, clarsimp)
  apply (rule_tac x="h' ++ h2" in exI, rule_tac x="hJ'" in exI, simp add: hsimps)
  apply (frule (1) red_wf_cmd, drule red_properties, clarsimp)
  apply (drule_tac a=C1' and b=C2 in mall2D, simp add: hsimps)
  apply (subst map_add_commute, simp add: hsimps)
  apply (drule mall3_imp2D, erule_tac[3] mimp3D, simp_all add: hsimps)
  apply (rule_tac s="s" in safe_agrees)
       apply (rule_tac n="Suc n" in safe_mon, simp add: hsimps, simp)
  apply (fastforce simp add: agreesC disjoint_commute)
  apply (intro conjI | erule (1) disjoint_search)+
(* C2 does a step *)
  apply (clarify, drule_tac a="hJ" and b="h1 ++ hF" in all2D, drule all3_imp2D, 
         simp_all add: hsimps envs_app, clarsimp)
  apply (rule_tac x="h1 ++ h'" in exI, rule_tac x="hJ'" in exI, simp add: hsimps)
  apply (frule (1) red_wf_cmd, drule red_properties, clarsimp)
  apply (drule_tac a=C1 and b=C2' in mall2D, simp add: hsimps)
  apply (drule mall3_imp2D, erule_tac[3] mimp3D, simp_all add: hsimps)
  apply (rule_tac s="s" in safe_agrees)
   apply (rule_tac n="Suc n" in safe_mon, simp add: hsimps, simp)
  apply (subst agreesC, fastforce, fastforce, fastforce)
(* Par skip skip *)
  apply (clarify)
  apply (rule_tac x="h1 ++ h2" in exI, rule_tac x="hJ" in exI, simp add: hsimps)
  apply (rule_tac safe_skip, simp, (rule exI, erule conjI)+, simp)
done

theorem rule_par:
 "\<lbrakk> \<Gamma> \<turnstile> {P1} C1 {Q1} ; \<Gamma> \<turnstile> {P2} C2 {Q2};
    disjoint (fvC C1 \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrC C2);
    disjoint (fvC C2 \<union> fvA Q2 \<union> fvAs \<Gamma>) (wrC C1) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P1 ** P2} (Cpar C1 C2) {Q1 ** Q2}"
by (auto simp add: CSL_def intro!: safe_par)

subsubsection {* Resource declaration *}

lemma safe_resource:
 "\<lbrakk> safe n C s h (\<Gamma>(r := R)) Q; wf_cmd C; disjoint (fvA R) (wrC C) \<rbrakk> \<Longrightarrow>
     (\<forall>hR. r \<notin> locked C \<longrightarrow> disjoint (dom h) (dom hR) \<longrightarrow> (s,hR) \<Turnstile> R \<longrightarrow> safe n (Cresource r C) s (h ++ hR) \<Gamma> (Q ** R))
   \<and> (r \<in> locked C \<longrightarrow> safe n (Cresource r C) s h \<Gamma> (Q ** R))"
apply (induct n arbitrary: C s h, simp, clarsimp)
apply (rule conjI, clarify)
 apply (rule conjI, clarify)
(*no aborts *)
  apply (erule aborts.cases, simp_all, clarsimp)
  apply (drule_tac a="hR ++ hF" in all_impD, simp, simp add: hsimps)
(* accesses *)
 apply (rule conjI, erule order_trans, simp)
(* step *)
 apply (clarify, frule red_properties, clarsimp)
 apply (erule red.cases, simp_all, clarsimp, rename_tac C s C' s' hh)
(* normal step *)
  apply (case_tac "r \<in> set (llocked C')", simp_all add: locked_eq)
   apply (drule_tac a="hJ ++ hR" and b="hF" and c=C' and d=s' and e=hh in all5D, simp add: hsimps)
   apply (drule impD, subst sat_envs_expand [where r=r], simp_all)
     apply (rule wf_cmd_distinct_locked, erule (1) red_wf_cmd)
    apply (intro exI conjI, simp, simp_all add: envs_upd)
   apply (clarsimp simp add: envs_removeAll_irr) 
   apply (drule (1) mall3_imp2D, erule (1) red_wf_cmd)
   apply (drule mimpD, fast, clarsimp) 
   apply (intro exI conjI, simp+)
(* @{term "r \<notin> locked C'"} *)
  apply (drule_tac a="hJ" and b="hR ++ hF" and c=C' and d=s' and e=hh in all5D, simp add: hsimps)
  apply (clarsimp simp add: envs_upd)
  apply (drule (1) mall3_imp2D, erule (1) red_wf_cmd)
  apply (drule mimpD, fast, clarsimp) 
  apply (rule_tac x="h' ++ hR" and y="hJ'" in ex2I, simp add: hsimps) 
  apply (drule_tac a=hR in all_imp2D, simp_all add: hsimps)
  apply (subst assn_agrees, simp_all, fastforce)
 (* skip *)
 apply (clarsimp simp add: envs_def)
 apply (rule_tac x="h ++ hR" in exI, simp add: hsimps, rule safe_skip, simp, fast)
(* not user cmd *)
apply (clarsimp)
apply (rule conjI, clarsimp, erule aborts.cases, simp_all, clarsimp, clarsimp)
apply (frule red_properties, clarsimp)
apply (erule red.cases, simp_all, clarsimp, rename_tac C s C' s' hh)
apply (drule_tac a="hJ" and b="hF" and c=C' and d=s' and e=hh in all5D, simp add: hsimps)
apply (clarsimp simp add: envs_upd envs_removeAll2)
apply (drule (1) mall3_imp2D, erule (1) red_wf_cmd)
apply (drule mimpD, fast, clarsimp) 
apply (case_tac "r \<in> set (llocked C')", simp_all add: locked_eq envs_removeAll2 envs_upd)
 apply (intro exI conjI, simp+)
apply (subst (asm) sat_envs_expand [where r=r], simp_all add: wf_cmd_distinct_locked, 
       clarsimp, rename_tac hR' hJ')
apply (drule (2) all_imp2D, rule_tac x="h' ++ hR'" and y=hJ' in ex2I, simp add: hsimps envs_upd)
done

theorem rule_resource:
 "\<lbrakk> \<Gamma>(r := R) \<turnstile> {P} C {Q} ; disjoint (fvA R) (wrC C) \<rbrakk> \<Longrightarrow> 
    \<Gamma> \<turnstile> {P ** R} (Cresource r C) {Q ** R}"
by (clarsimp simp add: CSL_def, drule (1) all3_impD)
   (auto simp add: locked_eq dest!: safe_resource)

subsubsection {* Frame rule *}

text {* The safety of the frame rule can be seen as a special case of the parallel composition
  rule taking one thread to be the empty command. *}

lemma safe_frame:
 "\<lbrakk> safe n C s h J Q; 
    disjoint (dom h) (dom hR);
    disjoint (fvA R) (wrC C);
    (s,hR) \<Turnstile> R\<rbrakk>
  \<Longrightarrow> safe n C s (h ++ hR) J (Q ** R)"
apply (induct n arbitrary: C s h hR, simp, clarsimp)
apply (rule conjI, clarify, fast)
apply (rule conjI, clarify)
 (* no aborts *)
 apply (drule_tac a="hR ++ hF" in all_impD, simp, simp add: hsimps)
(* accesses *)
apply (rule conjI, erule order_trans, simp)
(* step *)
apply (clarify, frule red_properties, clarsimp)
apply (drule_tac a="hJ" and b="hR ++ hF" in all3D, simp add: hsimps, drule (1) all2_impD, clarsimp)
apply (rule_tac y="hJ'" and x="h' ++ hR" in ex2I, clarsimp simp add: hsimps)
apply (subst map_add_commute, simp add: hsimps)
apply (drule mall4D, erule mimp4D, simp_all add: hsimps)
 apply (erule (1) disjoint_search)
apply (subst assn_agrees, simp_all, fastforce)
done

theorem rule_frame:
 "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ; disjoint (fvA R) (wrC C) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P ** R} C {Q ** R}"
by (auto simp add: CSL_def intro: safe_frame)

subsubsection {* Conditional critical regions *}

lemma safe_inwith:
  "\<lbrakk>safe n C s h \<Gamma> (Q ** \<Gamma> r); wf_cmd (Cinwith r C) \<rbrakk>
  \<Longrightarrow> safe n (Cinwith r C) s h \<Gamma> Q"
apply (induct n arbitrary: C s h, simp_all, clarify)
apply (rule conjI)
 apply (clarify, erule aborts.cases, simp_all, clarsimp)
apply (clarify, erule_tac red.cases, simp_all, clarify)
 apply (frule (1) red_wf_cmd)
 apply (drule (1) all5_imp2D, simp_all)
 apply (simp add: envs_def list_minus_removeAll [THEN sym] locked_eq)+
 apply fast
apply (clarsimp simp add: envs_def, rename_tac hQ hJ)
apply (rule_tac x="hQ" and y="hJ" in ex2I, simp add: hsimps, fast)
done

theorem rule_with:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj (P ** \<Gamma> r) (Apure B)} C {Q ** \<Gamma> r} \<rbrakk>
   \<Longrightarrow> \<Gamma> \<turnstile> {P} Cwith r B C {Q}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI, clarify, erule aborts.cases, simp_all)
apply (clarify, erule red.cases, simp_all, clarsimp)
apply (simp add: envs_def, rule_tac x="h ++ hJ" in exI, simp)
apply (rule safe_inwith, erule all3_impD, auto dest: user_cmdD)
done

subsubsection {* Sequential composition *}

lemma safe_seq:
 "\<lbrakk> safe n C s h J Q; user_cmd C2;
    \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Q \<longrightarrow> safe m C2 s' h' J R \<rbrakk>
  \<Longrightarrow> safe n (Cseq C C2) s h J R"
apply (induct n arbitrary: C s h l, simp, clarsimp)
apply (rule conjI, clarsimp)
 apply (erule aborts.cases, simp_all, clarsimp)
apply (clarsimp, erule red.cases, simp_all)
 (* Seq1 *)
 apply (clarify, rule_tac x="h" and y="hJ" in ex2I, simp)
(* Seq2 *)
apply (clarify, drule (1) all5_impD, clarsimp) 
apply (drule (1) mall3_impD, rule_tac x="h'" and y="hJ'" in ex2I, simp)
done

theorem rule_seq:
  "\<lbrakk> \<Gamma> \<turnstile> {P} C1 {Q} ; \<Gamma> \<turnstile> {Q} C2 {R} \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> {P} Cseq C1 C2 {R}"
by (auto simp add: CSL_def intro!: safe_seq)

subsubsection {* Conditionals (if-then-else) *}

theorem rule_if:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj P (Apure B)} C1 {Q} ; 
     \<Gamma> \<turnstile> {Aconj P (Apure (Bnot B))} C2 {Q} \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P} Cif B C1 C2 {Q}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
apply (elim conjE)
apply (erule red.cases, simp_all)
apply (clarsimp, intro exI, (rule conjI, simp)+, simp)+
done

subsubsection {* While *}

lemma safe_while:
  "\<lbrakk> \<Gamma> \<turnstile> {Aconj P (Apure B)} C {P} ; (s, h) \<Turnstile> P \<rbrakk>
  \<Longrightarrow> safe n (Cwhile B C) s h \<Gamma> (Aconj P (Apure (Bnot B)))"
apply (induct n arbitrary: s h, simp, clarsimp)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
apply (elim conjE, erule red.cases, simp_all)
apply (clarsimp, intro exI, (rule conjI, simp)+)
apply (subgoal_tac "\<forall>m s h. m \<le> n \<and> (s, h) \<Turnstile> P \<longrightarrow> safe m (Cwhile B C) s h \<Gamma> (Aconj P (Apure (Bnot B)))")
 apply (case_tac n, simp, clarsimp)
 apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
 apply (elim conjE, erule red.cases, simp_all)
  apply (clarsimp, intro exI, (rule conjI, simp)+)
  apply (clarsimp simp add: CSL_def, rule safe_seq, blast, simp, clarsimp)
 apply (clarsimp, intro exI, (rule conjI, simp)+, rule safe_skip, simp)
apply (clarsimp, drule (1) mall2_impD, erule (1) safe_mon) 
done

theorem rule_while:
  "\<Gamma> \<turnstile> {Aconj P (Apure B)} C {P}
  \<Longrightarrow> \<Gamma> \<turnstile> {P} Cwhile B C {Aconj P (Apure (Bnot B))}"
by (auto simp add: CSL_def intro: safe_while)

subsubsection {* Local variable declaration *}

lemma safe_inlocal:
  "\<lbrakk> safe n C (s(x:=v)) h \<Gamma> Q ; x \<notin> fvA Q \<union> fvAs \<Gamma> \<rbrakk>
  \<Longrightarrow> safe n (Cinlocal x v C) s h \<Gamma> Q"
apply (induct n arbitrary: s h v C, simp, clarsimp)
apply (intro conjI allI impI notI, erule aborts.cases, simp_all, clarsimp)
apply (elim conjE, erule red.cases, simp_all)
 apply (clarsimp, drule (1) all5_imp2D, simp)
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
apply (elim conjE, erule red.cases, simp_all, clarsimp)
apply (intro exI conjI, simp_all, rule safe_inlocal, simp_all)
done

subsubsection {* Basic commands (Assign, Read, Write, Alloc, Free) *}

theorem rule_assign:
  "x \<notin> fvAs \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> {subA x E Q} Cassign x E {Q}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI, clarsimp, erule aborts.cases, simp_all)
apply (clarsimp, erule red.cases, simp_all)
apply (rule_tac x="h" in exI, rule_tac x="hJ" in exI, 
       clarsimp simp add: subA_assign) 
done

theorem rule_read:
  "\<lbrakk> x \<notin> fvE E \<union> fvE E' \<union> fvAs \<Gamma> \<rbrakk> \<Longrightarrow>
    \<Gamma> \<turnstile> {E \<longmapsto> E'} Cread x E {Aconj (E \<longmapsto> E') (Apure (Beq (Evar x) E'))}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI)
 apply (clarsimp, erule aborts.cases, simp_all, clarsimp simp add: dom_def)
apply (clarify, erule red.cases, simp_all, elim exE conjE, hypsubst)
apply (rule_tac x="h" in exI, rule_tac x="hJ" in exI, clarsimp)
apply (simp add: disjoint_def, clarsimp, elim disjE, clarsimp+)
done

theorem rule_write:
  "\<Gamma> \<turnstile> {E \<longmapsto> E0} Cwrite E E' {E \<longmapsto> E'}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI)
 apply (clarsimp, erule aborts.cases, simp_all, clarsimp simp add: dom_def)
apply (clarify, erule red.cases, simp_all, clarsimp)
apply (rule_tac x="h(edenot E sa \<mapsto> edenot E' sa)" in exI, rule_tac x="hJ" in exI, simp)
apply (rule conjI [rotated], clarsimp) 
apply (subst map_add_assoc [THEN sym], subst map_add_commute, simp add: hsimps)
apply (subst map_add_upd [THEN sym], simp add: hsimps del: map_add_upd)
done

theorem rule_alloc:
  "\<lbrakk> x \<notin> fvE E \<union> fvAs \<Gamma> \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {Aemp} Calloc x E {Evar x \<longmapsto> E}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI, clarsimp, erule aborts.cases, simp_all)
apply (clarify)
apply (erule red.cases, simp_all)
apply (rule_tac x="Map.empty(v \<mapsto> edenot E s)" in exI, rule_tac x="hJ" in exI, simp)
apply (elim conjE, hypsubst, simp, elim conjE)
apply (clarsimp simp add: map_add_upd_left disjoint_def)
done

theorem rule_free:
  "\<Gamma> \<turnstile> {E \<longmapsto> E0} Cdispose E {Aemp}"
apply (clarsimp simp add: CSL_def)
apply (case_tac n, simp, clarsimp)
apply (rule conjI)
 apply (clarsimp, erule aborts.cases, simp_all, clarsimp simp add: dom_def)
apply (clarify, erule red.cases, simp_all, clarsimp)
apply (rule_tac x="h(edenot E sa := None)" in exI, rule_tac x="hJ" in exI, simp)
apply (clarsimp, rule ext, simp, clarify, erule dom_eqD, simp)
done

subsubsection {* Simple structural rules (Conseq, Disj, Ex) *}

lemma safe_conseq:
 "\<lbrakk> safe n C s h \<Gamma> Q ; Q \<sqsubseteq> Q' \<rbrakk> \<Longrightarrow> safe n C s h \<Gamma> Q'"
apply (induct n arbitrary: C s h, simp, clarsimp simp add: implies_def)
apply (drule (2) all5_imp2D, simp_all, clarsimp)
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

subsubsection {* Conjunction rule *}

lemma safe_conj:
  "\<lbrakk> safe n C s h \<Gamma> Q1; 
     safe n C s h \<Gamma> Q2;
     \<forall>r. precise (\<Gamma> r) \<rbrakk> 
  \<Longrightarrow> safe n C s h \<Gamma> (Aconj Q1 Q2)"
apply (induct n arbitrary: C s h, simp, clarsimp)
apply (drule (1) all5_impD, clarsimp)+
apply (rule_tac x=h' and y=hJ' in ex2I, simp) 
apply (erule mall3_imp2D, simp_all, drule map_add_cancel, simp_all)
apply (drule_tac s="a" and y="h'" and y'="h'a" in preciseD [rotated], simp_all add: hsimps)
apply (auto simp add: envs_def precise_istar)
done

theorem rule_conj:
 "\<lbrakk> \<Gamma> \<turnstile> {P1} C {Q1}; 
    \<Gamma> \<turnstile> {P2} C {Q2}; 
    \<forall>r. precise (\<Gamma> r) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {Aconj P1 P2} C {Aconj Q1 Q2}"
by (auto simp add: CSL_def intro: safe_conj)

subsubsection {* Auxiliary variables *}

lemma safe_aux:
  "\<lbrakk> safe n C s h \<Gamma> Q; disjoint X (fvC (rem_vars X C) \<union> fvA Q \<union> fvAs \<Gamma>) \<rbrakk>
  \<Longrightarrow> safe n (rem_vars X C) s h \<Gamma> Q"
apply (induct n arbitrary: C s h, simp_all)
apply (intro conjI impI allI, clarsimp)
apply (fastforce intro: aborts_remvars)
apply (elim conjE, erule order_trans [OF accesses_remvars])
apply (clarsimp, frule red_properties, drule aux_red, simp_all)
apply (drule_tac a="hJ ++ hF" in allD, simp add: hsimps)
apply (clarsimp, drule (2) all5_imp2D, clarsimp)
apply (intro exI conjI, simp+)
apply (fastforce simp add: disjoint_commute agreesC)
apply (drule (1) mall3_imp2D, fast) 
apply (erule safe_agrees, fastforce simp add: disjoint_commute agreesC)
done

text {* The proof rule for eliminating auxiliary variables. Note that a
  set of variables, @{term X}, is auxiliary for a command @{term C}
  iff it disjoint from @{term "fvC (rem_vars X C)"}. *}

theorem rule_aux:
  "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ;
     disjoint X (fvA P \<union> fvA Q \<union> fvAs \<Gamma> \<union> fvC (rem_vars X C)) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {P} rem_vars X C {Q}"
by (auto simp add: CSL_def safe_aux disjoint_commute)


subsection {* Alternative definition of configuration safety *}

text {* Here is an alternative definition of safety monotonicity that does not 
  quantify over the frame @{term hF}. *}

primrec
  safe_weak :: "nat \<Rightarrow> cmd \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "safe_weak 0       C s h \<Gamma> Q = True"
| "safe_weak (Suc n) C s h \<Gamma> Q = (
(* Condition (i) *)
            (C = Cskip \<longrightarrow> (s, h) \<Turnstile> Q)
(* Condition (ii) *)
          \<and> \<not> aborts C (s, h)
(* Condition (iii) *)
          \<and> accesses C s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>hJ C' \<sigma>'.
                  red C (s,h ++ hJ) C' \<sigma>'
                 \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (llocked C') (llocked C)
                 \<longrightarrow> (disjoint (dom h) (dom hJ))
                 \<longrightarrow> (\<exists>h' hJ'.
                         snd \<sigma>' = h' ++ hJ'
                       \<and> disjoint (dom h') (dom hJ')
                       \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (llocked C) (llocked C')
                       \<and> safe_weak n C' (fst \<sigma>') h' \<Gamma> Q)))"

text {* It is easy to show that the alternative definition is weaker
  than the one with the quantification: *}

lemma safe_weakI:
  "safe n C s h \<Gamma> Q \<Longrightarrow> safe_weak n C s h \<Gamma> Q"
  apply (induct n arbitrary: C s h, simp, clarsimp)
  apply (rule conjI)
  apply (metis disjoint_simps(2) dom_empty map_add_empty)
  apply (clarify)
  by (metis disjoint_simps(2) dom_empty map_add_empty)


text {* If, however, the operational semantics satisfies the safety
monotonicity and frame properties (which it does), then the two
definitions are equivalent.  We first prove that the operational
semantics satisfies these two properties, and then using these
properties, we show that the alternative definition of configuration
safety implies the original one. *}

text {* [A] Safety monotonicity: *}

lemma safety_monotonicity_helper[rule_format]: 
  "aborts C \<sigma>  \<Longrightarrow> \<forall>s h hF. \<sigma> = (s, h ++ hF) \<longrightarrow> disjoint (dom h) (dom hF) \<longrightarrow> aborts C (s, h)"
by (erule aborts.induct, auto)

lemma safety_monotonicity: 
  "\<lbrakk> aborts C (s, h ++ hF); disjoint (dom h) (dom hF) \<rbrakk> \<Longrightarrow> aborts C (s, h)"
by (erule safety_monotonicity_helper, simp_all)

text {* [B] Frame property: *}

lemma frame_property_helper[rule_format]: 
  "red C \<sigma>  C' \<sigma>' \<Longrightarrow> \<forall>s h hF s' h''. \<sigma> = (s, h ++ hF) \<longrightarrow> \<sigma>' = (s', h'')
   \<longrightarrow> disjoint (dom h) (dom hF)
   \<longrightarrow> \<not> aborts C (s, h)
   \<longrightarrow> (\<exists>h'. red C (s, h) C' (s', h') \<and> h'' = h' ++ hF \<and> disjoint (dom h') (dom hF))"
apply (erule red.induct, fastforce+)
(* Read *)
apply (clarsimp, rename_tac h hF)
apply (case_tac "h (edenot E s)", erule notE, fastforce)
apply (intro exI conjI red_Read, fast+, simp_all)
apply (fastforce simp add: disjoint_def)
(* Write *)
apply (clarsimp, rename_tac h hF)
apply (case_tac "h (edenot E s)", erule notE, fastforce)
apply (rule_tac x="h(edenot E s \<mapsto> edenot E' s)" in exI, intro conjI, fast)
 apply (rule map_add_upd_left [THEN sym], fastforce simp add: disjoint_def)
apply (fastforce simp add: disjoint_def)
(* Alloc *)
apply (clarsimp, rename_tac h hF)
apply (rule_tac x="h(v \<mapsto> edenot E s)" in exI, intro conjI)
  apply (rule_tac v=v in red_Alloc, fast+)
 apply (rule map_add_upd_left [THEN sym], fastforce simp add: disjoint_def)
apply (fastforce simp add: disjoint_def)
(* Dispose *)
apply (clarsimp, rename_tac h hF)
apply (case_tac "h (edenot E s)", erule notE, fastforce)
  apply (rule_tac x="h(edenot E s := None)" in exI, intro conjI, fast)
 apply (subgoal_tac "hF(edenot E s := None) = hF", simp, rule ext, fastforce simp add: disjoint_def)
apply (fastforce simp add: disjoint_def)
done

lemma frame_property: 
  "\<lbrakk> red C (s, h ++ hF) C' (s', h''); disjoint (dom h) (dom hF); \<not> aborts C (s, h) \<rbrakk>
  \<Longrightarrow> \<exists>h'. red C (s, h) C' (s', h') \<and> h'' = h' ++ hF \<and> disjoint (dom h') (dom hF)"
by (erule frame_property_helper, simp_all)

text {* Finally, using safety monotonicity and the frame property, we conclude that
  @{term "safe_weak n C s h \<Gamma> Q"} implies @{term "safe n C s h \<Gamma> Q"}. *}

lemma safe_weakE:
  "safe_weak n C s h \<Gamma> Q \<Longrightarrow> safe n C s h \<Gamma> Q"
apply (induct n arbitrary: C s h, simp, clarsimp)
apply (rule conjI, clarify)
 apply (erule notE, erule (1) safety_monotonicity)
apply (clarify, drule frame_property, simp)
 apply (erule contrapos_nn, erule (1) safety_monotonicity, clarify)
apply (drule (2) all4_imp2D, clarsimp, fast)
done

end