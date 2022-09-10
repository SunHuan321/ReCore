theory RGSepSound
  imports CSLsound AuxillaryLemma
begin
subsection {* state definition *}
type_synonym localVariable = "heap"
type_synonym sharedVariable = "rname \<Rightarrow> heap"
type_synonym RGstate = "stack \<times> localVariable \<times> sharedVariable"
subsection {* rely guarantee definition *}
type_synonym rely = "rname \<Rightarrow> (heap \<times> heap) set"
type_synonym guar = rely


subsection {* RGsep assertions *}
datatype rgsep_assn = 
    RGlocal assn 
    | RGshared rname assn
    | RGconj rgsep_assn rgsep_assn
    | RGdisj rgsep_assn rgsep_assn
    | RGstar rgsep_assn rgsep_assn
    | RGex "(nat \<Rightarrow> rgsep_assn)"

text {* Separating conjunction of a finite list of assertions is 
  just a derived assertion. *}

primrec 
  RGistar :: "rgsep_assn list \<Rightarrow> rgsep_assn"
where
  "RGistar [] = RGlocal Aemp"
| "RGistar (P # Ps) = RGstar P (RGistar Ps)"

value "snd (1::nat,2::nat,3::nat)"
text {*The semantics of assertions is given by the following function
  indicating whether a state [ss] satisfies an assertion [p]. *}

primrec
  RGsat :: "RGstate \<Rightarrow> rgsep_assn \<Rightarrow> bool" (infixl "\<^sup>\<Turnstile>rgsep" 60)
where
  "(\<sigma> \<^sup>\<Turnstile>rgsep RGlocal P) = sat ((fst \<sigma>),fst (snd \<sigma>)) P"                                             
| "(\<sigma> \<^sup>\<Turnstile>rgsep RGshared r P) = (((fst (snd \<sigma>)) = Map.empty) \<and> (sat (fst \<sigma> , (snd (snd \<sigma>)) r) P))"
| "(\<sigma> \<^sup>\<Turnstile>rgsep RGconj P Q) = (\<sigma> \<^sup>\<Turnstile>rgsep P \<and> \<sigma> \<^sup>\<Turnstile>rgsep Q)"
| "(\<sigma> \<^sup>\<Turnstile>rgsep RGdisj P Q) = (\<sigma> \<^sup>\<Turnstile>rgsep P \<or> \<sigma> \<^sup>\<Turnstile>rgsep Q)"
| "(\<sigma> \<^sup>\<Turnstile>rgsep RGstar P Q) = (\<exists>h1 h2. (fst \<sigma>, h1, snd (snd \<sigma>)) \<^sup>\<Turnstile>rgsep P \<and> (fst \<sigma>, h2, snd (snd \<sigma>)) \<^sup>\<Turnstile>rgsep Q 
                            \<and> fst (snd \<sigma>) = (h1 ++ h2) \<and> disjoint (dom h1) (dom h2))"
| "(\<sigma> \<^sup>\<Turnstile>rgsep RGex PP) = (\<exists>v. \<sigma> \<^sup>\<Turnstile>rgsep PP v)"

definition 
  rgsep_implies :: "rgsep_assn \<Rightarrow> rgsep_assn \<Rightarrow> bool" (infixl "\<^sup>\<sqsubseteq>rgsep" 60)
where
  "P \<^sup>\<sqsubseteq>rgsep Q \<equiv> (\<forall>\<sigma>. \<sigma> \<^sup>\<Turnstile>rgsep P \<longrightarrow> \<sigma> \<^sup>\<Turnstile>rgsep Q)"
(** We can derive the following unfolding lemma for iterated
  separating conjunction. *)

lemma sat_istar_map_expand:
  "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<^sup>\<Turnstile>rgsep RGistar (map f l)
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1, snd (snd \<sigma>)) \<^sup>\<Turnstile>rgsep f r
              \<and> (fst \<sigma>, h2, snd (snd \<sigma>)) \<^sup>\<Turnstile>rgsep RGistar (map f (remove1 r l))
              \<and> fst (snd \<sigma>) = (h1 ++ h2)
              \<and> disjoint (dom h1) (dom h2))"
apply (case_tac \<sigma>, rename_tac s h, clarify)
apply (induction l arbitrary: \<sigma>, auto)
apply (intro exI conjI, (simp add: hsimps)+)+
  done

subsection {* Meaning of RGSep judgments *}
text{*
First, we define configuration safety (cf. Definitions 3 and 4 in paper).
Intuitively, any configuration is safe for zero steps. For n + 1 steps, it better 
(i) satisfy the postcondition if it is a terminal configuration, (ii) not abort, 
(iii) access memory only inside its footprint,
(iv) whenever the environment changes the shared state according to the rely,
the resulting configuration remains safe for another n steps, and
(v) after any step it does, re-establish the resource invariant and be safe for 
another n steps.
*}


definition RGdef :: "rname list \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> bool" 
where
"RGdef l \<Gamma> = (\<forall>r1 r2. r1 \<noteq> r2 \<and> r1 \<in> set l \<and> r2 \<in> set l \<longrightarrow>
 disjoint (dom (\<Gamma> r1)) (dom (\<Gamma> r2)))"

primrec
  rgsep_safe :: "nat \<Rightarrow> cmd \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  where
  "rgsep_safe 0       C s h \<Gamma> R G Q = True"
| "rgsep_safe (Suc n) C s h \<Gamma> R G Q = (
(* Condition (i) *)
            (C = Cskip \<longrightarrow> (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Q)
(* Conditon (ii) *)
          \<and> (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> aborts C (s, h ++ hF))
(* Condition (iii) *)
          \<and> accesses C s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
                    \<longrightarrow> (r \<notin> locked C) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
                    \<longrightarrow> rgsep_safe n C s h \<Gamma>' R G Q)

(* Condition (v) *)
          \<and> (\<forall>hJ hF C' \<sigma>'.
                red C (s,h ++ hJ ++ hF) C' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (llocked C') (llocked C)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (llocked C') (llocked C)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (locked C') \<and> (r \<notin> locked C) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (llocked C) (llocked C'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (llocked C) (llocked C')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (locked C) \<and> r \<notin> (locked C') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (locked C) \<and> r \<notin> (locked C') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (locked C) \<or> r \<in> (locked C') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_safe n C' (fst \<sigma>') h' \<Gamma>' R G Q)

)))"

text {*  The meaning of RGSep judgements. *}

definition
    RGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> cmd \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>rgsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>rgsep {P} C {Q} \<equiv> (user_cmd C \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<longrightarrow> rgsep_safe n C s h \<Gamma> R G Q))" 

text{* Free variables and substitutions *}

text{** The free variables of an assertion [p] are given as a predicate [fvA p]. *}

primrec fvAA :: "rgsep_assn \<Rightarrow> var set"
  where
    "fvAA (RGlocal P) = fvA P"
  | "fvAA (RGshared r P) = fvA P"
  | "fvAA (RGconj P Q) = (fvAA P \<union> fvAA Q)"
  | "fvAA (RGstar P Q) = (fvAA P \<union> fvAA Q)"
  | "fvAA (RGdisj P Q) = (fvAA P \<union> fvAA Q)"
  | "fvAA (RGex P) = (\<Union>x. fvAA (P x))"

text{** The free region names in an assertion [p]. *}
primrec frgnA :: "rgsep_assn \<Rightarrow> rname \<Rightarrow> bool"
  where
    "frgnA (RGlocal P) _ = False"
  | "frgnA (RGshared r P) v = (v = r)"
  | "frgnA (RGconj P Q) v = ((frgnA P v) \<or> (frgnA Q v))"
  | "frgnA (RGstar P Q) v = ((frgnA P v) \<or> (frgnA Q v))"
  | "frgnA (RGdisj P Q) v = ((frgnA P v) \<or> (frgnA Q v))"
  | "frgnA (RGex P) v = (\<exists>x. frgnA (P x) v)"

text {* Proposition 4.2 for assertions *}



subsection{* soundness proof *}
(** 1. Assertions depend only on the values of their free variables and regions. *)
lemma RGassn_agrees: "agrees (fvAA P) s s' \<Longrightarrow> ((s, lh, sh) \<^sup>\<Turnstile>rgsep P \<equiv> (s', lh, sh) \<^sup>\<Turnstile>rgsep P)"
  apply (induct P arbitrary: lh sh, simp_all add: bexp_agrees)
    apply (simp add: assn_agrees)
   apply (simp add: assn_agrees)
  apply (rule iff_exI, simp add: agrees_def)
  done

lemma RGassn_agrees_rgn: "\<forall>v. frgnA P v \<longrightarrow> \<Gamma> v = \<Gamma>' v \<Longrightarrow> (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<equiv> (s, h, \<Gamma>') \<^sup>\<Turnstile>rgsep P"
  apply (induct P arbitrary: s h, simp, clarsimp)
  using RGsat.simps(3) frgnA.simps(3) apply blast
    apply (metis RGsat.simps(4) frgnA.simps(5))
   apply simp
  by fastforce                                                        
(** 2. Safety is monotone with respect to the step number
(cf. Proposition 3 in paper). *)

lemma RGsafe_mon:
  "\<lbrakk> rgsep_safe n C s h \<Gamma> R G Q; m \<le> n \<rbrakk> \<Longrightarrow> rgsep_safe m C s h \<Gamma> R G Q"
  apply (induct m arbitrary: C s n h \<Gamma> R G Q, simp)
  apply (case_tac n, clarify)
  apply (simp only: rgsep_safe.simps, clarsimp)
  apply (rule conjI)
   apply blast
  apply (clarsimp)
  apply (drule all4D)
  apply (drule (2) imp4D, simp, clarsimp)
  apply auto
   apply (rule_tac x="h'" in exI)
   apply auto
  apply (rule_tac x= "h'" in exI)
  apply auto
  done

(** 3. Safety depends only on the values of the free variables of the
program, the postcondition and the resource invariants
(cf. Proposition 4 in the paper). To establish this property, we need
the following auxiliary lemmas.
*)
lemma RGsafe_agrees: 
  "\<lbrakk> rgsep_safe n C s h \<Gamma> R G Q ; 
     agrees (fvC C \<union> fvAA Q) s s' \<rbrakk>
   \<Longrightarrow> rgsep_safe n C s' h \<Gamma> R G Q"
  apply (induct n arbitrary: C s s' h \<Gamma> R G, simp, simp only: rgsep_safe.simps, clarify)
  apply (rule conjI)
  using RGassn_agrees apply auto[1]
  apply (rule conjI, clarsimp)
   apply (metis aborts_agrees agrees_search(1) fst_conv snd_conv)
  apply (rule conjI, subst (asm) accesses_agrees, simp_all)
  apply (rule conjI, blast)
  apply (clarify, drule_tac X="fvC C \<union> fvAA Q" in red_agrees, 
       simp (no_asm), fast, simp (no_asm), fast, clarify)
  apply (drule (1) all4_impD, clarsimp)
  apply (rule_tac x="h'" in exI, simp add: hsimps)
  apply (drule red_properties)
  apply (rule_tac x = "\<Gamma>'" in exI)
  by (meson agrees_search(1) agrees_search(2))

(* -------------------------------------------------------------------------- *)
(** ** Soundness of the proof rules *)
(* -------------------------------------------------------------------------- *)

(** We now show the soundness of each proof rule of RGSep separately. *)
(*
definition stable :: "rgsep_assn \<Rightarrow> rname list \<Rightarrow> rely \<Rightarrow> bool"
  where
"stable P exn R \<equiv> \<forall>s h \<Gamma> \<Gamma>' r. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<longrightarrow> (
                        (r \<notin> set exn \<longrightarrow> ((\<Gamma> r, \<Gamma>' r) \<in> R r \<or> \<Gamma> r = \<Gamma>' r))
                      \<longrightarrow> (r \<in> set exn \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                      \<longrightarrow> (r \<notin> set exn \<longrightarrow> disjoint (dom h) (dom (\<Gamma>' r)) \<or> \<Gamma> r = \<Gamma>' r)
                  )   \<longrightarrow> (s, h, \<Gamma>') \<^sup>\<Turnstile>rgsep P"
*)

definition stable :: "rgsep_assn \<Rightarrow> rname list \<Rightarrow> rely \<Rightarrow> bool"
  where
"stable P exn R \<equiv> \<forall>s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<longrightarrow> (\<forall>\<Gamma>'. 
                        (\<forall>r. r \<notin> set exn \<longrightarrow> ((\<Gamma> r, \<Gamma>' r) \<in> R r \<or> \<Gamma> r = \<Gamma>' r))
                      \<longrightarrow> (\<forall>r. r \<in> set exn \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                      \<longrightarrow> (\<forall>r. r \<notin> set exn \<longrightarrow> disjoint (dom h) (dom (\<Gamma>' r)) \<or> \<Gamma> r = \<Gamma>' r)
                     \<longrightarrow> (s, h, \<Gamma>') \<^sup>\<Turnstile>rgsep P)"

lemma RGsafe_skip[intro!]:
  "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Q \<Longrightarrow> stable Q [] R \<Longrightarrow> rgsep_safe n Cskip s h \<Gamma> R G Q"
  apply (induct n arbitrary: s h \<Gamma>, simp, clarsimp)
  apply (case_tac n, simp)
  apply (simp only: rgsep_safe.simps, clarsimp)
  apply (rule conjI, simp add: stable_def)
   apply (drule all3_impD, simp, blast)
  apply meson 
  apply (simp add: stable_def)
   by blast

theorem RGrule_skip:
  "stable P [] R \<Longrightarrow> RGSep R G P Cskip P"
  by (auto simp add: RGSep_def)

(** *** Parallel composition *)
definition RGUnion :: "rely \<Rightarrow> rely \<Rightarrow> rely" 
  where "RGUnion R G r \<equiv>  (R r) \<union> (G r) "

definition RGInter :: "rely \<Rightarrow> rely \<Rightarrow> rely" 
  where "RGInter R G r \<equiv>  (R r) \<inter> (G r) "

lemma locked_diff : "disjoint (set (llocked C2)) (set (llocked C1')) \<Longrightarrow> \<forall>r. r \<in> set (llocked C1') \<and> r \<notin> set (llocked C1) 
      \<longrightarrow> (r \<in> set (llocked C1') \<or> r \<in> set (llocked C2)) \<and> r \<notin> set (llocked C1) \<and> r \<notin> set (llocked C2)"
  by (metis Set.set_insert disjoint_def disjoint_insert(1))

lemma map_4_add1 : "\<lbrakk>disjoint (dom c) (dom a); disjoint (dom c) (dom b); disjoint (dom c) (dom d)\<rbrakk> 
      \<Longrightarrow> a ++ b ++ c ++ d = a ++ c ++ (b ++ d)"
  by (metis map_add_assoc map_add_commute)

lemma map_4_add2: "\<lbrakk>disjoint (dom a) (dom b); disjoint (dom a) (dom c); 
        disjoint (dom a) (dom d); disjoint (dom b) (dom c)\<rbrakk> \<Longrightarrow> 
        a ++ (b ++ (c ++ d)) = b ++ (c ++ (a ++ d))"
  by (simp add: map_add_left_commute)

lemma map_4_add3 :  "\<lbrakk>disjoint (dom c) (dom a); disjoint (dom c) (dom b); disjoint (dom c) (dom d)\<rbrakk> 
      \<Longrightarrow> a ++ b ++ (c ++ d) = a ++ (c ++ (b ++ d))"
  by (metis map_add_assoc map_add_commute)

lemma par_skip: "\<lbrakk>rgsep_safe n Cskip s h1 \<Gamma> (RGUnion R G2) G1 Q1;
        rgsep_safe n Cskip s h2 \<Gamma> (RGUnion R G1) G2 Q2;
        disjoint (dom h1) (dom h2)\<rbrakk>
   \<Longrightarrow> rgsep_safe n Cskip s (h1 ++ h2) \<Gamma> R (RGUnion G1 G2) (RGstar Q1 Q2)"
  apply (induct n arbitrary: \<Gamma>, simp, clarsimp)
  apply (rule conjI)
   apply (rule_tac x = "h1" in exI, simp)
   apply (rule_tac x = "h2" in exI, simp)
  apply (clarsimp)
  by (simp add: RGUnion_def)

lemma RGsafe_par: 
  "\<lbrakk>rgsep_safe n C1 s h1 \<Gamma> (RGUnion R G2) G1 Q1;
    rgsep_safe n C2 s h2 \<Gamma> (RGUnion R G1) G2 Q2;
    wf_cmd (Cpar C1 C2);
    disjoint (dom h1) (dom h2);
    disjoint (fvC C1 \<union> fvAA Q1) (wrC C2);
    disjoint (fvC C2 \<union> fvAA Q2) (wrC C1)\<rbrakk> \<Longrightarrow> 
    rgsep_safe n (Cpar C1 C2) s (h1 ++ h2) \<Gamma> R (RGUnion G1 G2) (RGstar Q1 Q2)"
  apply(induct n arbitrary: C1 C2 s h1 h2 \<Gamma>, simp, clarsimp)
(* no aborts *)
  apply (rule conjI, clarify, erule aborts.cases, simp_all)
      apply (drule_tac a = "h2 ++ hF" in all_impD, simp, simp add: map_add_assoc)
     apply (clarify, drule allD, drule_tac a = "h1 ++ hF" in all_impD, 
            simp add: hsimps, simp add: hsimps)
(* no races *)
 apply (clarsimp, erule notE, erule disjoint_search [rotated], erule disjoint_search,
        erule order_trans [OF writes_accesses])+
(*accesses *)
  apply (rule conjI, erule order_trans, simp)+
(*rely *)
  apply(rule conjI, simp add: RGUnion_def)
(* step *)                       
  apply (clarsimp, erule red_par_cases)
(* C1 does a step *)
    apply (clarify, drule_tac a = "h2 ++ hF" and b = "C1'" and c = "a" and d = "b" in all4_impD)
     apply (clarsimp, simp add: locked_eq list_minus_appr)
  apply (subgoal_tac "h1 ++ h2 ++ hplus_list (map \<Gamma> (list_minus (llocked C1') (llocked C1))) ++ hF = 
        h1 ++ hplus_list (map \<Gamma> (list_minus (llocked C1') (llocked C1))) ++ (h2 ++ hF)", simp)
     apply (rule map_4_add1)
       apply (simp add: disjoint_hplus_list, clarsimp)
       apply (metis disjoint_search(1) locked_diff)
       apply (simp add: disjoint_hplus_list, clarsimp)
      apply (metis disjoint_search(1) locked_diff)
       apply (simp add: disjoint_hplus_list, clarsimp)
     apply (metis disjoint_search(1) locked_diff)
    apply (drule imp3D, simp)
      apply (simp add: list_minus_appr locked_eq)
     apply (simp add: locked_eq)
     apply (metis locked_diff, clarsimp)
    apply (rule_tac x = "h' ++ h2" and y = "\<Gamma>'" in ex2I, clarsimp)
    apply (rule conjI, simp add: locked_eq list_minus_appr) 
     apply (rule sym) apply (rule map_4_add1)
       apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
      apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (rule conjI)
     apply (simp add: list_minus_appr locked_eq)
    apply (rule conjI, clarsimp)
    apply (rule conjI, clarsimp)
     apply (simp add: RGUnion_def)
    apply (rule conjI)
     apply (metis Set.set_insert disjoint_def disjoint_insert(1))
    apply (frule (1) red_wf_cmd, drule red_properties, clarsimp)
    apply (drule_tac a=C1' and b=C2 in mall2D, simp add: hsimps)
    apply (subst map_add_commute, simp add: hsimps)
    apply (drule mall4_imp2D, erule_tac[3] mimp3D, simp_all add: hsimps)
      apply (rule_tac s = "s" in RGsafe_agrees)
       apply (metis (mono_tags, lifting) RGUnion_def UnCI locked_diff locked_eq)
      apply (metis agrees_minusD agrees_search(1) agrees_simps(4) disjoint_search(1))
     apply auto[1]
    apply auto[1]
(* C2 does a step *)
   apply (clarify, drule_tac a = "h1 ++ hF" and b = "C2'" and c = "a" and d = "b" in all4_impD) back
  apply (clarsimp, simp add: locked_eq list_minus_appl)
    apply (subgoal_tac "h1 ++ (h2 ++ (hplus_list (map \<Gamma> (list_minus (llocked C2') (llocked C2))) ++ hF))
        = h2 ++ (hplus_list (map \<Gamma> (list_minus (llocked C2') (llocked C2))) ++ (h1 ++ hF))", simp)
    apply (rule map_4_add2, simp_all)
     apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) locked_diff set_list_minus)
    apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) locked_diff set_list_minus)
   apply (drule imp3D)
      apply auto[1]
     apply (metis list_minus_appl locked_eq)
    apply (metis locked_diff locked_eq)
   apply (clarsimp, rule_tac x = "h' ++ h1" and y = "\<Gamma>'" in ex2I)
   apply (rule conjI, simp add: locked_eq list_minus_appl)
    apply (rule sym) apply (rule map_4_add3)
      apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (intro conjI)
  apply auto[1]
    apply (metis list_minus_appl locked_eq)
    apply (metis disjoint_simps(3) dom_map_add)
  using RGUnion_def apply force
    apply (metis locked_diff locked_eq)
   apply (frule (1) red_wf_cmd, drule red_properties, clarsimp)
   apply (drule_tac a=C1 and b= C2' in mall2D, simp add: hsimps)
    apply (drule mall4_imp2D, erule_tac[3] mimp3D, simp_all add: hsimps)
     apply (rule_tac s = "s" in RGsafe_agrees)
      apply (metis (mono_tags, lifting) RGUnion_def UnCI locked_diff locked_eq)
      apply (metis agrees_minusD agrees_search(1) agrees_simps(4) disjoint_search(1))
     apply auto[1]
    apply auto[1]
(* Par skip skip *)
  apply (clarify)
  apply (rule_tac x = "h1 ++ h2" in exI, simp add: hsimps)
  apply (rule_tac x = "\<Gamma>" in exI, simp)
  by (simp add: par_skip)
  
theorem RGrule_par: "\<lbrakk>(RGUnion R G2), G1 \<^sup>\<turnstile>rgsep {P1} C1 {Q1};
                     (RGUnion R G1), G2 \<^sup>\<turnstile>rgsep {P2} C2 {Q2};
                     disjoint (fvC C1 \<union> fvAA Q1) (wrC C2);
                     disjoint (fvC C2 \<union> fvAA Q2) (wrC C1)\<rbrakk>
       \<Longrightarrow> R, (RGUnion G1 G2) \<^sup>\<turnstile>rgsep {RGstar P1 P2} (Cpar C1 C2) {RGstar Q1 Q2}"
  using RGSep_def RGsafe_par fst_conv user_cmdD by auto

subsubsection {* Resource declaration *}

lemma map_upd_irr : "r \<notin> set l \<Longrightarrow> map (\<Gamma>(r := hK)) l = map \<Gamma> l"
  by simp

lemma RGdef_removeAll: "\<lbrakk> RGdef (removeAll r l) \<Gamma>;  \<forall>r'. r' \<in> set (removeAll r l) 
      \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (\<Gamma> r')) \<rbrakk> \<Longrightarrow> RGdef l \<Gamma>"
  apply (simp add: RGdef_def, clarsimp)
  apply (case_tac "r1 = r", simp)
  apply (case_tac "r2 = r", simp)
  using disjoint_search(1) apply blast
  by blast

lemma RGdef_upd_irr : "r \<notin> set l \<Longrightarrow> RGdef l (\<Gamma>(r := hK)) \<Longrightarrow> RGdef l \<Gamma>"
  apply (simp add: RGdef_def, clarsimp)
  apply (subgoal_tac "r1 \<noteq> r \<and> r2 \<noteq> r")
   apply presburger
  by blast

lemma resource_Skip : "\<lbrakk>rgsep_safe n Cskip s h \<Gamma> (R(r := Rr)) (G(r := Gr)) (RGstar Q (RGshared r q));
        disjoint (dom h) (dom (\<Gamma> r)); \<not> frgnA Q r \<rbrakk>
    \<Longrightarrow> rgsep_safe n Cskip s (h ++ \<Gamma> r) (\<Gamma>(r := hK)) R G (RGstar Q (RGlocal q)) "
  apply (induct n arbitrary: \<Gamma> hK, simp, clarsimp)
  apply (rule conjI) apply (rule_tac x = "h" in exI)
  apply (rule conjI)
    apply (metis RGassn_agrees_rgn fun_upd_other)
   apply (rule_tac x= "\<Gamma> r" in exI, simp, clarsimp)
  apply (drule_tac a = "\<Gamma>'(r := \<Gamma> r)" in allD, simp)
  apply (drule impD, clarsimp)
  apply (drule_tac a = "\<Gamma>'(r := \<Gamma> r)" and b = "\<Gamma>' r" in mall2_imp2D, simp_all)
  done

lemma RGsafe_resource:
 "\<lbrakk> rgsep_safe n C s h \<Gamma> (R(r := Rr)) (G(r := Gr)) (RGstar Q (RGshared r q)); wf_cmd C; frgnA Q r = False\<rbrakk> \<Longrightarrow> 
   (\<forall>hK. r \<notin> locked C \<longrightarrow> disjoint (dom h) (dom (\<Gamma> r)) \<longrightarrow> 
    rgsep_safe n (Cresource r C) s (h ++ (\<Gamma> r)) (\<Gamma>(r := hK)) R G (RGstar Q (RGlocal q)))
   \<and> (\<forall>hK. r \<in> locked C \<longrightarrow> rgsep_safe n (Cresource r C) s h (\<Gamma>(r := hK)) R G (RGstar Q (RGlocal q))) "
  apply (induction n arbitrary: C s h \<Gamma>, simp)
  apply (rule conjI, clarsimp)
  apply (intro allI impI conjI, clarsimp)
(* no aborts *)
    apply(erule aborts.cases, simp_all add:hsimps)
    apply (metis disjoint_simps(3) dom_map_add map_add_assoc safety_monotonicity_helper)
(* access *)
   apply (erule order_trans, simp)
(* rely *)
    apply (drule_tac a = "C" and b = "s" and c = "h" and d = "\<Gamma>'(r := \<Gamma> r)"  in mall4_impD)
     apply (erule all_impD, simp)
    apply (subgoal_tac "\<forall>hK. rgsep_safe n (Cresource r C) s (h ++ (\<Gamma>'(r := \<Gamma> r)) r) (\<Gamma>'(r := \<Gamma> r, r := hK)) R G (RGstar Q (RGlocal q))")
     apply (metis fun_upd_same fun_upd_triv fun_upd_upd, simp)
(* normal step *)
   apply (clarify, frule red_properties, clarsimp)
   apply ( erule red.cases, simp_all, clarify)
    apply (case_tac "r \<in> locked C'a")
     apply (drule_tac a = "hF" and b = "C'a" and c = "ab" and d = "bb" in all4_imp4D, simp_all)
         apply (simp add: removeAll_id locked_eq list_minus_removeAll)
         apply (subgoal_tac "\<Gamma> r ++ (hplus_list (map \<Gamma> (removeAll r (list_minus (llocked C'a) (llocked Ca)))) ++ hF)
                        = (hplus_list (map \<Gamma>  (list_minus (llocked C'a) (llocked Ca)))) ++ hF", simp)
        apply (simp add: map_add_assoc) 
        apply (subgoal_tac "\<Gamma> r ++ hplus_list (map \<Gamma> (removeAll r (list_minus (llocked C'a) (llocked Ca))))
                       = hplus_list (map \<Gamma> (list_minus (llocked C'a) (llocked Ca)))", simp)
        apply (rule sym) 
        apply (rule hplus_list_map_expand)
          apply (rule distinct_list_minus)
          apply (simp add: red_wf_cmd wf_cmd_distinct_locked)
         apply (simp add: set_list_minus)
        apply (clarsimp)
        apply (case_tac "r1 = r")
         apply (simp add: disjoint_commute)
        apply (case_tac "r2 = r")
         apply blast
        apply (simp add: RGdef_def)
       apply (simp add: removeAll_id locked_eq list_minus_removeAll)
       apply (metis DiffD1 DiffD2 RGdef_removeAll RGdef_upd_irr 
        disjoint_search(1) member_remove remove_code(1) set_list_minus)
      apply metis
     apply (clarsimp, rule_tac x = "h'" and y = "\<Gamma>'( r:= hK)" in ex2I)
     apply (rule conjI, simp add: removeAll_id locked_eq)
      apply (simp add: list_minus_removeAll_irr, simp)
     apply (rule conjI, simp add: list_minus_removeAll_irr locked_eq)
      apply (rule_tac r = "r" and \<Gamma> = "\<Gamma>'(r := hK)" and hK = "\<Gamma>' r" in RGdef_upd_irr, simp, simp)
     apply (rule conjI) apply presburger
     apply (simp add: red_wf_cmd)
    apply (simp add: removeAll_id locked_eq)
    apply (drule_tac a = "hF ++ \<Gamma> r" and b = "C'a" and c = "ab" and d = "bb" in all4_imp4D, simp_all)
       apply (subgoal_tac "\<Gamma> r ++ (hplus_list (map \<Gamma> (list_minus (llocked C'a) (llocked Ca))) ++ hF)
                  = hplus_list (map \<Gamma> (list_minus (llocked C'a) (llocked Ca))) ++ (hF ++ \<Gamma> r)", simp)
       apply (subgoal_tac "hF ++ \<Gamma> r = \<Gamma> r ++ hF", simp)
        apply (rule hsimps(3))
         apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
       apply (simp add: map_add_commute)
      apply (metis DiffE RGdef_upd_irr set_list_minus)
     apply (metis disjoint_commute)
    apply (clarsimp, rule_tac x = "h' ++ \<Gamma>' r" and y = "\<Gamma>'(r := hK)" in ex2I, simp)
    apply (rule conjI, simp add: hsimps)
     apply (rule map_add_subst) apply (subgoal_tac "hF ++ \<Gamma> r = \<Gamma> r ++ hF", simp)
      apply (rule hsimps(3))
       apply auto[1]
  apply (metis DiffD1 DiffD2 disjoint_map_list set_list_minus)
     apply (simp add: map_add_commute)
    apply (rule conjI) using RGdef_def fun_upd_def set_list_minus apply force
    apply (rule conjI) apply presburger
    apply (meson disjoint_search(1) red_wf_cmd)
(* exit *)
   apply (clarsimp, rule_tac x = "h ++ \<Gamma> r" in exI, simp add: hsimps)
   apply(rule_tac x = "\<Gamma>(r := hK)" in exI, simp)
   apply (rule_tac Rr = "Rr" and Gr = "Gr" in resource_Skip, simp_all)
  apply (intro allI impI conjI, clarsimp)
(* no aborts *)
  apply(erule aborts.cases, simp_all add:hsimps)
    apply (metis disjoint_simps(3) dom_map_add map_add_assoc safety_monotonicity_helper)  
(* rely *)
   apply (drule_tac a = "C" and b = "s" and c = "h" and d = "\<Gamma>'(r := \<Gamma> r)"  in mall4_impD, simp_all)
   apply (metis fun_upd_triv)
(* normal step *)
  apply (clarsimp, erule red.cases, simp_all, clarify)
  apply (drule_tac a = "hF" and b = "C'a" and c = "ab" and d = "bb" in all4_imp4D, simp_all)
     apply (simp add:  list_minus_removeAll2 list_minus_removeAll_irr)
     apply (subgoal_tac "r \<notin> set (list_minus (llocked C'a) (llocked Ca))", simp, simp add: locked_eq)
    apply (metis Diff_iff RGdef_upd_irr list_minus_removeAll2 locked_eq removeAll_id set_list_minus)
   apply metis
   apply (clarify, frule red_properties, clarsimp)
  apply (case_tac "r \<in> locked C'a")
   apply (rule_tac x = "h'" and y = "\<Gamma>'(r := hK)" in ex2I, simp)
   apply (rule conjI, simp add: hsimps list_minus_removeAll2)
    apply (rule map_add_subst, simp add: map_add_assoc)
    apply (subgoal_tac "r \<notin> set (list_minus (llocked C'a) (llocked Ca))", simp_all add: locked_eq)
   apply (rule conjI, simp add: RGdef_def list_minus_removeAll2)
   apply (rule conjI) apply blast
   apply (rule conjI) apply meson
  apply (simp add: red_wf_cmd)
   apply (rule_tac x = "h' ++ \<Gamma>' r" and y = "\<Gamma>'(r := hK)" in ex2I, simp)
   apply (rule conjI, simp add: hsimps list_minus_removeAll2)
    apply (rule map_add_subst, simp add: map_add_assoc)
    apply (subgoal_tac " hplus_list (map \<Gamma>' (list_minus (llocked Ca) (llocked C'a)))
    = \<Gamma>' r ++ hplus_list (map \<Gamma>' (list_minus (removeAll r (llocked Ca)) (llocked C'a)))", simp)
  apply (simp add: list_minus_removeAll)
    apply (rule hplus_list_map_expand) 
      apply (rule distinct_list_minus)
     apply (simp add: red_wf_cmd wf_cmd_distinct_locked, simp, simp add: RGdef_def)
   apply (rule conjI, simp add: RGdef_def list_minus_removeAll2)
   apply (rule conjI) apply (metis Diff_iff RGdef_def set_list_minus)
  apply (rule conjI) apply meson
  apply (simp add: red_wf_cmd)
  done

theorem RGrule_resource : 
    "\<lbrakk> R(r := Rr), G(r:=Gr) \<^sup>\<turnstile>rgsep {RGstar P (RGshared r p)} C {RGstar Q (RGshared r q)};
     \<not> frgnA P r; \<not> frgnA Q r\<rbrakk> \<Longrightarrow> 
      R, G \<^sup>\<turnstile>rgsep {RGstar P (RGlocal p)} (Cresource r C) {RGstar Q (RGlocal q)}"
  apply (simp add: RGSep_def, clarsimp)
  apply (drule_tac a = "n" and b = "s" and c = "h1" and d = "\<Gamma>(r := h2)" in all4_impD, simp)
   apply (metis RGassn_agrees_rgn fun_upd_other)
  apply (drule RGsafe_resource, simp_all add: user_cmd_wf user_cmdD)
  apply (drule_tac a = "\<Gamma> r" in allD, simp)
  done

subsubsection {* Frame rule *}

text {* The safety of the frame rule can be seen as a special case of the parallel composition
  rule taking one thread to be the empty command. *}

lemma RGsafe_frame:
 "\<lbrakk> rgsep_safe n C s h \<Gamma> Rely Guar Q; 
    disjoint (dom h) (dom hR);
    disjoint (fvAA R) (wrC C);
    stable R [] (RGUnion Rely Guar);
    (s, hR, \<Gamma>) \<^sup>\<Turnstile>rgsep R\<rbrakk>
  \<Longrightarrow> rgsep_safe n C s (h ++ hR) \<Gamma> Rely Guar (RGstar Q R)"
  apply (induct n arbitrary: C s h hR \<Gamma>, simp, clarsimp)
(* skip *)
  apply (rule conjI, clarify, fast)
(* no aborts *)
  apply (rule conjI, clarify)
  apply (drule_tac a = "hR ++ hF" in all_impD, simp, simp add: hsimps)
(* access *)
  apply (rule conjI, erule order_trans, simp)
(* rely *)
  apply (rule conjI, clarsimp)
  apply (subgoal_tac "rgsep_safe n C s h \<Gamma>' Rely Guar Q")
    apply (drule mall5_imp4D, simp_all)
   apply (simp add:stable_def)
  apply (metis (no_types, lifting) RGUnion_def UnCI)
(* step *)
  apply (clarify, frule red_properties, clarsimp)
  apply (drule_tac a = "hR ++ hF" in all4Dto3D, simp add: hsimps)
  apply (drule_tac a = "C'" and b = "a" and c = "b" in all3_impD)
   apply (subgoal_tac "hR ++ (hplus_list (map \<Gamma> (list_minus (llocked C') (llocked C))) ++ hF)
            = hplus_list (map \<Gamma> (list_minus (llocked C') (llocked C))) ++ (hR ++ hF)", simp)
   apply (rule hsimps(3))
    apply (simp add: disjoint_hplus_list)
    apply (metis  DiffD1 DiffD2 disjoint_search(1) locked_eq)
    apply (simp add: disjoint_hplus_list)
  apply (metis  DiffD1 DiffD2 disjoint_search(1) locked_eq)
  apply (drule imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h' ++ hR" and y = "\<Gamma>'" in ex2I)
  apply (rule conjI) 
     apply (simp_all add: hsimps(4))
   apply (rule map_add_subst)
   apply (simp add: locked_eq)
   apply (rule hsimps(3), simp)
  apply (metis DiffD1 DiffD2 disjoint_map_list disjoint_search(1) set_list_minus)
  apply (rule conjI)
   apply auto[1]
  apply (drule mall5_imp4D, simp_all)
    apply auto[1] apply auto[1]
  apply (subgoal_tac "(s, hR, \<Gamma>') \<^sup>\<Turnstile>rgsep R")
   apply (subgoal_tac "agrees (fvAA R) a s")
    apply (simp add: RGassn_agrees)
   apply auto[1]
  apply (simp add: stable_def)
  by (metis RGUnion_def UnCI)

theorem RGrule_frame:
 "\<lbrakk> Rely ,Guar \<^sup>\<turnstile>rgsep {P} C {Q};  
    disjoint (fvAA R) (wrC C);
    stable R [] (RGUnion Rely Guar)\<rbrakk>
  \<Longrightarrow> Rely ,Guar \<^sup>\<turnstile>rgsep {RGstar P R} C {RGstar Q R}"
  using RGSep_def RGsafe_frame by auto

subsubsection {* Conditional critical regions *}

lemma RGsafe_inwith_rely_irr: 
  "\<lbrakk>rgsep_safe n (Cinwith r C) s h \<Gamma> (R(r :={})) G Q; stable Q [] R\<rbrakk>
   \<Longrightarrow> rgsep_safe n (Cinwith r C) s h \<Gamma> R G Q"
  apply (induct n arbitrary: C s h \<Gamma>, simp, clarsimp)
  apply (drule all4_imp4D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
  apply (erule red.cases, simp_all)
  apply (case_tac n, simp)
  apply (rule RGsafe_skip, simp_all)
  done

theorem RGrule_withR :
  "\<lbrakk> (R(r :={})), G  \<^sup>\<turnstile>rgsep {P} (Cwith r B C) {Q};
     stable P [] R; stable Q [] R\<rbrakk> 
  \<Longrightarrow> R, G  \<^sup>\<turnstile>rgsep {P} (Cwith r B C) {Q}"
  apply (simp add: RGSep_def)
proof(intro allI impI)
  fix n s lh sh
  assume a1: " user_cmd C \<and> (\<forall>n s lh sh. (s, lh, sh) \<^sup>\<Turnstile>rgsep P \<longrightarrow> rgsep_safe n (Cwith r B C) s lh sh (R(r := {})) G Q)"
    and  a2: "stable P [] R"
    and  a3: "stable Q [] R"
    and  a4: " (s, lh, sh) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_safe n (Cwith r B C) s lh sh R G Q"
    apply (induct n arbitrary : sh, simp, clarsimp)
(* no abort *)
    apply (rule conjI, clarify, erule aborts.cases, simp_all)
(* rely *)
    apply (rule conjI, intro allI impI, erule mall_impD, simp add: stable_def, blast)
(* step *)
    apply (clarsimp)
    apply (drule_tac a = "Suc n" in allD, drule all3_impD, simp)
    apply (clarsimp, erule red.cases, simp_all)
    apply (drule_tac a = "hF" in all4Dto3D, drule all3_impD, simp)
     apply (rule red_With1, simp_all, clarsimp)
    apply (rule_tac x = "h'" in exI, simp , rule_tac x = "\<Gamma>'" in exI)
    apply (rule conjI, blast)
    apply (rule conjI, simp)
    apply (rule RGsafe_inwith_rely_irr, simp_all)
    done
qed

lemma rule_with_skip: "\<lbrakk>rgsep_safe n C s h \<Gamma> R G (RGstar Q (RGlocal q));R r = {};
        r \<notin> locked C; (s, \<Gamma> r) \<Turnstile> p; disjoint (fvA p) (wrC C); \<not> frgnA Q r; 
        \<forall> s h h'. (s, h) \<Turnstile> p \<and> (s, h')\<Turnstile> q \<longrightarrow>  (h, h') \<in> G r; stable Q [] R\<rbrakk> 
    \<Longrightarrow> rgsep_safe n (Cinwith r C)  s h \<Gamma> R G (RGstar Q (RGshared r q))"
  apply (induct n arbitrary: C s h \<Gamma>, simp, clarsimp)
  apply (rule conjI, clarsimp, erule aborts.cases, simp_all)
   apply auto[1]
  apply (rule conjI, intro allI impI)
  apply metis apply (clarsimp)
  apply (erule red.cases, simp_all, clarsimp)
   apply (drule_tac a = "hF" and b = "C'a" and c = "ab" and d = "bb" in all4_impD)
    apply (subgoal_tac "removeAll r (list_minus (r # llocked C'a) (llocked Ca))
                      = list_minus (llocked C'a) (llocked Ca)", simp)
    apply (metis list_minus_removeAll locked_eq removeAll.simps(2) removeAll_id)
   apply (drule imp3D, simp)
     apply (metis list_minus_removeAll locked_eq removeAll.simps(2) removeAll_id)
  apply auto[1]
   apply (clarsimp, rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
   apply (intro conjI)
    apply (subgoal_tac "removeAll r (list_minus (r # llocked Ca) (llocked C'a))
                      = list_minus (llocked Ca) (llocked C'a)", simp)
       apply (metis list_minus_removeAll locked_eq removeAll.simps(2) removeAll_id)
      apply (metis list_minus_removeAll locked_eq removeAll.simps(2) removeAll_id)
     apply blast  apply blast
   apply (drule mall4_imp2D, simp, simp)
   apply (drule  mimp2D, simp_all)
    apply (metis agrees_minusD assn_agrees disjoint_search(1) fst_conv red_properties)
   apply (meson disjoint_search(1) disjoint_search(5) red_properties)
  apply (clarsimp, rule_tac x = "h1" and y = "\<Gamma>(r := h2)" in ex2I, clarsimp)
  apply (rule conjI) using RGdef_def apply auto[1]
  apply (rule conjI, simp add: hsimps)
  apply (rule RGsafe_skip, simp)
   apply (subgoal_tac "\<forall>v. frgnA Q v \<longrightarrow> \<Gamma> v =  (\<Gamma>(r := h2)) v")
  using RGassn_agrees_rgn apply blast
  apply (simp)
   apply (simp add: stable_def, clarify)
  apply (rule conjI) apply blast
  by auto


theorem RGrule_with:
  "\<lbrakk> R, G  \<^sup>\<turnstile>rgsep {RGstar P (RGlocal (Aconj p (Apure B)))} C {RGstar Q (RGlocal q)};
     \<not> frgnA Q r; R r = {}; \<forall>s h h'. (s, h) \<Turnstile> p \<longrightarrow> (s, h') \<Turnstile> q \<longrightarrow> (h, h') \<in> G r;
     disjoint (fvA p) (wrC C); stable P [] R ; stable Q [] R\<rbrakk> 
    \<Longrightarrow> R, G  \<^sup>\<turnstile>rgsep {RGstar P (RGshared r p)} (Cwith r B C) {RGstar Q (RGshared r q)}"
proof(simp add: RGSep_def, clarsimp)
  fix n s lh sh
  assume a1: "\<not> frgnA Q r"
    and a2: "R r = {}"
    and a3: " \<forall>s h. (s, h) \<Turnstile> p \<longrightarrow> (\<forall>h'. (s, h') \<Turnstile> q \<longrightarrow> (h, h') \<in> G r)"
    and a4: "stable P [] R"
    and a5: "stable Q [] R"
    and a6: "user_cmd C"
    and a7: "\<forall>n s lh sh.
          (\<exists>h1. (s, h1, sh) \<^sup>\<Turnstile>rgsep P \<and> (\<exists>h2. (s, h2) \<Turnstile> p \<and> bdenot B s \<and> lh = h1 ++ h2 \<and> disjoint (dom h1) (dom h2))) \<longrightarrow>
          rgsep_safe n C s lh sh R G (RGstar Q (RGlocal q))"
    and a8: "(s, lh, sh) \<^sup>\<Turnstile>rgsep P"
    and a9: "(s, sh r) \<Turnstile> p"
    and a10: "disjoint (fvA p) (wrC C)"
  then show "rgsep_safe n (Cwith r B C) s lh sh R G (RGstar Q (RGshared r q))"
    apply (induct n arbitrary: sh, simp, clarsimp)
(* no abort *)
    apply (rule conjI, clarsimp, erule aborts.cases, simp_all)
(* rely *)
    apply (rule conjI, intro allI impI)
     apply (erule mall_imp2D, simp add: stable_def, blast)
     apply (metis empty_iff)
(* enter *)
    apply (intro allI impI)
    apply (erule red.cases, simp_all, clarsimp)
    apply (rule_tac x = "lh ++ sha r" in exI, simp)
    apply (rule_tac x = "sha" in exI, simp)
    apply (rule conjI, simp add: RGdef_def)
    apply (subgoal_tac " r \<notin> locked C") defer
    apply (simp add: user_cmdD)
    apply (drule_tac a = "n" and b = "s" and c = "lh ++ sha r" and d = "sha" in all4_impD, simp)
     apply (rule_tac x = "lh" in exI, simp, rule_tac x = "sha r" in exI, simp)
    apply auto[1]
    by (metis rule_with_skip)
qed

subsubsection {* Sequential composition *}  

lemma RGsafe_seq :
"\<lbrakk>rgsep_safe n C s h \<Gamma> Rely Guar Q; user_cmd C2;
  \<forall>m s' h' \<Gamma>'. m \<le> n \<and> (s', h', \<Gamma>')  \<^sup>\<Turnstile>rgsep  Q \<longrightarrow> rgsep_safe m C2 s' h' \<Gamma>' Rely Guar R \<rbrakk>
  \<Longrightarrow> rgsep_safe n (Cseq C C2) s h \<Gamma> Rely Guar R"
  apply (induct n arbitrary: C s h \<Gamma> Rely Guar Q, simp, clarsimp)
(* no abort *)
  apply (rule conjI, clarsimp)
   apply (erule aborts.cases, simp_all, clarsimp)
(* rely *)
  apply (rule conjI, clarsimp)
  apply (metis le_Suc_eq)
apply (clarsimp, erule red.cases, simp_all)
(* seq1 *)
   apply (rule_tac x = "h" in exI, simp)
   apply auto[1]
(* seq2 *)
  apply (clarify, drule (1) all4_impD, clarsimp)
  by (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)

definition Stable_State :: "rgsep_assn \<Rightarrow> RGstate \<Rightarrow> rely \<Rightarrow> bool"
  where " Stable_State P \<sigma> R = (
    \<forall>s h \<Gamma>. \<sigma> = (s, h, \<Gamma>) \<longrightarrow> (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<and> (
    \<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r))) 
    \<longrightarrow> (s, h, \<Gamma>') \<^sup>\<Turnstile>rgsep P
)
)"

lemma RGsafe_seq' :
"\<lbrakk>rgsep_safe n C s h \<Gamma> Rely Guar Q; user_cmd C2;
  \<forall>m s' h' \<Gamma>'. m \<le> n \<and> (s', h', \<Gamma>')  \<^sup>\<Turnstile>rgsep  Q \<and> (Stable_State Q (s', h', \<Gamma>') Rely) 
     \<longrightarrow> rgsep_safe m C2 s' h' \<Gamma>' Rely Guar R \<rbrakk>
  \<Longrightarrow> rgsep_safe n (Cseq C C2) s h \<Gamma> Rely Guar R"
  apply (induct n arbitrary: C s h \<Gamma> Q, simp, clarsimp)
(* no abort *)
  apply (rule conjI, clarsimp)
   apply (erule aborts.cases, simp_all, clarsimp)
(* rely *)
  apply (rule conjI, clarsimp)
  apply (metis le_Suc_eq)
apply (clarsimp, erule red.cases, simp_all)
(* seq1 *)
   apply (rule_tac x = "h" in exI, clarsimp)
   apply (rule_tac x = "\<Gamma>" in exI, simp)
  apply (case_tac n, simp, simp)
   apply (drule_tac a = "n" and b = "aa" and c = "h" and d = "\<Gamma>" in all4_impD)
    apply (simp add: Stable_State_def, clarsimp)
(* seq2 *)
  apply (clarify, drule (1) all4_impD, clarsimp)
  by (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)

theorem RGrule_seq:
" \<lbrakk>Rely , Guar  \<^sup>\<turnstile>rgsep {P} C1 {Q} ; Rely , Guar  \<^sup>\<turnstile>rgsep {Q} C2 {R} \<rbrakk>
  \<Longrightarrow> Rely , Guar  \<^sup>\<turnstile>rgsep {P} Cseq C1 C2 {R}
"
  by (auto simp add: RGSep_def intro!: RGsafe_seq)

subsubsection {* Conditionals (if-then-else) *}

lemma red_det_tau: " \<lbrakk>rgsep_safe n C' s' h \<Gamma> R G Q;
          \<forall>h. red C (s,h) C' (s', h);
          \<forall>h cn ss. red C (s,h) cn ss \<longrightarrow> cn = C' \<and> ss = (s', h);
          \<forall>h. \<not>aborts C (s, h);
          accesses C s = {};
          locked C =  locked C'
        \<rbrakk> \<Longrightarrow> rgsep_safe n C s h \<Gamma> R G Q
"
  apply (induct n arbitrary : h \<Gamma> R G Q, simp, clarsimp)
  apply (rule conjI) apply auto[1]
  apply (clarsimp)
  apply (subgoal_tac "b =  h ++ hplus_list (map \<Gamma> (list_minus (llocked C'a) (llocked C))) ++ hF")
   defer apply (simp)
  apply (rule_tac x = "h" and y = "\<Gamma>" in ex2I, clarsimp)
  apply (subgoal_tac " list_minus (llocked C'a) (llocked C) = list_minus (llocked C) (llocked C'a)")
   defer apply (simp add: list_minus_reverse locked_eq)
  apply (simp)
  done

theorem "\<lbrakk>R,G \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure B))} C1 {Q};
          R,G \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure (Bnot B)))} C2 {Q}\<rbrakk>
        \<Longrightarrow> R,G \<^sup>\<turnstile>rgsep {P} Cif B C1 C2 {Q}"
  apply (clarsimp simp add: RGSep_def)
  apply (case_tac "bdenot B s = True")
   apply (drule all4_impD, simp, clarsimp)
   apply (erule red_det_tau)
        apply (simp add: red_If1)
       apply(intro allI  impI, erule red.cases, simp_all)
      apply auto[1]
     apply(intro allI notI, erule aborts.cases, simp_all)
   apply (simp add: user_cmdD)
  apply (subgoal_tac "rgsep_safe n C2 s h \<Gamma> R G Q")
   defer  apply blast
  apply ( erule red_det_tau)
        apply (simp add: red_If2)
       apply(intro allI  impI, erule red.cases, simp_all)
      apply auto[1]
     apply(intro allI notI, erule aborts.cases, simp_all)
  apply (simp add: user_cmdD)
  done

subsubsection {* While *}

lemma stable_local: "stable (RGlocal P) exn R"
  by (simp add: stable_def)

lemma stable_conj : "stable P exn R \<Longrightarrow> stable Q exn R \<Longrightarrow> stable (RGconj P Q) exn R"
  apply (simp add: stable_def, clarsimp)
  done

lemma RGsafe_while:
  "\<lbrakk> R,G \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure B))} C {P} ; (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P ; stable P [] R\<rbrakk>
  \<Longrightarrow> rgsep_safe n (Cwhile B C) s h \<Gamma> R G (RGconj P (RGlocal (Apure (Bnot B))))"
  apply (induct n arbitrary: s h \<Gamma> R G, simp, clarsimp)
(* no aborts *)
  apply (intro conjI allI impI notI, erule aborts.cases, simp_all)
(* rely *)
   apply (drule_tac a = "s" and b = "h" and c = "\<Gamma>'" and d = "R" and e = "G" in mall5_impD, simp)
   apply (drule mimp2D, simp_all, simp add: stable_def) apply blast
(* while *)
  apply ( erule red.cases, simp_all)
  apply (clarsimp, intro exI, (rule conjI, simp)+)
  apply (rule_tac x = "\<Gamma>" in exI)
  apply (rule conjI) apply simp
  apply (rule conjI) apply simp
  apply (case_tac "bdenot B aa = True")
  apply (subgoal_tac "rgsep_safe n (Cseq C (Cwhile B C)) aa h \<Gamma> R G (RGconj P (RGlocal (Apure (Bnot B))))")
    apply (erule red_det_tau)
        apply (simp add: red_If1)
       apply (intro allI impI, erule red.cases, simp_all, clarsimp)
      apply auto[1]
     apply(intro allI notI, erule aborts.cases, simp_all)
  using RGSep_def user_cmdD apply blast
   apply (rule_tac Q = "P" in RGsafe_seq)
   apply (simp add: RGSep_def, clarsimp)
  using RGSep_def apply blast
   apply (intro allI impI, rule_tac n = "n" in RGsafe_mon, simp_all)
  apply (subgoal_tac "rgsep_safe n Cskip aa h \<Gamma> R G (RGconj P (RGlocal (Apure (Bnot B))))")
   apply (erule red_det_tau)
       apply (simp add: red_If2)
       apply (intro allI impI, erule red.cases, simp_all, clarsimp)
   apply auto[1]
   apply (erule aborts.cases, simp_all)
  apply (rule RGsafe_skip, simp)
  apply (rule stable_conj, simp)
  by (rule stable_local)

theorem RGrule_while: 
  "\<lbrakk>R,G \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure B))} C {P};
    stable P [] R\<rbrakk> 
    \<Longrightarrow> R,G \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure B))} (Cwhile B C) {RGconj P (RGlocal (Apure (Bnot B)))}"
  by (simp add: RGSep_def RGsafe_while)

subsubsection {* Simple structural rules (Conseq, Disj, Ex) *}

definition RGsubset :: "rely \<Rightarrow> rely \<Rightarrow> bool" (infixl "\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p" 60)
  where
" R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G \<equiv> \<forall>r. R r \<subseteq> G r"

lemma RGsafe_conseq: "
  \<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_safe n C s h \<Gamma> R G Q\<rbrakk> \<Longrightarrow> rgsep_safe n C s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: C s h \<Gamma>, simp, clarsimp)
(* skip *)
  apply (rule conjI) 
  apply (simp add: rgsep_implies_def)
(*rely *)
  apply (rule conjI)
   apply (intro allI impI)
   apply (subgoal_tac "rgsep_safe n C s h \<Gamma>' R G Q", simp_all)
  apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all4_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
  using RGsubset_def by blast

theorem RGrule_conseq: "
  \<lbrakk> R,G \<^sup>\<turnstile>rgsep {P} C {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>rgsep {P'} C {Q'}   
"
  apply (simp add: RGSep_def)
  apply (intro allI impI)
  apply (rule_tac R = "R" and G = "G" and Q = "Q" in RGsafe_conseq)
     apply (simp_all add: rgsep_implies_def)
  done

theorem RGrule_disj:
  "\<lbrakk> R,G \<^sup>\<turnstile>rgsep {P1} C {Q1};
     R,G \<^sup>\<turnstile>rgsep {P2} C {Q2}\<rbrakk>
   \<Longrightarrow> R,G \<^sup>\<turnstile>rgsep {RGdisj P1 P2} C {RGdisj Q1 Q2}"
  apply (simp add: RGSep_def)
  apply (intro allI)
  apply (rule conjI, intro impI)
   apply (rule_tac R = "R" and G = "G" and Q = "Q1" in RGsafe_conseq, simp_all add: rgsep_implies_def RGsubset_def)
  apply (intro impI)
  apply (rule_tac R = "R" and G = "G" and Q = "Q2" in RGsafe_conseq, simp_all add: rgsep_implies_def RGsubset_def)
  done




end



