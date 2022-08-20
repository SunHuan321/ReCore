theory Event_RGsafe
  imports RGSepSound test
begin

primrec
  rgsep_esafe :: "nat \<Rightarrow> event \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"
where
  "rgsep_esafe 0 e s h \<Gamma> R G Q = True"
| "rgsep_esafe (Suc n) e s h \<Gamma> R G Q = (
(* Condition (i) *)
            (e = AnonyEvent Cskip \<longrightarrow> (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Q)
(* Conditon (ii) *)
          \<and> (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> eaborts e (s, h ++ hF))
(* Condition (iii) *)
          \<and> eaccesses e s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
                    \<longrightarrow> (r \<notin> elocked e) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
                    \<longrightarrow> rgsep_esafe n e s h \<Gamma>' R G Q)
(* Condition (v) *)
          \<and> (\<forall>hJ hF e' \<sigma>'.
                ered e (s,h ++ hJ ++ hF) e' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (ellocked e') (ellocked e)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (ellocked e') (ellocked e)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (elocked e') \<and> (r \<notin> elocked e) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (ellocked e) (ellocked e'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (ellocked e) (ellocked e')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (elocked e) \<and> r \<notin> (elocked e') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (elocked e) \<and> r \<notin> (elocked e') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (elocked e) \<or> r \<in> (elocked e') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_esafe n e' (fst \<sigma>') h' \<Gamma>' R G Q)
)))"

lemma RGesafe_agrees: 
  "\<lbrakk> rgsep_esafe n e s h \<Gamma> R G Q ; 
     agrees (fvEv e \<union> fvAA Q) s s' \<rbrakk>
   \<Longrightarrow> rgsep_esafe n e s' h \<Gamma> R G Q"
  apply (induct n arbitrary: e s s' h \<Gamma> R G, simp, simp only: rgsep_esafe.simps, clarify)
  apply (rule conjI)
  using RGassn_agrees apply auto[1]
  apply (rule conjI)
   apply (metis agrees_search(1) agrees_simps(4) eaborts_agrees snd_conv snd_swap swap_simp)
  apply (rule conjI, subst (asm) eaccesses_agrees, simp_all)
  apply (rule conjI, blast)
  apply (clarify, drule_tac X="fvEv e \<union> fvAA Q" in ered_agrees, 
         simp (no_asm), fast, simp (no_asm), fast, clarify)
  apply (drule (1) all4_impD, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  by (meson agrees_search(1) agrees_search(3) ered_properties)

definition
    eRGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> event \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>ergsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>ergsep {P} e {Q} \<equiv> (user_event e \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P
                         \<longrightarrow> rgsep_esafe n e s h \<Gamma> R G Q))" 

lemma RGesafe_AnonyEvt: "rgsep_safe n C s h \<Gamma> R G Q \<Longrightarrow> rgsep_esafe n (AnonyEvent C) s h \<Gamma> R G Q"
  apply (induct n arbitrary: C s h \<Gamma>, simp_all, clarify)
  apply (rule conjI)
   apply (clarsimp, erule eaborts.cases, simp_all)
   apply (drule_tac a = "hF" in all_impD, simp_all)
  apply (clarsimp, erule ered.cases, simp_all)
  apply (drule_tac a = "hF" and b = "C'" and c = "a" and d = "b"  in all4_impD, simp)
  apply (drule imp2D, simp_all)
  by blast

theorem RGrule_Inner: "R,G  \<^sup>\<turnstile>rgsep {P} C {Q} \<Longrightarrow> R,G  \<^sup>\<turnstile>ergsep {P} (AnonyEvent C) {Q}"
  by (simp add: eRGSep_def RGSep_def RGesafe_AnonyEvt)

theorem RGrule_BasicEvt: "\<lbrakk> R,G  \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure guard))} C {Q};
                            stable P [] R\<rbrakk>
                    \<Longrightarrow> R,G  \<^sup>\<turnstile>ergsep {P} (BasicEvent (guard, C)) {Q}"
  apply (simp add: eRGSep_def RGSep_def, clarsimp)
proof-
  fix n s h \<Gamma>
  assume a0: " stable P [] R"
  and    a1: "user_cmd C"
  and    a2: "\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<and> bdenot guard s \<longrightarrow> rgsep_safe n C s h \<Gamma> R G Q"
  and    a3: "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_esafe n (BasicEvent (guard, C)) s h \<Gamma> R G Q"
    apply (induct n arbitrary: C s h \<Gamma>, simp, simp)
(* no aborts *)    
    apply (rule conjI, clarsimp)
     apply(erule eaborts.cases, simp_all)
(* rely *)
    apply (rule conjI, simp add: stable_def, clarify)
     apply metis
(* step *)
    apply (clarsimp, erule ered.cases, simp, clarsimp)
    apply (rule_tac x = "ha" in exI, clarsimp)
    apply (rule_tac x = "\<Gamma>'" in exI, clarsimp)
    by (simp add: RGesafe_AnonyEvt)
qed

lemma RGesafe_conseq: " \<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_esafe n e s h \<Gamma> R G Q\<rbrakk> 
    \<Longrightarrow> rgsep_esafe n e s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: e s h \<Gamma>, simp, clarsimp)
(* skip *)
  apply (rule conjI) 
  apply (simp add: rgsep_implies_def)
(*rely *)
  apply (rule conjI)
   apply (intro allI impI)
   apply (subgoal_tac "rgsep_esafe n e s h \<Gamma>' R G Q", simp_all)
  apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all4_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
  by (meson RGsubset_def contra_subsetD)

theorem RGrule_EvtConseq : "
  \<lbrakk> R,G \<^sup>\<turnstile>ergsep {P} e {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>ergsep {P'} e {Q'}"
  by (simp add: eRGSep_def rgsep_implies_def RGesafe_conseq)

primrec
  rgsep_resafe :: "nat \<Rightarrow> revent \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"
where
  "rgsep_resafe 0 re s h \<Gamma> R G Q = True"
| "rgsep_resafe (Suc n) re s h \<Gamma> R G Q = (
(* Condition (i) *)
            (snd re = AnonyEvent Cskip \<longrightarrow> (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Q)
(* Conditon (ii) *)
          \<and> (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> reaborts re (s, h ++ hF))
(* Condition (iii) *)
          \<and> reaccesses re s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
                    \<longrightarrow> (r \<notin> relocked re) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
                    \<longrightarrow> rgsep_resafe n re s h \<Gamma>' R G Q)
(* Condition (v) *)
          \<and> (\<forall>hJ hF re' \<sigma>'.
                rered re (s,h ++ hJ ++ hF) re' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (rellocked re') (rellocked re)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (rellocked re') (rellocked re)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (relocked re') \<and> (r \<notin> relocked re) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (rellocked re) (rellocked re'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (rellocked re) (rellocked re')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (relocked re) \<and> r \<notin> (relocked re') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (relocked re) \<and> r \<notin> (relocked re') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (relocked re) \<or> r \<in> (relocked re') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_resafe n re' (fst \<sigma>') h' \<Gamma>' R G Q)
)))"


lemma RGresafe_agrees: 
  "\<lbrakk> rgsep_resafe n re s h \<Gamma> R G Q ; 
     agrees (fvREv re \<union> fvAA Q) s s' \<rbrakk>
   \<Longrightarrow> rgsep_resafe n re s' h \<Gamma> R G Q"
  apply (induct n arbitrary: re s s' h \<Gamma> R G, simp, simp only: rgsep_resafe.simps, clarify)
  apply (rule conjI)
  using RGassn_agrees apply auto[1]
  apply (rule conjI)
  apply (metis agrees_search(1) agrees_simps(4) fst_conv reaborts_agrees snd_conv)
  apply (rule conjI, subst (asm) reaccesses_agrees, simp_all)
  apply (rule conjI, blast)
  apply (clarify, drule_tac X="fvREv (a,b)  \<union> fvAA Q" in rered_agrees, 
         simp (no_asm), fast, simp (no_asm), fast, clarify)
  apply (drule (1) all5_impD, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  by (meson agrees_search(1) agrees_search(3) rered_properties)

definition
    reRGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> revent \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>rergsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>rergsep {P} re {Q} \<equiv> (user_revent re \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P
                         \<longrightarrow> rgsep_resafe n re s h \<Gamma> R G Q))" 

lemma RGresafe_rAnonyEvt: "rgsep_safe n C s h \<Gamma> R G Q \<Longrightarrow> rgsep_resafe n (rs, AnonyEvent C) s h \<Gamma> R G Q"
  apply (induct n arbitrary: C s h \<Gamma>, simp_all)
  apply (rule conjI,simp add: reaborts_def, clarify)
   apply (erule eaborts.cases, simp_all)
  apply auto[1]
  apply (rule conjI, simp add: reaccesses_def)
  apply (rule conjI, simp add: relocked_def)
  apply (clarify, erule rered.cases, simp_all, clarify)
  apply (drule_tac a = "hF" and b = "C'" and c = "ac" and d = "bc"in all4_impD, simp add: rellocked_def)
  apply (drule imp3D, simp, simp add: rellocked_def, simp add: relocked_def, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp add: rellocked_def, simp add: relocked_def)
  done

theorem RGrule_rInner: "R,G  \<^sup>\<turnstile>rgsep {P} C {Q} \<Longrightarrow> R,G  \<^sup>\<turnstile>rergsep {P} (rs, AnonyEvent C) {Q}"
  apply (simp add: reRGSep_def RGSep_def RGesafe_AnonyEvt)
  by (simp add: RGresafe_rAnonyEvt user_revent_def)

theorem RGrule_rBasicEvt: "\<lbrakk> R,G  \<^sup>\<turnstile>rgsep {RGconj P (RGlocal (Apure guard))} (Cresources rs C) {Q};
                            stable P [] R\<rbrakk>
                    \<Longrightarrow> R,G  \<^sup>\<turnstile>rergsep {P} (rs, BasicEvent (guard, C)) {Q}"
  apply (simp add: reRGSep_def RGSep_def, simp add: user_revent_def, clarify)
proof-
  fix n s h \<Gamma>
  assume a0: " stable P [] R"
  and    a1: "user_cmd C"
  and    a2: "\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<and> bdenot guard s 
                  \<longrightarrow> rgsep_safe n (Cresources rs C) s h \<Gamma> R G Q"
  and    a3: "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_resafe n (rs, BasicEvent (guard, C)) s h \<Gamma> R G Q"
    apply (induct n arbitrary: C s h \<Gamma>, simp, simp)
(* no aborts *)    
    apply (rule conjI, simp add: reaborts_def, clarify)
     apply(erule eaborts.cases, simp_all)
(* access *)
    apply (rule conjI, simp add: stable_def, clarify)
    using reaccesses_def apply auto[1]
(* rely *)
     apply (rule conjI, simp add: stable_def, clarify)
     apply metis
(* step *)
    apply (clarify, erule rered.cases, simp, clarsimp)
    apply (rule_tac x = "ha" in exI, clarsimp)
    apply (rule_tac x = "\<Gamma>'" in exI, clarsimp)
    by (simp add: RGresafe_rAnonyEvt elocked_eq rellocked_def relocked_def)
qed

lemma RGresafe_conseq: " \<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_resafe n re s h \<Gamma> R G Q\<rbrakk> 
    \<Longrightarrow> rgsep_resafe n re s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: re s h \<Gamma>, simp, clarsimp)
(* skip *)
  apply (rule conjI) 
  apply (simp add: rgsep_implies_def)
(*rely *)
  apply (rule conjI)
   apply (intro allI impI)
   apply (subgoal_tac "rgsep_resafe n (a, b) s h \<Gamma>' R G Q", simp)
    apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all5_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp add: relocked_def)
  by (meson RGsubset_def contra_subsetD)

theorem RGrule_rEvtConseq : "
  \<lbrakk> R,G \<^sup>\<turnstile>rergsep {P} re {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>rergsep {P'} re {Q'}"
  by (simp add: reRGSep_def rgsep_implies_def RGresafe_conseq)


primrec
  rgsep_essafe :: "nat \<Rightarrow> esys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"
where
  "rgsep_essafe 0 es s h \<Gamma> R G Q = True"
| "rgsep_essafe (Suc n) es s h \<Gamma> R G Q = (
(* Conditon (ii) *)
           (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> esaborts es (s, h ++ hF))
(* Condition (iii) *)
          \<and> esaccesses es s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
                    \<longrightarrow> (r \<notin> eslocked es) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
                    \<longrightarrow> rgsep_essafe n es s h \<Gamma>' R G Q)
(* Condition (v) *)
          \<and> (\<forall>hJ hF es' \<sigma>'.
                esred es (s,h ++ hJ ++ hF) es' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (esllocked es') (esllocked es)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (esllocked es') (esllocked es)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (eslocked es') \<and> (r \<notin> eslocked es) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (esllocked es) (esllocked es'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (esllocked es) (esllocked es')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (eslocked es) \<and> r \<notin> (eslocked es') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (eslocked es) \<and> r \<notin> (eslocked es') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (eslocked es) \<or> r \<in> (eslocked es') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_essafe n es' (fst \<sigma>') h' \<Gamma>' R G Q)
)))"

lemma RGessafe_agrees: 
  "\<lbrakk> rgsep_essafe n es s h \<Gamma> R G Q ; 
     agrees (fvEsv es \<union> fvAA Q) s s' \<rbrakk>
   \<Longrightarrow> rgsep_essafe n es s' h \<Gamma> R G Q"
  apply (induct n arbitrary: es s s' h \<Gamma> R G, simp, simp only: rgsep_essafe.simps, clarify)
  apply (rule conjI)
   apply (metis agrees_search(1) agrees_simps(4) esaborts_agrees snd_conv snd_swap swap_simp)
  apply (rule conjI, subst (asm) esaccesses_agrees, simp_all)
  apply (rule conjI, blast)
  apply (clarify, drule_tac X="fvEsv es \<union> fvAA Q" in esred_agrees, 
         simp (no_asm), fast, simp (no_asm), fast, clarify)
  apply (drule (1) all4_impD, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  by (meson agrees_search(1) agrees_search(3) esred_properties)

lemma RGessafe_mon:
  "\<lbrakk> rgsep_essafe n es s h \<Gamma> R G Q; m \<le> n \<rbrakk> \<Longrightarrow> rgsep_essafe m es s h \<Gamma> R G Q"
apply (induct m arbitrary: es n s h \<Gamma>, simp) 
apply (case_tac n, clarify)
  apply (simp only: rgsep_essafe.simps, clarsimp)
  apply (rule conjI, clarsimp) apply blast
  apply (clarsimp, drule_tac a = "hF" and b = "es'" and c = "a" and d = "b" in all4_impD, simp)
  apply (drule imp3D, simp_all, clarify)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  done

definition
    esRGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> esys \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>esrgsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>esrgsep {P} es {Q} \<equiv> (user_esys es \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P
                         \<longrightarrow> rgsep_essafe n es s h \<Gamma> R G Q))" 


lemma RGessafe_EvtSeq :"\<lbrakk>rgsep_resafe n re s h \<Gamma> Rely Guar Q; user_esys esys;
      \<forall>m s' h' \<Gamma>. m \<le> n \<and> (s', h', \<Gamma>) \<^sup>\<Turnstile>rgsep Q \<longrightarrow> rgsep_essafe m esys s' h' \<Gamma> Rely Guar R\<rbrakk> 
      \<Longrightarrow>  rgsep_essafe n (EvtSeq re esys) s h \<Gamma> Rely Guar R"
  apply (induct n arbitrary: re s h \<Gamma>, simp, clarsimp)
  apply (rule conjI, clarsimp)
   apply (erule esaborts.cases, simp_all, clarsimp)
  apply (clarsimp, erule esred.cases, simp_all)
  apply (drule_tac a = "hF" and b = "fst re'" and c = "snd re'" 
          and d = "aa" and e = "ba" in all5_impD, simp)
   apply (drule imp3D, simp_all, clarify)
   apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp, clarify)
  apply (rule_tac x = "h" and y = "\<Gamma>" in ex2I, simp add:rellocked_def)
  apply (rule conjI,simp add: user_reventD user_revent_def)
  by (simp add: relocked_def)

theorem rule_rEvtSeq :"\<lbrakk>Rely ,Guar  \<^sup>\<turnstile>rergsep {P} re {Q};
                 Rely , Guar \<^sup>\<turnstile>esrgsep { Q } esys { R }\<rbrakk> 
                \<Longrightarrow> Rely , Guar \<^sup>\<turnstile>esrgsep {P} (EvtSeq re esys) {R}"
  apply (simp add: reRGSep_def esRGSep_def )
  by (meson RGessafe_EvtSeq)

lemma RGessafe_conseq : "\<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_essafe n es s h \<Gamma> R G Q\<rbrakk> 
    \<Longrightarrow> rgsep_essafe n es s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: es s h \<Gamma>, simp, clarsimp)
  apply (rule conjI)
  apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all4_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
  by (meson RGsubset_def contra_subsetD)

theorem RGrule_esconseq : "
  \<lbrakk> R,G \<^sup>\<turnstile>esrgsep {P} es {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>esrgsep {P'} es {Q'}"
  by (simp add: esRGSep_def rgsep_implies_def RGessafe_conseq)

lemma Rely_Stable : "R' \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R \<Longrightarrow> stable P [] R \<Longrightarrow> stable P [] R'"
  apply (simp add: stable_def RGsubset_def, clarsimp)
  apply (drule_tac a = "s" and b = "h" and c = "\<Gamma>" in all3D, clarsimp)
  by (meson set_rev_mp)

theorem rule_EvtSys :  "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep {Pre re} re {Post re};
                          \<forall>re \<in> es.  P \<^sup>\<sqsubseteq>rgsep Pre re;
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          stable P [] R;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
                        \<Longrightarrow> R, G \<^sup>\<turnstile>esrgsep {P} (EvtSys es) {Q}"
  apply (simp add: esRGSep_def reRGSep_def, clarsimp)
proof-
  fix n s h \<Gamma>
  assume a0: " \<forall>re\<in>es.
          user_revent re \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Pre re \<longrightarrow> rgsep_resafe n re s h \<Gamma> (Rely re) (Guar re) (Post re))"
  and    a1: "\<forall>re\<in>es. P \<^sup>\<sqsubseteq>rgsep Pre re"
  and    a2: " \<forall>re\<in>es. Post re \<^sup>\<sqsubseteq>rgsep Q"
  and    a3: "\<forall>re\<in>es. R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re"
  and    a4: "\<forall>re\<in>es. Guar re \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  and    a5: "stable P [] R"
  and    a6: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a7: "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma> P, simp, simp)
    apply (rule conjI, simp add: esaborts.simps)
    apply (rule conjI, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" and d = "Pa" in mall4_impD, simp_all)
      apply (simp add: stable_def) apply metis 
    apply (clarsimp, erule esred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (subgoal_tac "user_event ba") 
     apply (rule_tac x = "ha" in exI, clarsimp)
     apply (rule_tac x = "\<Gamma>'" in exI, simp)
     apply (rule_tac Q = "Post (aa, ba)" in RGessafe_EvtSeq)
       apply (subgoal_tac "rgsep_resafe n (aa, ba) ab ha \<Gamma>' 
                            (Rely (aa, ba)) (Guar (aa, ba)) (Post (aa, ba))")
        apply (meson RGresafe_conseq rgsep_implies_def)
       apply (subgoal_tac "(ab, ha, \<Gamma>') \<^sup>\<Turnstile>rgsep Pre (aa, ba)")
        apply blast
       apply (simp add: rgsep_implies_def)
      apply (simp add: a0, clarsimp)
     apply (drule_tac a = "s'" and b = "h'" and c = "\<Gamma>''" and d = "Post(aa, ba)" in mall4_impD, clarify)
    apply(drule_tac a = "aa" and b = "ba" and c = "a" and d = "b" in all4_impD, simp, simp)
     apply (drule mimp2D) 
       apply (rule_tac R = "Rely (aa, ba)" in Rely_Stable, simp)
    oops   



(*
definition RG_get_int_pre :: "RGstate \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> rgsep_assn) \<Rightarrow> bool"
  where "RG_get_int_pre \<sigma> es Pre \<equiv> \<forall> re \<in> es.  \<sigma> \<^sup>\<Turnstile>rgsep (Pre re)" 

definition RG_get_union_post :: "RGstate \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> rgsep_assn) \<Rightarrow> bool"
  where "RG_get_union_post \<sigma> es Post \<equiv>  \<exists>re \<in> es. \<sigma> \<^sup>\<Turnstile>rgsep (Post re)" 

lemma RG_pre_conj : "\<lbrakk> \<forall>re \<in> es. P \<^sup>\<sqsubseteq>rgsep (Pre re) ; \<sigma> \<^sup>\<Turnstile>rgsep P \<rbrakk> \<Longrightarrow> RG_get_int_pre \<sigma> es Pre"
  using RG_get_int_pre_def rgsep_implies_def by blast

lemma RG_post_dconj : "\<lbrakk>\<forall>re\<in>es. (Post re) \<^sup>\<sqsubseteq>rgsep Q; RG_get_union_post \<sigma> es Post\<rbrakk> \<Longrightarrow> \<sigma> \<^sup>\<Turnstile>rgsep Q"
  using RG_get_union_post_def rgsep_implies_def by blast

lemma RGessafe_EvtSys :  "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep {Pre re} re {Post re};
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          \<forall>s h \<Gamma>.
          RG_get_int_pre (s, h, \<Gamma>) es Pre \<longrightarrow>
          (\<forall>\<Gamma>'. (\<forall>r. (\<Gamma> r, \<Gamma>' r) \<in> R r \<or> \<Gamma> r = \<Gamma>' r) \<longrightarrow>
                 (\<forall>r. disjoint (dom h) (dom (\<Gamma>' r)) \<or> \<Gamma> r = \<Gamma>' r) \<longrightarrow> RG_get_int_pre (s, h, \<Gamma>') es Pre);
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk> 
                    \<Longrightarrow>   \<forall>n s h. RG_get_int_pre (s, h, \<Gamma>) es Pre
                            \<longrightarrow> rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
  apply (simp add: reRGSep_def, clarsimp)
proof-
  fix n s h 
  assume a0: " \<forall>re\<in>es.
          user_revent re \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Pre re \<longrightarrow> rgsep_resafe n re s h \<Gamma> (Rely re) (Guar re) (Post re))"
  and    a2: " \<forall>re\<in>es. Post re \<^sup>\<sqsubseteq>rgsep Q"
  and    a3: "\<forall>re\<in>es. R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re"
  and    a4: "\<forall>re\<in>es. Guar re \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  and    a5: "\<forall>s h \<Gamma>.
          RG_get_int_pre (s, h, \<Gamma>) es Pre \<longrightarrow>
          (\<forall>\<Gamma>'. (\<forall>r. (\<Gamma> r, \<Gamma>' r) \<in> R r \<or> \<Gamma> r = \<Gamma>' r) \<longrightarrow>
                 (\<forall>r. disjoint (dom h) (dom (\<Gamma>' r)) \<or> \<Gamma> r = \<Gamma>' r) \<longrightarrow> RG_get_int_pre (s, h, \<Gamma>') es Pre)"
  and    a6: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a7: "RG_get_int_pre (s, h, \<Gamma>) es Pre"
  then show "rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma>, simp, simp)
    apply (rule conjI, simp add: esaborts.simps)
    apply (rule conjI, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" in mall3_impD, simp_all)
     apply blast
    apply (clarsimp, erule esred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (subgoal_tac "user_event ba") 
     apply (rule_tac x = "ha" in exI, clarsimp)
     apply (rule_tac x = "\<Gamma>'" in exI, simp)
     apply (rule_tac Q = "Post (aa, ba)" in RGessafe_EvtSeq)
       apply (subgoal_tac "rgsep_resafe n (aa, ba) ab ha \<Gamma>' 
                            (Rely (aa, ba)) (Guar (aa, ba)) (Post (aa, ba))")
        apply (meson RGresafe_conseq rgsep_implies_def)
       apply (subgoal_tac "(ab, ha, \<Gamma>') \<^sup>\<Turnstile>rgsep Pre (aa, ba)")
        apply blast
       apply (simp add: rgsep_implies_def)
    apply (simp add: RG_get_int_pre_def)
      apply (simp add: a0, clarsimp)
     apply (drule_tac a = "s'" and b = "h'" and c = "\<Gamma>''" in mall3_impD) 
    using RG_get_int_pre_def rgsep_implies_def apply force
     apply (simp add: RGessafe_mon)
    by auto
qed

lemma "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep {Pre re} re {Post re};                         
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
         \<Longrightarrow> \<forall>P n s h \<Gamma>.  (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P \<longrightarrow> stable P [] R 
                        \<longrightarrow>  (\<forall>re \<in> es.  P \<^sup>\<sqsubseteq>rgsep Pre re) \<longrightarrow>
                            rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
proof(simp add: reRGSep_def, clarify)
  fix P n s h \<Gamma>
  assume a0: "\<forall>re\<in>es.  user_revent re \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Pre re
                   \<longrightarrow> rgsep_resafe n re s h \<Gamma> (Rely re) (Guar re) (Post re))"
  and    a1: "\<forall>re\<in>es. P \<^sup>\<sqsubseteq>rgsep Pre re"
  and    a2: " \<forall>re\<in>es. Post re \<^sup>\<sqsubseteq>rgsep Q"
  and    a3: "\<forall>re\<in>es. R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re"
  and    a4: "\<forall>re\<in>es. Guar re \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  and    a5: "stable P [] R"
  and    a6: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a7: "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma> P, simp, simp)
    apply (rule conjI, simp add: esaborts.simps)
    apply (rule conjI, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" in mall3_impD, simp_all)
      apply (simp add: stable_def) apply blast
    apply (clarsimp, erule esred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (subgoal_tac "user_event ba") 
     apply (rule_tac x = "ha" in exI, clarsimp)
     apply (rule_tac x = "\<Gamma>'" in exI, simp)
     apply (rule_tac Q = "Post (aa, ba)" in RGessafe_EvtSeq)
       apply (subgoal_tac "rgsep_resafe n (aa, ba) ab ha \<Gamma>' 
                            (Rely (aa, ba)) (Guar (aa, ba)) (Post (aa, ba))")
        apply (meson RGresafe_conseq rgsep_implies_def)
       apply (subgoal_tac "(ab, ha, \<Gamma>') \<^sup>\<Turnstile>rgsep Pre (aa, ba)")
        apply blast
       apply (simp add: rgsep_implies_def)
      apply (simp add: a0, clarsimp)
     apply (drule_tac a = "s'" and b = "h'" and c = "\<Gamma>''" in mall3_impD)

*)