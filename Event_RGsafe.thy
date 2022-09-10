theory Event_RGsafe
  imports RGSepSound Event_Helper
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
  apply (rule conjI,simp add: reaborts_equiv, clarify)
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
    apply (rule conjI, simp add: reaborts_equiv, clarify)
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
    by (metis RGresafe_rAnonyEvt ellocked.simps(1) ellocked.simps(2) elocked_eq 
        rellocked_def relocked_def snd_conv user_cmd.simps(14) user_cmd_llocked)
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
      \<forall>m s' h' \<Gamma>'. m \<le> n \<and> (s', h', \<Gamma>') \<^sup>\<Turnstile>rgsep Q \<longrightarrow> rgsep_essafe m esys s' h' \<Gamma>' Rely Guar R\<rbrakk> 
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

lemma RGessafe_EvtSeq' :"\<lbrakk>rgsep_resafe n re s h \<Gamma> Rely Guar Q; user_esys esys;
       \<forall>m s' h' \<Gamma>'. m \<le> n \<and> (s', h', \<Gamma>')  \<^sup>\<Turnstile>rgsep  Q \<and> (Stable_State Q (s', h', \<Gamma>') Rely) 
      \<longrightarrow> rgsep_essafe m esys s' h' \<Gamma>' Rely Guar R\<rbrakk> 
      \<Longrightarrow>  rgsep_essafe n (EvtSeq re esys) s h \<Gamma> Rely Guar R"
  apply (induct n arbitrary: re s h \<Gamma>, simp, clarsimp)
  apply (rule conjI, clarsimp)
   apply (erule esaborts.cases, simp_all, clarsimp)
  apply (clarsimp, erule esred.cases, simp_all)
  apply (drule_tac a = "hF" and b = "fst re'" and c = "snd re'" 
          and d = "aa" and e = "ba" in all5_impD, simp)
   apply (drule imp3D, simp_all, clarify)
   apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  apply (rule_tac x = "h" and y = "\<Gamma>" in ex2I, simp add:rellocked_def, clarsimp)
  apply (rule conjI,simp add: user_reventD user_revent_def)
  apply (simp add: relocked_def)
  apply (case_tac n, simp, simp)
  apply (drule_tac a = "n" and b = "ac" and c = "h" and d = "\<Gamma>" in all4_impD)
   apply (simp add: Stable_State_def, simp)
  done

theorem RGrule_EvtSeq :"\<lbrakk>Rely ,Guar  \<^sup>\<turnstile>rergsep {P} re {Q};
                 Rely , Guar \<^sup>\<turnstile>esrgsep { Q } esys { R }\<rbrakk> 
                \<Longrightarrow> Rely , Guar \<^sup>\<turnstile>esrgsep {P} (EvtSeq re esys) {R}"
  apply (simp add: reRGSep_def esRGSep_def )
  by (meson RGessafe_EvtSeq)

lemma Rely_Stable : "R' \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R \<Longrightarrow> stable P [] R \<Longrightarrow> stable P [] R'"
  apply (simp add: stable_def RGsubset_def, clarsimp)
  apply (drule_tac a = "s" and b = "h" and c = "\<Gamma>" in all3D, clarsimp)
  by (meson set_rev_mp)

definition RG_get_int_pre :: "RGstate \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> rgsep_assn) \<Rightarrow> bool"
  where "RG_get_int_pre \<sigma> es Pre \<equiv> \<forall> re \<in> es.  \<sigma> \<^sup>\<Turnstile>rgsep (Pre re)" 

definition RG_get_union_post :: "RGstate \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> rgsep_assn) \<Rightarrow> bool"
  where "RG_get_union_post \<sigma> es Post \<equiv>  \<exists>re \<in> es. \<sigma> \<^sup>\<Turnstile>rgsep (Post re)" 

lemma RG_pre_conj : "\<lbrakk> \<forall>re \<in> es. P \<^sup>\<sqsubseteq>rgsep (Pre re) ; \<sigma> \<^sup>\<Turnstile>rgsep P \<rbrakk> \<Longrightarrow> RG_get_int_pre \<sigma> es Pre"
  using RG_get_int_pre_def rgsep_implies_def by blast

lemma post_dconj : "\<lbrakk>\<forall>re\<in>es. (Post re) \<^sup>\<sqsubseteq>rgsep Q; RG_get_union_post \<sigma> es Post\<rbrakk> \<Longrightarrow> \<sigma> \<^sup>\<Turnstile>rgsep Q"
  using RG_get_union_post_def rgsep_implies_def by blast

definition RG_stable_getintpre :: "RGstate \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> rgsep_assn) \<Rightarrow> rely \<Rightarrow>  bool"
  where "RG_stable_getintpre \<sigma> es Pre R \<equiv>  \<forall>s h \<Gamma> re. \<sigma> = (s, h, \<Gamma>) \<longrightarrow> re \<in> es \<longrightarrow> 
        (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep (Pre re) \<and> ( \<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
    \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r))) 
    \<longrightarrow> (s, h, \<Gamma>') \<^sup>\<Turnstile>rgsep (Pre re)
)"

definition Rely_Trans :: "rely \<Rightarrow> bool"
  where "Rely_Trans R \<equiv> \<forall>r. trans (R r)"

lemma Stable_Property1 : " \<forall>re\<in>es. P \<^sup>\<sqsubseteq>rgsep Pre re \<Longrightarrow> Stable_State P \<sigma> R \<Longrightarrow>
      RG_stable_getintpre \<sigma> es Pre R"
  apply (simp add: RG_stable_getintpre_def Stable_State_def, clarsimp)
  apply (rule conjI) 
  using rgsep_implies_def apply blast
  using rgsep_implies_def by blast

lemma Stable_Property2 : "\<sigma> \<^sup>\<Turnstile>rgsep P \<Longrightarrow> stable P [] R \<Longrightarrow> Stable_State P \<sigma> R"
  apply (simp add: stable_def Stable_State_def, clarify)
  by blast

lemma Stable_trans_int: "\<lbrakk>RG_stable_getintpre (sa, ha, \<Gamma>') es Pre R; 
           Rely_Trans R;
           \<forall>r. \<Gamma>' r \<noteq> \<Gamma>'' r \<longrightarrow> (\<Gamma>' r, \<Gamma>'' r) \<in> R r \<and> disjoint (dom ha) (dom (\<Gamma>'' r))\<rbrakk>
      \<Longrightarrow>  RG_stable_getintpre (sa, ha, \<Gamma>'') es Pre R"
  apply (simp add: RG_stable_getintpre_def, clarify)
  apply (drule_tac a = "a" and b = "b" in all2_impD, simp)
  by (metis Rely_Trans_def transD)

lemma rgessafe_EvtSys :  "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep {Pre re} re {Post re};
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          Rely_Trans R;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
                        \<Longrightarrow> \<forall>n s h \<Gamma>. RG_stable_getintpre (s, h, \<Gamma>) es Pre R \<longrightarrow>
                            rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
  apply (simp add: reRGSep_def, clarify)
proof-
  fix n s h \<Gamma>
  assume a0: " \<forall>re\<in>es.
          user_revent re \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Pre re \<longrightarrow> rgsep_resafe n re s h \<Gamma> (Rely re) (Guar re) (Post re))"
  and    a1: " \<forall>re\<in>es. Post re \<^sup>\<sqsubseteq>rgsep Q"
  and    a2: "\<forall>re\<in>es. R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re"
  and    a3: "\<forall>re\<in>es. Guar re \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  and    a4: " Rely_Trans R"
  and    a5: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a6: "RG_stable_getintpre (s, h, \<Gamma>) es Pre R"
  then show "rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma>, simp, simp)
    apply (rule conjI, simp add: esaborts.simps, clarify)
     apply (drule_tac x = "(a, b)" in Set.bspec, simp) apply auto[1]
     apply (drule_tac a = "Suc 0" and b = "sa" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using RG_stable_getintpre_def apply blast apply simp
    apply (rule conjI, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" in mall3_impD, simp_all)
    using Stable_trans_int apply auto[1]
    apply (clarsimp, erule esred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (drule_tac x = "(aa, ba)" in Set.bspec, simp)
    apply (drule_tac x = "(aa, ba)" in Set.bspec, simp) apply auto
    apply (drule_tac a = "Suc n" and b = "ab" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using RG_stable_getintpre_def apply blast
    apply (simp add: rellocked_def, clarify)
    apply (drule_tac a = "hF" and b = "ac" and c = "bc" and d = "ad" 
                                    and e = "bd" in all5_impD, simp)
    apply (drule imp3D, simp, simp, simp, clarsimp)
    apply (rule_tac x = "h'" in exI, clarsimp)
    apply (rule_tac x = "\<Gamma>''" in exI, simp)
    apply (rule conjI, simp add: a0 user_reventD)
    apply (rule_tac Q = "Post (aa, ba)" in RGessafe_EvtSeq')
      apply (meson RGresafe_conseq rgsep_implies_def)
     apply (simp add: a0, clarsimp)
    apply (drule_tac a = "s'" and b = "h'a" and c = "\<Gamma>'''" in mall3_impD)
     apply (rule Stable_Property1, simp_all)
     apply auto[1]
    by (simp add: RGessafe_mon)
qed

theorem RGrule_EvtSys :  "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep {Pre re} re {Post re};
                          \<forall>re \<in> es.  P  \<^sup>\<sqsubseteq>rgsep Pre re;
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          Rely_Trans R; stable P [] R;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
                        \<Longrightarrow> R, G \<^sup>\<turnstile>esrgsep {P} (EvtSys es) {Q}" 
  apply (frule rgessafe_EvtSys, simp_all)
  apply (simp add: reRGSep_def esRGSep_def, clarify)
  apply (drule all4_impD, simp_all)
  by (metis Stable_Property1 Stable_Property2)

theorem RGrule_EvtSys' :  "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep {Pre re} re {Post re};
                          \<forall>re \<in> es.  P \<^sup>\<sqsubseteq>rgsep Pre re;
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          \<forall>re \<in> es. stable (Post re) [] (Rely re);
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
  and    a5: "\<forall>re\<in>es. stable (Post re) [] (Rely re)"
  and    a6: "stable P [] R"
  and    a7: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a8: "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_essafe n (EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma> P, simp, simp)
    apply (rule conjI, simp add: esaborts.simps, clarify)
     apply (drule_tac x = "(a, b)" in Set.bspec, simp)
     apply (drule_tac x = "(a, b)" in Set.bspec, simp) apply auto[1]
     apply (drule_tac a = "Suc 0" and b = "sa" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using rgsep_implies_def apply blast apply simp
    apply (rule conjI, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" and d = "Pa" in mall4_impD, simp_all)
      apply (simp add: stable_def) apply metis 
    apply (clarsimp, erule esred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (drule_tac x = "(aa, ba)" in Set.bspec, simp)
    apply (drule_tac x = "(aa, ba)" in Set.bspec, simp) apply auto
    apply (drule_tac a = "Suc n" and b = "ab" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using rgsep_implies_def apply blast 
    apply (simp add: rellocked_def, clarify)
    apply (drule_tac a = "hF" and b = "ac" and c = "bc" and d = "ad" 
                                    and e = "bd" in all5_impD, simp)
    apply (drule imp3D, simp, simp, simp, clarsimp)
    apply (rule_tac x = "h'" in exI, clarsimp)
    apply (rule_tac x = "\<Gamma>''" in exI, simp)
    apply (rule conjI, simp add: a0 user_reventD)
    apply (rule_tac Q = "Post (aa, ba)" in RGessafe_EvtSeq)
      apply (meson RGresafe_conseq rgsep_implies_def)
     apply (simp add: a0, clarify)
    apply (drule_tac a = "s'" and b = "h'a" and c = "\<Gamma>'''" 
                    and d = " Post (aa, ba)" in mall4_impD, clarify)
     apply blast
    by (meson RGessafe_mon Rely_Stable)
qed

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

primrec
  rgsep_ressafe :: "nat \<Rightarrow> resys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"        
where
  "rgsep_ressafe 0 res s h \<Gamma> R G Q = True"
| "rgsep_ressafe (Suc n) res s h \<Gamma> R G Q = (
(* Conditon (ii) *)
           (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> resaborts res (s, h ++ hF))
(* Condition (iii) *)
          \<and> resaccesses res s \<subseteq> dom h
(* Condition (iv) *)
          \<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
                    \<longrightarrow> (r \<notin> reslocked res) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
                    \<longrightarrow> rgsep_ressafe n res s h \<Gamma>' R G Q)
(* Condition (v) *)
          \<and> (\<forall>hJ hF res' \<sigma>'.
                resred res (s,h ++ hJ ++ hF) res' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (resllocked res') (resllocked res)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (resllocked res') (resllocked res)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (reslocked res') \<and> (r \<notin> reslocked res) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (resllocked res) (resllocked res'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (resllocked res) (resllocked res')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (reslocked res) \<and> r \<notin> (reslocked res') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (reslocked res) \<and> r \<notin> (reslocked res') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (reslocked res) \<or> r \<in> (reslocked res') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_ressafe n res' (fst \<sigma>') h' \<Gamma>' R G Q)
)))"

lemma RGressafe_agrees: 
  "\<lbrakk> rgsep_ressafe n res s h \<Gamma> R G Q ; 
     agrees (fvREsv res \<union> fvAA Q) s s' \<rbrakk>
   \<Longrightarrow> rgsep_ressafe n res s' h \<Gamma> R G Q"
  apply (induct n arbitrary: res s s' h \<Gamma> R G, simp, simp only: rgsep_ressafe.simps, clarify)
  apply (rule conjI)
   apply (metis agrees_search(1) agrees_simps(4) resaborts_agrees snd_conv snd_swap swap_simp)
  apply (rule conjI, subst (asm) resaccesses_agrees, simp_all)
  apply (rule conjI, blast)
  apply (clarify, drule_tac X="fvREsv (a, b) \<union> fvAA Q" in resred_agrees, 
         simp (no_asm), fast, simp (no_asm), fast, clarify)
  apply (drule (1) all5_impD, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  by (meson agrees_search(1) agrees_search(3) resred_properties)

lemma RGressafe_mon:
  "\<lbrakk> rgsep_ressafe n res s h \<Gamma> R G Q; m \<le> n \<rbrakk> \<Longrightarrow> rgsep_ressafe m res s h \<Gamma> R G Q"
apply (induct m arbitrary: res n s h \<Gamma>, simp) 
apply (case_tac n, clarify)
  apply (simp only: rgsep_ressafe.simps, clarsimp)
  apply (rule conjI, clarsimp) apply blast
  apply (clarsimp, drule_tac a = "hF" and b = "aa" and c = "ba" 
          and d = "ab" and e = "bb" in all5_impD, simp)
  apply (drule imp3D, simp_all, clarify)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  done

definition
    resRGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> resys \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>resrgsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>resrgsep {P} res {Q} \<equiv> (user_resys res \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P
                         \<longrightarrow> rgsep_ressafe n res s h \<Gamma> R G Q))"

lemma RGressafe_EvtSeq :"\<lbrakk>rgsep_resafe n re s h \<Gamma> Rely Guar Q; user_esys esys;
      \<forall>m s' h' \<Gamma>'. m \<le> n \<and> (s', h', \<Gamma>') \<^sup>\<Turnstile>rgsep Q 
      \<longrightarrow> rgsep_ressafe m (ers, esys) s' h' \<Gamma>' Rely Guar R\<rbrakk> 
      \<Longrightarrow>  rgsep_ressafe n (ers, (EvtSeq re esys)) s h \<Gamma> Rely Guar R"
  apply (induct n arbitrary: re s h \<Gamma>, simp, clarsimp)
  apply (rule conjI)                                            
   apply (simp add: esaborts.simps reaborts_equiv resaborts_equiv)
    apply (rule conjI)
   apply (simp add: reaccesses_def resaccesses_def)
  apply (rule conjI, simp add: reslocked_def)
  apply (clarsimp, erule resred.cases, simp_all)
  apply (drule_tac a = "hF" and b = "fst re'" and c = "snd re'" 
          and d = "ab" and e = "bb" in all5_impD, simp add: resllocked_def)
   apply (drule imp3D, simp_all add: reslocked_def resllocked_def, clarify)
    apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp, clarify)
  apply (rule_tac x = "h" and y = "\<Gamma>" in ex2I, simp add:rellocked_def)
  apply (rule conjI,simp add: user_reventD user_revent_def)
  by (simp add: relocked_def)

lemma RGressafe_EvtSeq' :"\<lbrakk>rgsep_resafe n re s h \<Gamma> Rely Guar Q; user_esys esys;
      \<forall>m s' h' \<Gamma>'. m \<le> n \<and> (s', h', \<Gamma>') \<^sup>\<Turnstile>rgsep Q \<and> (Stable_State Q (s', h', \<Gamma>') Rely)
      \<longrightarrow> rgsep_ressafe m (ers, esys) s' h' \<Gamma>' Rely Guar R\<rbrakk> 
      \<Longrightarrow>  rgsep_ressafe n (ers, (EvtSeq re esys)) s h \<Gamma> Rely Guar R"
  apply (induct n arbitrary: re s h \<Gamma>, simp, clarsimp)
  apply (rule conjI)
   apply (simp add: esaborts.simps reaborts_equiv resaborts_equiv)
    apply (rule conjI)
   apply (simp add: reaccesses_def resaccesses_def)
  apply (rule conjI, simp add: reslocked_def)
  apply (clarsimp, erule resred.cases, simp_all)
  apply (drule_tac a = "hF" and b = "fst re'" and c = "snd re'" 
          and d = "ab" and e = "bb" in all5_impD, simp add: resllocked_def)
   apply (drule imp3D, simp_all add: reslocked_def resllocked_def, clarify)
    apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp, clarify)
  apply (rule_tac x = "h" and y = "\<Gamma>" in ex2I, simp add:rellocked_def)
  apply (rule conjI, simp add: user_reventD user_revent_def)
  apply (rule conjI, simp add: relocked_def)
  apply (case_tac n, simp)
  apply (drule_tac a = "n" and b = "ad" and c = "h" and d = "\<Gamma>" in all4_impD)
   apply (simp add: Stable_State_def relocked_def, clarify)
  done

theorem RGrule_rEvtSeq :"\<lbrakk>Rely ,Guar  \<^sup>\<turnstile>rergsep {P} re {Q};
                 Rely , Guar \<^sup>\<turnstile>resrgsep { Q } (ers, esys) { R }\<rbrakk> 
                \<Longrightarrow> Rely , Guar \<^sup>\<turnstile>resrgsep {P} (ers, (EvtSeq re esys)) {R}"
  apply (simp add: reRGSep_def resRGSep_def user_resys_def)
  by (meson RGressafe_EvtSeq)

lemma rgressafe_EvtSys :  "\<lbrakk>  \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep 
                           {Pre re} (resources_re ers re) {Post re};
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          Rely_Trans R;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
                        \<Longrightarrow> \<forall>n s h \<Gamma>. RG_stable_getintpre (s, h, \<Gamma>) es Pre R \<longrightarrow>
                            rgsep_ressafe n (ers, (EvtSys es)) s h \<Gamma> R G Q"
  apply (simp add: reRGSep_def, clarify)
proof-
  fix n s h \<Gamma>
  assume a0: "\<forall>re\<in>es.
          user_revent (resources_re ers re) \<and>
          (\<forall>n s h \<Gamma>.
              (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Pre re \<longrightarrow> rgsep_resafe n (resources_re ers re) s h \<Gamma> (Rely re) (Guar re) (Post re))"
  and    a1: " \<forall>re\<in>es. Post re \<^sup>\<sqsubseteq>rgsep Q"
  and    a2: "\<forall>re\<in>es. R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re"
  and    a3: "\<forall>re\<in>es. Guar re \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  and    a4: " Rely_Trans R"
  and    a5: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a6: "RG_stable_getintpre (s, h, \<Gamma>) es Pre R"
  then show "rgsep_ressafe n (ers, EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma>, simp, simp)
    apply (rule conjI, simp add: resaborts_equiv esaborts.simps, clarify)
     apply (drule_tac x = "(a, b)" in Set.bspec, simp) apply auto[1]
    apply (drule_tac a = "Suc 0" and b = "sa" and c= "ha" and d = "\<Gamma>'" in all4_impD)
    using RG_stable_getintpre_def apply blast 
    apply (simp add: resources_re_aborts_equiv)
    apply (rule conjI, simp add: resaccesses_def)
    apply (rule conjI, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" in mall3_impD, simp_all)
    using Stable_trans_int apply auto[1]
    apply (clarsimp, erule resred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (drule_tac x = "(rs, e)" in Set.bspec, simp) apply auto
    apply (drule_tac a = "Suc n" and b = "ac" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using RG_stable_getintpre_def apply blast
    apply (simp add: rellocked_def , clarify)
    apply (drule_tac a = "hF" and b = "ers @ rs" and c = "e'" 
                    and d = "ad" and e = "bd" in all5_impD, simp)
    apply (drule imp3D, simp, simp, simp add: relocked_def reslocked_def, clarsimp)
    apply (rule_tac x = "h'" in exI, clarsimp)
    apply (rule_tac x = "\<Gamma>''" in exI, simp add: reslocked_def relocked_def)
    apply (rule conjI, simp add: elocked_eq) 
    apply (rule_tac Q = "Post (rs, e)" in RGressafe_EvtSeq')
      apply (meson RGresafe_conseq rgsep_implies_def)
    using a0 resource_re_equiv user_revent_def apply auto[1]
    apply (clarsimp, drule_tac a = "s'" and b = "h'a" and c = "\<Gamma>'''" in mall3_impD)  
      apply (rule Stable_Property1, simp_all)
     apply auto[1]
    by (simp add: RGressafe_mon)
qed

theorem RGrule_rEvtSys :  "\<lbrakk>  \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep 
                           {Pre re} (resources_re ers re) {Post re};
                          \<forall>re \<in> es.  P  \<^sup>\<sqsubseteq>rgsep Pre re;
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          Rely_Trans R; stable P [] R;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
                        \<Longrightarrow> R, G \<^sup>\<turnstile>resrgsep {P} (ers, (EvtSys es)) {Q}" 
  apply (frule rgressafe_EvtSys, simp_all)
  apply (simp add: reRGSep_def resRGSep_def user_resys_def user_revent_def resources_re_def) 
  by (metis Stable_Property1 Stable_Property2)

theorem RGrule_rEvtSys' :  "\<lbrakk> \<forall>re \<in> es. (Rely re), (Guar re)  \<^sup>\<turnstile>rergsep 
                           {Pre re} (resources_re ers re) {Post re};
                          \<forall>re \<in> es.  P \<^sup>\<sqsubseteq>rgsep Pre re;
                          \<forall>re \<in> es.  Post re  \<^sup>\<sqsubseteq>rgsep Q;
                          \<forall>re \<in> es.  R  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re;
                          \<forall>re \<in> es.  Guar re  \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;
                          \<forall>re \<in> es. stable (Post re) [] (Rely re);
                          stable P [] R;
                          \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<^sup>\<sqsubseteq>rgsep Pre re2 \<rbrakk>
                        \<Longrightarrow> R, G \<^sup>\<turnstile>resrgsep {P} (ers, (EvtSys es)) {Q}"
  apply (simp add: resRGSep_def reRGSep_def user_resys_def)
  apply (rule conjI, simp add: user_revent_def resources_re_def, clarify)
proof-
  fix n s h \<Gamma>
  assume a0: "  \<forall>re\<in>es.
          user_revent (resources_re ers re) \<and>
          (\<forall>n s h \<Gamma>.
              (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep Pre re \<longrightarrow> rgsep_resafe n (resources_re ers re) s h \<Gamma> (Rely re) (Guar re) (Post re))"
  and    a1: "\<forall>re\<in>es. P \<^sup>\<sqsubseteq>rgsep Pre re"
  and    a2: " \<forall>re\<in>es. Post re \<^sup>\<sqsubseteq>rgsep Q"
  and    a3: "\<forall>re\<in>es. R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rely re"
  and    a4: "\<forall>re\<in>es. Guar re \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  and    a5: "\<forall>re\<in>es. stable (Post re) [] (Rely re)"
  and    a6: "stable P [] R"
  and    a7: " \<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<^sup>\<sqsubseteq>rgsep Pre (aa, ba)"
  and    a8: "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P"
  then show "rgsep_ressafe n (ers, EvtSys es) s h \<Gamma> R G Q"
    apply (induct n arbitrary: s h \<Gamma> P, simp, simp)
    apply (rule conjI, simp add: resaborts_equiv esaborts.simps, clarify)
     apply (drule_tac x = "(a, b)" in Set.bspec, simp)
     apply (drule_tac x = "(a, b)" in Set.bspec, simp) apply auto[1]
     apply (drule_tac a = "Suc 0" and b = "sa" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using rgsep_implies_def apply blast
    apply (simp add: resources_re_aborts_equiv)
    apply (rule conjI, simp add: resaccesses_def)
    apply (rule conjI, simp add: reslocked_def, clarsimp)
     apply (drule_tac a = "sa" and b = "ha" and c = "\<Gamma>''" and d = "Pa" in mall4_impD, simp_all)
      apply (simp add: stable_def) apply metis 
    apply (clarsimp, erule resred.cases, simp_all, clarify)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (drule_tac x = "(rs, e)" in Set.bspec, simp)
    apply (drule_tac x = "(rs, e)" in Set.bspec, simp) apply auto
    apply (drule_tac a = "Suc n" and b = "ac" and c = "ha" and d = "\<Gamma>'" in all4_impD)
    using rgsep_implies_def apply blast
    apply (simp add: rellocked_def , clarify)
    apply (drule_tac a = "hF" and b = "ers @ rs" and c = "e'" 
                    and d = "ad" and e = "bd" in all5_impD, simp)
    apply (drule imp3D, simp, simp, simp add: relocked_def reslocked_def, clarsimp)
    apply (rule_tac x = "h'" in exI, clarsimp)
    apply (rule_tac x = "\<Gamma>''" in exI, simp add: reslocked_def relocked_def)
    apply (rule conjI, simp add: elocked_eq) 
    apply (rule_tac Q = "Post (rs, e)" in RGressafe_EvtSeq)
      apply (meson RGresafe_conseq rgsep_implies_def)
    using a0 resource_re_equiv user_revent_def apply auto[1]
    apply (clarsimp, drule_tac a = "s'" and b = "h'a" 
              and c = "\<Gamma>'''" and d = "Post (rs, e)" in mall4_impD, clarsimp)
    by (meson RGressafe_mon Rely_Stable)
qed

lemma RGressafe_conseq : "\<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_ressafe n res s h \<Gamma> R G Q\<rbrakk> 
    \<Longrightarrow> rgsep_ressafe n res s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: res s h \<Gamma>, simp, clarsimp)
  apply (rule conjI)
  apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all5_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
  by (meson RGsubset_def contra_subsetD)

theorem RGrule_resconseq : "
  \<lbrakk> R,G \<^sup>\<turnstile>resrgsep {P} res {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>resrgsep {P'} res {Q'}"
  by (simp add: resRGSep_def rgsep_implies_def RGressafe_conseq)

primrec 
  rgsep_pessafe :: "nat \<Rightarrow> paresys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  where
  "rgsep_pessafe 0 pes s h \<Gamma> R G Q = True"
| "rgsep_pessafe (Suc n) pes s h \<Gamma> R G Q =  (
  (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> pesaborts pes (s, h ++ hF))
\<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
          \<longrightarrow> (r \<notin> peslocked pes) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
          \<longrightarrow> rgsep_pessafe n pes s h \<Gamma>' R G Q)
          \<and> (\<forall>hJ hF pes' \<sigma>'.
                pesred pes (s,h ++ hJ ++ hF) pes' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (pesllocked pes') (pesllocked pes)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (pesllocked pes') (pesllocked pes)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (peslocked pes') \<and> (r \<notin> peslocked pes) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (pesllocked pes) (pesllocked pes'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (pesllocked pes) (pesllocked pes')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (peslocked pes) \<and> r \<notin> (peslocked pes') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (peslocked pes) \<and> r \<notin> (peslocked pes') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (peslocked pes) \<or> r \<in> (peslocked pes') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_pessafe n pes' (fst \<sigma>') h' \<Gamma>' R G Q)
)))"

definition
    pesRGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> paresys \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>pesrgsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>pesrgsep {P} pes {Q} \<equiv> (user_pesys pes \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P
                         \<longrightarrow> rgsep_pessafe n pes s h \<Gamma> R G Q))"

lemma list_minus_cancel : "\<lbrakk>disjoint (set a) (set b); disjoint (set a) (set c)
                           ; disjoint (set b) (set c)\<rbrakk> \<Longrightarrow>
    list_minus (a @ b @ c) (a @ b' @ c) = list_minus b b'"
  by (simp add: list_minus_appl list_minus_appr)

lemma RGpesllocked_cancel : "\<lbrakk>disjoint_locked_list pes; pes ! k = res;
             pes' = pes[k := res']; k < length pes\<rbrakk>
        \<Longrightarrow> list_minus (pesllocked pes) (pesllocked pes')
          = list_minus (resllocked res) (resllocked res')"
  apply (simp add: peslocked_split)
  apply (rule list_minus_cancel, simp_all add: peslocked_eq)
    apply (metis disjoint_locked_with_property disjoint_search(1) disjoint_with_take reslocked_eq)
   apply (simp add: disjoint_between_take_drop disjoint_locked_between_property)
  by (metis disjoint_locked_with_property disjoint_with_drop reslocked_eq)

lemma RGpessafe_pesllocked_cancel :
        "\<lbrakk> disjoint_locked_list pes; pes' = pes[k := res']; pes ! k = res; k < length pes;
         \<forall>k'. k' < length pes \<and> k \<noteq> k' \<longrightarrow> disjoint (reslocked res') (reslocked (pes ! k'))\<rbrakk>
        \<Longrightarrow> list_minus (pesllocked pes') (pesllocked pes)
          = list_minus (resllocked res') (resllocked res)"
  apply (rule RGpesllocked_cancel, simp_all)
  using disjoint_locked_list_update apply blast
  by auto

lemma RGpessafe_pesllocked_cancel':  "\<lbrakk> disjoint_locked_list pes; pes' = pes[k := res']; pes ! k = res; k < length pes;
         \<forall>k'. k' < length pes \<and> k \<noteq> k' \<longrightarrow> disjoint (reslocked res') (reslocked (pes ! k'))\<rbrakk>
        \<Longrightarrow> list_minus (resllocked res') (resllocked res) =
            list_minus (pesllocked pes') (pesllocked pes)"
  by (simp add: RGpessafe_pesllocked_cancel)


lemma list_minus_set : "r \<in> set (list_minus l1 l2) \<longleftrightarrow> r \<in> set l1 \<and> r \<notin> set l2"
proof
  assume "r \<in> set (list_minus l1 l2)"
  then show "r \<in> set l1 \<and> r \<notin> set l2"
    by simp
next
  assume "r \<in> set l1 \<and> r \<notin> set l2"
  then show "r \<in> set (list_minus l1 l2)"
    by simp
qed

lemma disjoint_set_property:  "disjoint a b \<Longrightarrow> x \<in> a \<Longrightarrow> x \<notin> b"
  by (metis IntI disjoint_def empty_iff)

lemma peslocked_diff : "\<lbrakk>disjoint_locked_list pes; k < length pes';          
                         r \<notin> peslocked pes \<or> r \<in> peslocked pes';
                         pes ! k = res; pes' = pes[k := res'];
                         \<forall>k'. k' < length pes \<and> k' \<noteq> k 
                        \<longrightarrow> disjoint (reslocked res') (reslocked (pes ! k'))\<rbrakk>
                         \<Longrightarrow> r \<notin> reslocked res \<or> r \<in> reslocked res'"
  by (metis RGpesllocked_cancel length_list_update list_minus_set peslocked_def reslocked_eq) 

lemma rgsep_pessafe: 
" \<lbrakk>\<forall>k. k < length pes \<longrightarrow> rgsep_ressafe n (pes ! k) s (hs ! k) \<Gamma> (Rs ! k) (Gs ! k) (Qs ! k);
   \<forall>k. k < length pes \<longrightarrow> (Gs ! k) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G; \<forall>k. k < length pes \<longrightarrow> R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k);
   disjoint_heap_list hs; disjoint_locked_list pes;
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvAA (Qs ! k1)) (wrREsv (pes ! k2));
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> (Gs ! k1) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k2);
    length pes = length hs\<rbrakk>
   \<Longrightarrow> rgsep_pessafe n pes s (hplus_list hs) \<Gamma> R G (RGistar Qs)"
  apply (induct n arbitrary: pes s hs \<Gamma>, simp, clarsimp)
  apply (rule conjI, clarsimp, erule pesaborts.cases, clarsimp)
    apply (simp add: pessafe_noaborts, clarsimp)
   apply (meson disjoint_list_equiv disjoint_search(2) disjoint_search(4) reswrites_accesses)
(* rely *)
  apply (rule conjI, clarsimp)
   apply (drule_tac a = "pes" and b = "s" and c = "hs" and d = "\<Gamma>'" in mall4_impD, clarsimp) 
    apply (drule_tac a = "k" in allD, clarsimp)
    apply (subgoal_tac "\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r \<longrightarrow> r \<notin> reslocked (pes ! k) 
          \<and> (\<Gamma> r, \<Gamma>' r) \<in> (Rs ! k) r \<and> disjoint (dom (hs ! k)) (dom (\<Gamma>' r))", simp, clarsimp)
    apply (drule_tac a = "r" in all_impD, simp, clarsimp)
    apply (rule conjI, simp add: peslock_notin)
    apply (rule conjI, simp add: RGsubset_def)  apply blast
    apply (simp add: disjoint_hplus_list, simp)
(* step *)
  apply (clarsimp, erule pesred.cases, simp)
  apply (frule_tac a = "k" in allD, clarsimp)
  apply (drule_tac a = "(hplus_list (hs[k:= Map.empty]) ++ hF)"
          and b = "ac" and c = "bc" and d = "ad" and e = "bd" in all5_impD)
   apply (drule_tac l = "hs" and k = "k" and hF = "hF" and
          hJ = "hplus_list (map \<Gamma> (list_minus (resllocked (ac, bc)) (resllocked (aa, ba))))"
          in pessafe_hsimps2, simp_all add: RGpessafe_pesllocked_cancel')
     apply (rule disjoint_map_list, simp)
  using peslocked_def apply presburger
    apply (simp add: disjoint_commute) 
    apply (rule disjoint_map_list, simp)
   apply (metis disjoint_search(1) peslocked_def)
  apply (drule imp2D)
    apply (simp add: disjoint_hplus_list1 disjoint_hplus_list3, clarify)
   apply (subgoal_tac "r \<in> set (list_minus (resllocked (ac, bc)) (resllocked (aa, ba)))")
    apply (simp add: RGpessafe_pesllocked_cancel')
  apply (rule conjI)
  using peslocked_def apply presburger
   apply (rule conjI)
  apply (metis disjoint_hplus_list2 disjoint_search(1) peslocked_def)
    apply (metis disjoint_hplus_list disjoint_search(1) nth_mem peslocked_def)
  apply (metis list_minus_set reslocked_eq)
  apply (clarsimp, rule_tac x = "h' ++ (hplus_list (hs[k := Map.empty]))" 
        and y = "\<Gamma>'" in ex2I, simp add: RGpesllocked_cancel)
  apply (rule conjI)
   apply (rule sym) apply (rule map_4_add1)
     apply (simp add: disjoint_commute)
     apply (rule disjoint_map_list, clarify, simp add: reslocked_eq disjoint_commute)
    apply (simp add: disjoint_commute)
    apply (rule disjoint_map_list, clarify, simp add: reslocked_eq disjoint_commute)
    apply (simp add: disjoint_commute)
   apply (rule disjoint_map_list, clarify, simp add: reslocked_eq disjoint_commute)
  apply (rule conjI)
   apply (metis disjoint_hplus_list2)
  apply (rule conjI, clarsimp)
   apply (subgoal_tac "r \<in> set (list_minus (pesllocked pesa) (pesllocked (pesa[k := (ac, bc)])))")
    apply (simp add: RGpesllocked_cancel)
  using reslocked_eq apply presburger
   apply (metis list_minus_set peslocked_def)
  apply (rule conjI, clarsimp)
   apply (subgoal_tac "r \<in> set (list_minus (pesllocked pesa) (pesllocked (pesa[k := (ac, bc)])))")
  apply (simp add: RGpesllocked_cancel)
    apply (metis (no_types, lifting) RGsubset_def contra_subsetD reslocked_eq)
   apply (metis list_minus_set peslocked_def)
  apply (rule conjI, clarsimp)
  apply (metis length_list_update peslocked_diff)
   apply (drule resred_properties)
   apply (clarsimp, drule_tac a = "pesa[k := (ac, bc)]" and b = "ad"
                and c = "hs[k := h']" and d = "\<Gamma>'" in mall4_impD)
    apply (clarsimp, case_tac "ka = k", simp, simp)
    apply (rule_tac s = "ab" in RGressafe_agrees)
     apply (drule_tac a = "ka" in all_impD, simp)
     apply (subgoal_tac "\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r \<longrightarrow> r \<notin> reslocked (pesa ! ka) 
            \<and> (\<Gamma> r, \<Gamma>' r) \<in> (Rs ! ka) r \<and> disjoint (dom (hs ! ka)) (dom (\<Gamma>' r))", simp, clarsimp)
     apply (subgoal_tac "r \<in> reslocked (aa, ba) \<and> r \<notin> reslocked (ac, bc)")
  apply (rule conjI)
       apply (metis disjoint_set_property disjoint_locked_list_equiv)
      apply (rule conjI)
       apply (subgoal_tac "Gs ! k \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Rs ! ka")
        apply (meson RGsubset_def contra_subsetD)
       apply blast
      apply (metis (no_types, lifting) disjoint_hplus_list1 
      length_list_update list_update_id list_update_same_conv list_update_swap)
    apply meson
   apply (drule_tac a = "ka" and b = "k" in all2_impD, simp, clarsimp)
  apply auto[1]
    apply (drule mimp5D, simp_all)
  using disjoint_heap_update1 apply presburger
      apply (metis disjoint_locked_list_update)
     apply (clarsimp, drule_tac a = "k1" and b = "k2" in all2_impD, simp)
    apply (case_tac "k1 \<noteq> k") apply (case_tac "k2 \<noteq> k", simp)
      apply auto[1] apply auto[1]
  apply (subgoal_tac "h' ++ hplus_list (hs[k := Map.empty]) = hplus_list (hs[k := h'])", simp)
  apply (metis disjoint_heap_update1 hplus_list_exchange 
        length_list_update list_update_overwrite nth_list_update_eq)
  done           

lemma split_RGistar : "(s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep RGistar Ps \<Longrightarrow> (\<exists>hs. length hs = length Ps 
                          \<and> disjoint_heap_list hs \<and> 
                          (\<forall>k < length Ps. (s, hs ! k, \<Gamma>) \<^sup>\<Turnstile>rgsep Ps ! k ) \<and> hplus_list hs = h)" 
  apply (induct Ps arbitrary: s h, simp, clarsimp)
  apply (drule mall2_impD, simp, clarsimp)
  apply (rule_tac x = "h1 # hs" in exI, simp)
  apply (rule conjI) 
  using disjoint_heap_with_equiv2 disjoint_hplus_list1 disjoint_search(1) apply blast
  using less_Suc_eq_0_disj by auto

theorem RGrule_pes : " \<lbrakk>\<forall>k. k < length pes \<longrightarrow> (Rs ! k), (Gs ! k)  \<^sup>\<turnstile>resrgsep {Ps ! k} (pes ! k) {Qs ! k};
   \<forall>k. k < length pes \<longrightarrow> (Gs ! k) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G; \<forall>k. k < length pes \<longrightarrow> R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k);
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvAA (Qs ! k1)) (wrREsv (pes ! k2));
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> (Gs ! k1) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k2);
    length pes = length Ps\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>pesrgsep {RGistar Ps} pes {RGistar Qs}"
  apply (simp add: pesRGSep_def resRGSep_def, clarify)
  apply (drule split_RGistar, clarify)
  apply (rule rgsep_pessafe, simp_all)
  by (simp add: disjoint_locked_list_equiv user_resysD)

lemma RGpessafe_conseq : "\<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_pessafe n pes s h \<Gamma> R G Q\<rbrakk> 
    \<Longrightarrow> rgsep_pessafe n pes s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: pes s h \<Gamma>, simp, clarsimp)
  apply (rule conjI)
  apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all4_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp)
  by (meson RGsubset_def contra_subsetD)

theorem RGrule_pesconseq : "
  \<lbrakk> R,G \<^sup>\<turnstile>pesrgsep {P} pes {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>pesrgsep {P'} pes {Q'}"
  by (simp add: pesRGSep_def RGpessafe_conseq rgsep_implies_def)

lemma RGUnion_conj : "RGUnion G1 G2 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G \<longleftrightarrow> G1 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G \<and> G2 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G"
  using RGUnion_def RGsubset_def by auto

lemma RGInter_disj : "R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (RGInter R1 R2) \<longleftrightarrow> R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R1 \<and> R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R2"
  using RGInter_def RGsubset_def by auto

corollary RGrule_pes2' :   " \<lbrakk>R1, G1  \<^sup>\<turnstile>resrgsep {P1} res1 {Q1};
  R2, G2  \<^sup>\<turnstile>resrgsep {P2} res2 {Q2}; G1 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R2; G2 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R1;
  (RGUnion G1 G2) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;  R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (RGInter R1 R2); 
  disjoint (fvREsv (res1) \<union> fvAA (Q1)) (wrREsv (res2));
  disjoint (fvREsv (res2) \<union> fvAA (Q2)) (wrREsv (res1))\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>pesrgsep {RGistar [P1, P2]} [res1, res2] {RGistar [Q1, Q2]}"
  apply (rule_tac Rs = "[R1, R2]" and Gs = "[G1, G2]" in RGrule_pes, 
        simp_all add: less_Suc_eq)
  using RGUnion_conj apply blast
  using RGInter_disj apply blast
  by auto

corollary RGrule_pes2 :   " \<lbrakk>R1, G1  \<^sup>\<turnstile>resrgsep {P1} res1 {Q1};
  R2, G2  \<^sup>\<turnstile>resrgsep {P2} res2 {Q2}; G1 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R2; G2 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R1;
  (RGUnion G1 G2) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;  R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (RGInter R1 R2); 
  disjoint (fvREsv (res1) \<union> fvAA (Q1)) (wrREsv (res2));
  disjoint (fvREsv (res2) \<union> fvAA (Q2)) (wrREsv (res1))\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>pesrgsep {RGstar P1 P2} [res1, res2] {RGstar Q1 Q2}"
  apply (rule_tac P = "RGistar [P1, P2]" and Q = "RGistar [Q1, Q2]"
        and R = "R" and G = "G" in RGrule_pesconseq)
  using RGrule_pes2' apply auto[1]
    apply (simp add: rgsep_implies_def)
    apply (simp add: rgsep_implies_def)
   apply (simp add: RGsubset_def)
  apply (simp add: RGsubset_def)
  done

primrec 
  rgsep_rpessafe :: "nat \<Rightarrow> rparesys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> heap) \<Rightarrow> rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  where
  "rgsep_rpessafe 0 rpes s h \<Gamma> R G Q = True"
| "rgsep_rpessafe (Suc n) rpes s h \<Gamma> R G Q =  (
  (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> rpesaborts rpes (s, h ++ hF))
\<and> (\<forall>\<Gamma>'. (\<forall>r. \<Gamma> r \<noteq> \<Gamma>' r 
          \<longrightarrow> (r \<notin> rpeslocked rpes) \<and> (\<Gamma> r, \<Gamma>' r) \<in> R r \<and> disjoint (dom h) (dom (\<Gamma>' r)))
          \<longrightarrow> rgsep_rpessafe n rpes s h \<Gamma>' R G Q)
          \<and> (\<forall>hJ hF rpes' \<sigma>'.
                rpesred rpes (s,h ++ hJ ++ hF) rpes' \<sigma>'
              \<longrightarrow> hJ = hplus_list (map \<Gamma> (list_minus (rpesllocked rpes') (rpesllocked rpes)))
              \<longrightarrow> disjoint (dom h) (dom hF)
              \<longrightarrow> RGdef (list_minus (rpesllocked rpes') (rpesllocked rpes)) \<Gamma>
              \<longrightarrow> (\<forall>r. r \<in> (rpeslocked rpes') \<and> (r \<notin> rpeslocked rpes) \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom (h ++ hF)))
              \<longrightarrow> (\<exists>h' \<Gamma>'. 
                    snd \<sigma>' = h' ++ hplus_list (map \<Gamma>' (list_minus (rpesllocked rpes) (rpesllocked rpes'))) ++ hF
                  \<and> disjoint (dom h') (dom hF)
                  \<and> RGdef (list_minus (rpesllocked rpes) (rpesllocked rpes')) \<Gamma>'
                  \<and> (\<forall>r. r \<in> (rpeslocked rpes) \<and> r \<notin> (rpeslocked rpes') \<longrightarrow> disjoint (dom (h' ++ hF)) (dom (\<Gamma>' r)))
                  \<and> (\<forall>r. r \<in> (rpeslocked rpes) \<and> r \<notin> (rpeslocked rpes') \<longrightarrow> (\<Gamma> r, \<Gamma>' r) \<in> G r)
                  \<and> (\<forall>r. r \<notin> (rpeslocked rpes) \<or> r \<in> (rpeslocked rpes') \<longrightarrow> \<Gamma> r = \<Gamma>' r)
                  \<and> (rgsep_rpessafe n rpes' (fst \<sigma>') h' \<Gamma>' R G Q)
)))"



definition
    rpesRGSep :: "rely \<Rightarrow> guar \<Rightarrow> rgsep_assn \<Rightarrow> rparesys \<Rightarrow> rgsep_assn \<Rightarrow> bool"
  ("_ , _ \<^sup>\<turnstile>rpesrgsep { _ } _ { _ }")
where
  "R,G  \<^sup>\<turnstile>rpesrgsep {P} rpes {Q} \<equiv> (user_rpesys rpes \<and> (\<forall>n s h \<Gamma>. (s, h, \<Gamma>) \<^sup>\<Turnstile>rgsep P
                         \<longrightarrow> rgsep_rpessafe n rpes s h \<Gamma> R G Q))"

lemma rgrpes_equiv : 
  "rgsep_pessafe n (resources_pes rs pes) s h \<Gamma> R G Q \<Longrightarrow> 
   rgsep_rpessafe n (rs, pes) s h \<Gamma> R G Q"
  apply (induct n arbitrary : pes s h \<Gamma>, simp, clarsimp)
  apply (rule conjI, simp add: rpesaborts_equiv')
  apply (rule conjI, simp add: resources_pes_def rpeslocked_def)
  apply (clarsimp, erule rpesred.cases, simp)
  apply (drule_tac a = "hF" and b = "resources_pes pres pesa[k := (pres @ ers, es')]" 
        and c = "aa" and d = "ba" in all4_impD, simp)
   apply (rule pesred.red_Par, simp, simp)
    apply (simp add: rpesllocked_def res_pes_update)
    apply (metis list_update_same_conv res_pes_length res_pes_update, simp)
  apply (drule imp3D, simp_all add: rpesllocked_def res_pes_update)
  apply (simp add: resources_pes_def rpeslocked_def, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, clarsimp)
  apply (rule conjI, simp add: resources_pes_def rpeslocked_def)
  apply (simp add: resources_pes_def rpeslocked_def)
  done

theorem RGrule_rpes1 : " \<lbrakk>\<forall>k. k < length pes \<longrightarrow> 
   (Rs ! k), (Gs ! k)  \<^sup>\<turnstile>resrgsep {Ps ! k} (resources_res rs) (pes ! k) {Qs ! k};
   \<forall>k. k < length pes \<longrightarrow> (Gs ! k) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G; \<forall>k. k < length pes \<longrightarrow> R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k);
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvAA (Qs ! k1)) (wrREsv (pes ! k2));
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> (Gs ! k1) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k2);
    length pes = length Ps\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>pesrgsep {RGistar Ps} (resources_pes rs pes) {RGistar Qs}"
  apply (rule RGrule_pes, simp_all, clarify)
   apply (simp add: res_pes_property)
  using res_pes_property by auto

theorem RGrule_rpes : " \<lbrakk>\<forall>k. k < length pes \<longrightarrow> 
   (Rs ! k), (Gs ! k)  \<^sup>\<turnstile>resrgsep {Ps ! k} (resources_res rs) (pes ! k) {Qs ! k};
   \<forall>k. k < length pes \<longrightarrow> (Gs ! k) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G; \<forall>k. k < length pes \<longrightarrow> R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k);
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvAA (Qs ! k1)) (wrREsv (pes ! k2));
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> (Gs ! k1) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (Rs ! k2);
    length pes = length Ps\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>rpesrgsep {RGistar Ps} (rs, pes) {RGistar Qs}"
  apply (drule RGrule_rpes1, simp_all)
  apply (simp add: pesRGSep_def rpesRGSep_def rgrpes_equiv user_rpesys_equiv)
  done

lemma RGrpessafe_conseq : "\<lbrakk>R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G';
   Q \<^sup>\<sqsubseteq>rgsep Q';rgsep_rpessafe n (rs, pes) s h \<Gamma> R G Q\<rbrakk> 
    \<Longrightarrow> rgsep_rpessafe n (rs, pes) s h \<Gamma> R' G' Q'"
  apply (induct n arbitrary: rs pes s h \<Gamma>, simp, simp add: RGsubset_def)
  apply (rule conjI)
  apply (metis RGsubset_def contra_subsetD)
(* step *)
  apply (clarsimp, drule (2) all5_imp2D, simp_all, clarsimp)
  apply (rule_tac x = "h'" and y = "\<Gamma>'" in ex2I, simp add: RGsubset_def)
  apply (simp add: rpeslocked_def)
  apply blast
  done

theorem RGrule_rpesconseq : "
  \<lbrakk> R,G \<^sup>\<turnstile>rpesrgsep {P} (rs, pes) {Q};
   P' \<^sup>\<sqsubseteq>rgsep P; Q \<^sup>\<sqsubseteq>rgsep Q';
   R'\<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R; G \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G' \<rbrakk>
    \<Longrightarrow> R',G' \<^sup>\<turnstile>rpesrgsep {P'} (rs, pes) {Q'}"
  by (simp add: rpesRGSep_def RGrpessafe_conseq rgsep_implies_def)

corollary RGrule_rpes2' :   " \<lbrakk>R1, G1  \<^sup>\<turnstile>resrgsep {P1} (resources_res rs res1) {Q1};
  R2, G2  \<^sup>\<turnstile>resrgsep {P2} (resources_res rs res2) {Q2}; G1 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R2; G2 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R1;
  (RGUnion G1 G2) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;  R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (RGInter R1 R2); 
  disjoint (fvREsv (res1) \<union> fvAA (Q1)) (wrREsv (res2));
  disjoint (fvREsv (res2) \<union> fvAA (Q2)) (wrREsv (res1))\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>pesrgsep {RGstar P1 P2} (resources_pes rs [res1, res2]) {RGstar Q1 Q2}"
    apply (rule_tac P = "RGistar [P1, P2]" and Q = "RGistar [Q1, Q2]"
        and R = "R" and G = "G" in RGrule_pesconseq)
  using RGrule_pes2' apply auto[1]
    apply (simp add: rgsep_implies_def)
    apply (simp add: rgsep_implies_def)
   apply (simp add: RGsubset_def)
  apply (simp add: RGsubset_def)
  done

corollary RGrule_rpes2 :   " \<lbrakk>R1, G1  \<^sup>\<turnstile>resrgsep {P1} (resources_res rs res1) {Q1};
  R2, G2  \<^sup>\<turnstile>resrgsep {P2} (resources_res rs res2) {Q2}; G1 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R2; G2 \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R1;
  (RGUnion G1 G2) \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p G;  R \<subseteq>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p (RGInter R1 R2); 
  disjoint (fvREsv (res1) \<union> fvAA (Q1)) (wrREsv (res2));
  disjoint (fvREsv (res2) \<union> fvAA (Q2)) (wrREsv (res1))\<rbrakk>
   \<Longrightarrow> R,G  \<^sup>\<turnstile>rpesrgsep {RGstar P1 P2} (rs, [res1, res2]) {RGstar Q1 Q2}"
  apply (drule RGrule_rpes2', simp_all)
  apply (simp add: pesRGSep_def rpesRGSep_def rgrpes_equiv user_rpesys_equiv)
  done

end