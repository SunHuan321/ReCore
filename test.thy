theory test
  imports CSLsound Event_Computation
begin


primrec user_event :: "event \<Rightarrow> bool"
  where "user_event (AnonyEvent C) = user_cmd C"
  |     "user_event (BasicEvent GC) = user_cmd (snd GC)"

primrec wf_event :: "event \<Rightarrow> bool"
  where "wf_event (AnonyEvent C) = wf_cmd C"
  |     "wf_event (BasicEvent GC) = wf_cmd (snd GC)"

lemma user_eventD : "user_event e \<Longrightarrow> wf_event e \<and> elocked e= {}"
  by (induct e, simp_all add: user_cmdD)

corollary user_event_wf[intro]: "user_event e \<Longrightarrow> wf_event e"
  by (drule user_eventD, simp)

corollary user_event_llocked[simp] : "user_event e \<Longrightarrow> ellocked e = []"
  by (drule user_eventD, simp add: elocked_eq)

definition user_revent :: "revent \<Rightarrow> bool"
  where "user_revent re = user_event (snd re)"

definition wf_revent :: "revent \<Rightarrow> bool"
  where "wf_revent re = wf_event (snd re)"
         
lemma user_reventD : "user_revent re \<Longrightarrow> wf_revent re \<and> relocked re= {}"
  by (simp add: user_revent_def wf_revent_def relocked_def user_eventD)

corollary user_revent_wf[intro]: "user_revent re \<Longrightarrow> wf_revent re"
  by (drule user_reventD, simp)

corollary user_revent_llocked[simp] : "user_revent re \<Longrightarrow> rellocked re = []"
  by (drule user_reventD, simp add: relocked_eq)

primrec user_esys :: "esys \<Rightarrow> bool"
  where "user_esys (EvtSeq res esys) = ((user_revent res) \<and> (user_esys esys))"
  |     "user_esys (EvtSys es) = (\<forall> res \<in> es. (user_revent res))"

primrec wf_esys :: "esys \<Rightarrow> bool"
  where "wf_esys (EvtSeq res esys) = ((wf_revent res) \<and> (wf_esys esys))"
  |     "wf_esys (EvtSys es) = (\<forall> res \<in> es. (wf_revent res))"

lemma user_esysD : "user_esys esys \<Longrightarrow> wf_esys esys \<and> eslocked esys = {}"
  by (induct esys, simp_all add: user_reventD)

corollary user_esys_wf[intro]: "user_esys esys \<Longrightarrow> wf_esys esys"
  by (drule user_esysD, simp)

corollary user_esys_llocked[simp] : "user_esys esys \<Longrightarrow> esllocked esys = []"
  by (drule user_esysD, simp add: eslocked_eq)

definition user_resys :: "resys \<Rightarrow> bool"
  where "user_resys resys = user_esys (snd resys)"

definition wf_resys :: "resys \<Rightarrow> bool"
  where "wf_resys resys = wf_esys (snd resys)"

lemma user_resysD : "user_resys resys \<Longrightarrow> wf_resys resys \<and> reslocked resys = {}"
  by (simp add: user_resys_def wf_resys_def reslocked_def user_esysD)

corollary user_resys_wf[intro]: "user_resys resys \<Longrightarrow> wf_resys resys"
  by (drule user_resysD, simp)

corollary user_resys_llocked[simp] : "user_resys resys \<Longrightarrow> resllocked resys = []"
  by (drule user_resysD, simp add: reslocked_eq)

primrec user_pesys :: "paresys \<Rightarrow> bool"
  where "user_pesys [] = True"
  |     "user_pesys (x # xs) = ((user_resys x) \<and> (user_pesys xs))"

primrec wf_pesys :: "paresys \<Rightarrow> bool"
  where "wf_pesys [] = True"
  |     "wf_pesys (x # xs) = ((wf_resys x) \<and> (wf_pesys xs))"

definition user_rparesys :: "rparesys \<Rightarrow> bool"
  where "user_rparesys rpes = user_pesys (snd rpes)"

definition wf_rparesys :: "rparesys \<Rightarrow> bool"
  where "wf_rparesys rpes = wf_pesys (snd rpes)"

primrec
  esafe :: "nat \<Rightarrow> event \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "esafe 0 e s h \<Gamma> Q = True"
| "esafe (Suc n) e s h \<Gamma> Q = (
              (e = AnonyEvent Cskip \<longrightarrow> (s, h) \<Turnstile> Q)
            \<and> (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> eaborts e (s, h ++ hF))
            \<and> (eaccesses e s \<subseteq> dom h)
            \<and> (\<forall>hJ hF e' \<sigma>'. 
                  ered e (s, h ++ hJ ++ hF) e' \<sigma>'
                \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (ellocked e') (ellocked e)
                \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
                \<longrightarrow> (\<exists> h' hJ'.
                        snd \<sigma>' = h' ++ hJ' ++ hF
                      \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
                      \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (ellocked e) (ellocked e')
                      \<and>  esafe n e' (fst \<sigma>') h' \<Gamma> Q)))"

lemma esafe_agrees: 
    "\<lbrakk> esafe n e s h \<Gamma> Q ; 
     agrees (fvEv e \<union> fvA Q \<union> fvAs \<Gamma>) s s' \<rbrakk>
   \<Longrightarrow> esafe n e s' h \<Gamma> Q"
  apply (induct n arbitrary: e s s' h, simp, simp only: esafe.simps, clarify)
  apply (rule conjI, clarsimp, subst assn_agrees, subst agreesC, assumption+)
  apply (rule conjI, clarsimp)
   apply (drule_tac eaborts_agrees, simp, fast, simp, simp)
  apply (rule conjI, subst(asm) eaccesses_agrees, simp_all)
  apply (clarify, drule_tac X="fvEv e \<union> fvAs \<Gamma> \<union> fvA Q" in ered_agrees, 
         simp (no_asm), fast, simp (no_asm), fast, clarify)
  apply (drule (1) all5_impD, clarsimp)
  apply (drule impD, erule assns_agreesE, simp add: agreesC, clarify)
  apply (rule_tac x=h' and y=hJ' in ex2I, simp add: hsimps)
  apply (rule conjI, erule assns_agreesE, subst agreesC, assumption)
  apply (erule (1) mall4_imp2D, simp add: agreesC)
  apply (drule ered_properties, auto)
done

definition 
  eCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> event \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>e { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>e {P} e {Q} \<equiv> (user_event e) \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> esafe n e s h \<Gamma> Q)"


lemma list_minus_empty[simp] : "list_minus [] l = []"
  by (induct l, simp_all)

lemma envs_empty_minus[simp]: " envs \<Gamma> [] l = Aemp"
  by (simp add: envs_def)

lemma envs_minus_empty[simp]: " envs \<Gamma> l [] = Aistar (map \<Gamma> l)"
  by (simp add: envs_def)

lemma esafe_AnonyEvt: "safe n C s h \<Gamma> Q \<Longrightarrow> esafe n (AnonyEvent C) s h \<Gamma> Q"
  apply (induct n arbitrary: C s h, simp_all, clarify)
  apply (rule conjI)
  using eaborts.cases apply blast
  apply (clarsimp, erule ered.cases, simp_all)
  apply (drule_tac a = "hJ" and b = "hF" and c = "C'" and d = "a " and e = "b" in all5_impD, simp)
  apply (drule imp2D, simp_all)
  by blast

theorem rule_Inner: "\<Gamma> \<turnstile> {P} C {Q} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e {P} (AnonyEvent C) {Q}"
  by (simp add: eCSL_def CSL_def esafe_AnonyEvt)

theorem rule_BasicEvt: "\<Gamma> \<turnstile> {Aconj P (Apure guard)} C {Q} 
                    \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e {P} (BasicEvent (guard, C)) {Q}"
  apply (simp add: eCSL_def CSL_def, clarsimp)
  apply (case_tac n, simp, simp)
  apply (rule conjI)
  using eaborts.cases apply blast
  apply (clarsimp, erule ered.cases, simp)
  apply (rule_tac x = "h" in exI, clarify, simp add: esafe_AnonyEvt)
  done

lemma esafe_conseq : "\<lbrakk> esafe n e s h \<Gamma> Q; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> esafe n e s h \<Gamma> Q'"
  apply (induct n arbitrary: e s h, simp)
  apply (clarsimp, simp add : implies_def)
  apply (clarify, erule ered.cases, simp_all, clarsimp)
   apply (drule_tac a = "hJ" and b = "hF" and c = "AnonyEvent C'" and d = "ab" and e = "bb" in all5_impD)
    apply (simp add: ered.red_AnonyEvt)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "AnonyEvent C" and d = "a" and e = "b" in all5_impD)
  using ered.red_BasicEvt apply blast
  apply (clarsimp, rule_tac x = "h'" in exI, simp)
  done

theorem rule_Evtconseq : "\<lbrakk> P \<sqsubseteq> P'; Q' \<sqsubseteq> Q; \<Gamma>  \<turnstile>\<^sub>e {P'} e {Q'} \<rbrakk> \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>e {P} e {Q}"
  by (meson eCSL_def esafe_conseq implies_def)

primrec 
  resafe :: "nat \<Rightarrow> revent \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "resafe 0 e s h \<Gamma> Q = True"
| "resafe (Suc n) re s h \<Gamma> Q = (
              (snd re = AnonyEvent Cskip \<longrightarrow> (s, h) \<Turnstile> Q)
            \<and> (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> reaborts re (s, h ++ hF))
            \<and> (reaccesses re s \<subseteq> dom h)
            \<and> (\<forall>hJ hF re' \<sigma>'. 
                  rered re (s, h ++ hJ ++ hF) re' \<sigma>'
                \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (rellocked re') (rellocked re)
                \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
                \<longrightarrow> (\<exists>h' hJ'.
                        snd \<sigma>' = h' ++ hJ' ++ hF
                      \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
                      \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (rellocked re) (rellocked re')
                      \<and> resafe n re' (fst \<sigma>') h' \<Gamma> Q)))"

lemma resafe_agrees: 
    "\<lbrakk> resafe n re s h \<Gamma> Q ; 
     agrees (fvREv re \<union> fvA Q \<union> fvAs \<Gamma>) s s' \<rbrakk>
   \<Longrightarrow> resafe n re s' h \<Gamma> Q"
  apply (induct n arbitrary: re s s' h, simp, simp only: resafe.simps, clarify)
  apply (rule conjI, clarsimp, subst assn_agrees, subst agreesC, assumption+)
  apply (rule conjI, clarsimp)
   apply (drule_tac reaborts_agrees, simp, fast, simp, simp)
  apply (rule conjI, subst (asm) reaccesses_agrees, simp_all)
  apply (clarify, drule_tac X = "fvREv (a, b) \<union> fvAs \<Gamma> \<union> fvA Q" in rered_agrees,
       simp (no_asm), fast, simp(no_asm), fast, clarify)
  apply (drule (1) all6_impD, clarsimp)
  apply (drule impD, erule assns_agreesE, simp add: agreesC, clarify)
  apply (rule_tac x=h' and y=hJ' in ex2I, simp add: hsimps)
  apply (rule conjI, erule assns_agreesE, subst agreesC, assumption)
  apply (erule (1) mall5_imp2D, simp add: agreesC)
  apply (drule rered_properties, auto)
  done

definition 
  reCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> revent \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>r\<^sub>e { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q} \<equiv> (user_revent re) \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> resafe n re s h \<Gamma> Q)"

lemma resafe_AnonyEvt: "esafe n (AnonyEvent C) s h \<Gamma> Q  \<Longrightarrow> resafe n (rs, (AnonyEvent C)) s h \<Gamma> Q"
  apply (induct n arbitrary: C s h, simp_all)
  apply (rule conjI)
   apply (simp add: reaborts_def)
  apply (rule conjI)
   apply (simp add: reaccesses_def)
  apply (clarify, erule rered.cases, simp_all, clarify)
  apply (drule_tac a = "hJ" and b = "hF" and c = "AnonyEvent C'" and d = "ac" and e = "bc" in all5_impD)
   apply (simp add: ered.red_AnonyEvt)
  apply (simp add : rellocked_def, clarify)
  apply (rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  done

theorem rule_rInner: "\<Gamma> \<turnstile> {P} C {Q} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} (rs, AnonyEvent C) {Q}"
  using eCSL_def reCSL_def resafe_AnonyEvt rule_Inner user_revent_def by auto

theorem rule_rBasicEvt: "\<Gamma> \<turnstile> {Aconj P (Apure guard)} (Cresources rs C) {Q} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} (rs, BasicEvent (guard, C)) {Q}"
  apply (simp add: reCSL_def CSL_def, clarsimp)
  apply (simp add: user_revent_def, clarsimp)
  apply (case_tac n, simp, simp)
  apply (rule conjI, simp add: reaborts_def)
  using eaborts.cases apply blast
  apply (rule conjI, simp add: reaccesses_def)
  apply (clarsimp, erule rered.cases, simp, simp add: rellocked_def, clarify)
  apply (rule_tac x = "h" in exI, clarsimp)
  apply (rule resafe_AnonyEvt, simp add: esafe_AnonyEvt)
  done


lemma resafe_conseq : "\<lbrakk> resafe n re s h \<Gamma> Q; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> resafe n re s h \<Gamma> Q'"
    apply (induct n arbitrary: re s h, simp)
  apply (clarsimp, simp add : implies_def)
  apply (clarify, erule rered.cases, simp_all, clarsimp)
   apply (drule_tac a = "hJ" and b = "hF" and c = "rs" and d = "AnonyEvent C'" and e = "ad" and f = "bd" in all6_impD)
  apply (simp add: rered.red_AnonyEvt)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "rs" and d = "AnonyEvent (Cresources rs C)" and e = "ab" and f = "bb" in all6_impD)
  using rered.red_BasicEvt apply blast
  apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  done

theorem rule_rEvtconseq : "\<lbrakk> P \<sqsubseteq> P'; Q' \<sqsubseteq> Q; \<Gamma>  \<turnstile>\<^sub>r\<^sub>e {P'} re {Q'} \<rbrakk> \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e {P} re {Q}"
  by (meson implies_def reCSL_def resafe_conseq)

primrec 
  essafe :: "nat \<Rightarrow> esys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "essafe 0 es s h \<Gamma> Q = True"
| "essafe (Suc n) es s h \<Gamma> Q = (
             (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> esaborts es (s, h ++ hF))
            \<and> (esaccesses es s \<subseteq> dom h)
            \<and> (\<forall>hJ hF es' \<sigma>'. 
                  esred es (s, h ++ hJ ++ hF) es' \<sigma>'
                \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (esllocked es') (esllocked es)
                \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
                \<longrightarrow> (\<exists>h' hJ'.
                        snd \<sigma>' = h' ++ hJ' ++ hF
                      \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
                      \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (esllocked es) (esllocked es')
                      \<and> essafe n es' (fst \<sigma>') h' \<Gamma> Q)))"

lemma essafe_agrees: 
    "\<lbrakk> essafe n esys s h \<Gamma> Q ; 
     agrees (fvEsv esys \<union> fvA Q \<union> fvAs \<Gamma>) s s' \<rbrakk>
   \<Longrightarrow> essafe n esys s' h \<Gamma> Q"
  apply (induct n arbitrary: esys s s' h, simp, simp only: essafe.simps, clarify)
  apply (rule conjI, clarsimp)
   apply (drule_tac esaborts_agrees, simp, fast, simp, simp)
  apply (rule conjI, subst (asm) esaccesses_agrees, simp_all)
  apply (clarify, drule_tac X = "fvEsv esys \<union> fvAs \<Gamma> \<union> fvA Q" in esred_agrees,
       simp (no_asm), fast, simp(no_asm), fast, clarify)
  apply (drule (1) all5_impD, clarsimp)
  apply (drule impD, erule assns_agreesE, simp add: agreesC, clarify)
  apply (rule_tac x=h' and y=hJ' in ex2I, simp add: hsimps)
  apply (rule conjI, erule assns_agreesE, subst agreesC, assumption)
  apply (erule (1) mall4_imp2D, simp add: agreesC)
  apply (drule esred_properties, auto)
  done

definition 
  esCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> esys \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>e\<^sub>s { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} esys {Q} \<equiv> (user_esys esys) \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> essafe n esys s h \<Gamma> Q)"

lemma essafe_mon:
  "\<lbrakk> essafe n es s h \<Gamma> Q; m \<le> n \<rbrakk> \<Longrightarrow> essafe m es s h \<Gamma> Q"
apply (induct m arbitrary: es s n h, simp) 
apply (case_tac n, clarify)
apply (simp only: safe.simps, clarsimp)
apply (drule all5D, drule (2) imp3D, simp, clarsimp)
apply (rule_tac x="h'" in exI, rule_tac x="hJ'" in exI, simp)
  done

lemma essafe_EvtSeq :"\<lbrakk>resafe n re s h \<Gamma> Q;
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> (Q ** (Aistar (map \<Gamma> (esllocked esys)))) \<longrightarrow> essafe m esys s' h' \<Gamma> R\<rbrakk> 
      \<Longrightarrow>  essafe n (EvtSeq re esys) s h \<Gamma> R"
  apply (induct n arbitrary: re s h, simp, clarsimp)
  apply (rule conjI, clarsimp)
   apply (erule esaborts.cases, simp_all, clarsimp)
  apply (clarsimp, erule esred.cases, simp_all)
   apply (clarify, drule (1) all6_impD, clarsimp)
   apply (rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (clarify, simp add: rellocked_def)
  apply (rule_tac x = "h ++ hJ" in exI, simp)
  apply (drule_tac a = "n" and b = "ac" and c = "h ++ hJ" in all3_impD, simp_all)
  apply (rule_tac x = "h" in exI, simp)
  apply (rule_tac x = "hJ" in exI, simp)
  done

lemma essafe_EvtSeq' :"\<lbrakk>resafe n re s h \<Gamma> Q; user_esys esys;
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Q  \<longrightarrow> essafe m esys s' h' \<Gamma> R\<rbrakk> 
      \<Longrightarrow>  essafe n (EvtSeq re esys) s h \<Gamma> R"
  by (rule essafe_EvtSeq, simp_all)

theorem rule_EvtSeq :"\<lbrakk>\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q};
                 \<Gamma> \<turnstile>\<^sub>e\<^sub>s {Q } esys {R}\<rbrakk> 
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} (EvtSeq re esys) {R}"
  by (auto simp add: reCSL_def esCSL_def intro!: essafe_EvtSeq)

definition get_int_pre :: "state \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> assn) \<Rightarrow> bool"
  where "get_int_pre \<sigma> es Pre \<equiv> \<forall> re \<in> es.  \<sigma> \<Turnstile> (Pre re)" 

definition get_union_post :: "state \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> assn) \<Rightarrow> bool"
  where "get_union_post \<sigma> es Post \<equiv>  \<exists>re \<in> es. \<sigma> \<Turnstile> (Post re)" 

lemma pre_conj : "\<lbrakk> \<forall>re \<in> es. P \<sqsubseteq> (Pre re) ; \<sigma> \<Turnstile> P \<rbrakk> \<Longrightarrow> get_int_pre \<sigma> es Pre"
  using get_int_pre_def implies_def by blast

lemma post_dconj : "\<lbrakk>\<forall>re\<in>es. (Post re) \<sqsubseteq> Q; get_union_post \<sigma> es Post\<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> Q"
  using get_union_post_def implies_def by blast

lemma essafe_EvtSys : "\<lbrakk> \<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re)} re {Post re};
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q; 
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow> \<forall>n s h. get_int_pre (s, h) es Pre \<longrightarrow> essafe n (EvtSys es) s h \<Gamma> Q"
  apply (simp add: reCSL_def)
proof(intro allI impI)
  fix n s h
  assume a0 : "\<forall>re\<in>es. user_revent re \<and> (\<forall>n s h. (s, h) \<Turnstile> Pre re \<longrightarrow> resafe n re s h \<Gamma> (Post re))"
  and    a1 : "\<forall>re\<in>es. Post re \<sqsubseteq> Q"
  and    a2 : "\<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<sqsubseteq> Pre (aa, ba)"
  and    a3 : "get_int_pre (s, h) es Pre"
  then show "essafe n (EvtSys es) s h \<Gamma> Q"
    apply (induct n arbitrary: s h, simp_all)
    apply (rule conjI)
     apply (meson esaborts.cases esys.simps(4))
    apply (clarify, erule esred.cases, simp_all)
    apply (rule_tac x = "ha" in exI, clarsimp)
    apply (rule_tac Q = "Post (aa, ba)" in essafe_EvtSeq)
     apply (subgoal_tac "(ab, ha) \<Turnstile> Pre (aa, ba)", simp)
     apply (simp add: get_int_pre_def)
    apply (clarsimp, drule_tac a = "s'" and b = "h'" in mall2_impD)
    using get_int_pre_def implies_def apply auto[1]
    using essafe_mon by blast
qed

theorem rule_EvtSys :  "\<lbrakk> \<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re)} re {Post re};
                         \<forall> re \<in> es. P \<sqsubseteq> Pre re;
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q;
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} (EvtSys es) {Q}"
  apply (simp add: esCSL_def)
  apply (rule conjI, simp add: reCSL_def)
  apply (clarsimp, drule essafe_EvtSys, simp_all)
  by (simp add: pre_conj)


lemma essafe_conseq : "\<lbrakk> essafe n es s h \<Gamma> Q; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> essafe n es s h \<Gamma> Q'"
  apply (induct n arbitrary: es s h, simp)
  apply (clarsimp, simp add : implies_def)
  apply (erule esred.cases, simp_all, clarify)
    apply (drule_tac a = "hJ" and b = "hF" and c = "EvtSeq (ac, bc) res" and d = "ad" and e = "bd" in all5_impD)
     apply (simp add: esred.red_EvtSeq1)
    apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
   apply (drule_tac a = "hJ" and b = "hF" and c = "res" and d = "a" and e = "b" in all5_impD)
    apply (simp add: esred.red_EvtSeq2)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "EvtSeq re (EvtSys revts)" and d = "a" and e = "b" in all5_impD)
   apply (simp add: esred.red_EvtSet)
  apply (clarsimp, rule_tac x = "h'" in exI, simp)
  done

theorem rule_esconseq : "\<lbrakk> P \<sqsubseteq> P'; Q' \<sqsubseteq> Q; \<Gamma>  \<turnstile>\<^sub>e\<^sub>s {P'} es {Q'} \<rbrakk> \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>e\<^sub>s {P} es {Q}"
  by (meson esCSL_def essafe_conseq implies_def)

primrec 
  ressafe :: "nat \<Rightarrow> resys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
where
  "ressafe 0 res s h \<Gamma> Q = True"
| "ressafe (Suc n) res s h \<Gamma> Q = (
             (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> resaborts res (s, h ++ hF))
            \<and> (resaccesses res s \<subseteq> dom h)
            \<and> (\<forall>hJ hF res' \<sigma>'. 
                  resred res (s, h ++ hJ ++ hF) res' \<sigma>'
                \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (resllocked res') (resllocked res)
                \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
                \<longrightarrow> (\<exists>h' hJ'.
                        snd \<sigma>' = h' ++ hJ' ++ hF
                      \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
                      \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (resllocked res) (resllocked res')
                      \<and> ressafe n res' (fst \<sigma>') h' \<Gamma> Q)))"

lemma ressafe_mon:
  "\<lbrakk> ressafe n res s h \<Gamma> Q; m \<le> n \<rbrakk> \<Longrightarrow> ressafe m res s h \<Gamma> Q"
apply (induct m arbitrary: res s n h, simp) 
apply (case_tac n, clarify)
apply (simp only: safe.simps, clarsimp)
apply (drule all6D, drule (2) imp3D, simp, clarsimp)
apply (rule_tac x="h'" in exI, rule_tac x="hJ'" in exI, simp)
  done

lemma ressafe_agrees: 
    "\<lbrakk> ressafe n resys s h \<Gamma> Q ; 
     agrees (fvREsv resys \<union> fvA Q \<union> fvAs \<Gamma>) s s' \<rbrakk>
   \<Longrightarrow> ressafe n resys s' h \<Gamma> Q"
  apply (induct n arbitrary: resys s s' h, simp, simp only: ressafe.simps, clarify)
  apply (rule conjI, clarsimp)
   apply (drule_tac resaborts_agrees, simp, fast, simp, simp)
  apply (rule conjI, subst (asm) resaccesses_agrees, simp_all)
  apply (clarify, drule_tac X = "fvREsv (a,b) \<union> fvAs \<Gamma> \<union> fvA Q" in resred_agrees,
       simp (no_asm), fast, simp(no_asm), fast, clarify)
  apply (drule (1) all6_impD, clarsimp)
  apply (drule impD, erule assns_agreesE, simp add: agreesC, clarify)
  apply (rule_tac x=h' and y=hJ' in ex2I, simp add: hsimps)
  apply (rule conjI, erule assns_agreesE, subst agreesC, assumption)
  apply (erule (1) mall5_imp2D, simp add: agreesC)
  apply (drule resred_properties, auto)
  done

definition 
  resCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> resys \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>r\<^sub>e\<^sub>s { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} resys {Q} \<equiv> (user_resys resys) \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> ressafe n resys s h \<Gamma> Q)"

definition resources_re :: "rname list \<Rightarrow> revent \<Rightarrow> revent"
  where "resources_re ers re \<equiv> (ers @ (fst re), (snd re))"

lemma ressafe_EvtSeq : "\<lbrakk>resafe n re s h \<Gamma> Q;
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> (Q ** (Aistar (map \<Gamma> (esllocked esys)))) \<longrightarrow> ressafe m (ers, esys) s' h' \<Gamma> R\<rbrakk> 
      \<Longrightarrow>  ressafe n (ers, (EvtSeq re esys)) s h \<Gamma> R"
  apply (induct n arbitrary: re s h, simp ,clarsimp)
  apply (rule conjI)
   apply (simp add: esaborts.simps reaborts_def resaborts_def)
  apply (rule conjI)
   apply (simp add: reaccesses_def resaccesses_def)
  apply (clarsimp, erule resred.cases, simp_all)
   apply (clarsimp, drule_tac a = "hJ" and b = "hF" and c = "ae" and d = "be" and e = "af" and f = "bf" in all6_impD, simp)
   apply (simp add: resllocked_def, clarify, rule_tac x = "h'" and y = "hJ'" in ex2I, clarsimp)
  apply (clarify, simp add: resllocked_def rellocked_def)
  apply (rule_tac x = "h ++ hJ" in exI, clarsimp)
  apply (drule_tac a = "n" and b = "ad" and c = "h ++ hJ" in all3_impD, simp_all)
  apply (rule_tac x = "h" in exI) 
  apply (clarsimp,rule_tac x = "hJ" in exI)
  by simp

lemma ressafe_EvtSeq' : "\<lbrakk>resafe n re s h \<Gamma> Q; user_esys esys;
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Q \<longrightarrow> ressafe m (ers, esys) s' h' \<Gamma> R\<rbrakk> 
      \<Longrightarrow>  ressafe n (ers, (EvtSeq re esys)) s h \<Gamma> R"
  by (simp add: ressafe_EvtSeq)

theorem rule_rEvtSeq :"\<lbrakk>\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q};
                 \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {Q } (ers,esys) {R}\<rbrakk> 
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} (ers, (EvtSeq re esys)) {R}"
  apply (auto simp add: reCSL_def resCSL_def user_resys_def intro!: ressafe_EvtSeq)
  done

lemma ressafe_EvtSys : "\<lbrakk> \<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re)} (resources_re ers re) {Post re};
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q;
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow> \<forall>n s h. get_int_pre (s, h) es Pre \<longrightarrow> ressafe n (ers, (EvtSys es)) s h \<Gamma> Q"
  apply (simp add: reCSL_def)
proof(intro allI impI)
  fix n s h
  assume a0: "  \<forall>re\<in>es. user_revent (resources_re ers re) \<and>
          (\<forall>n s h. (s, h) \<Turnstile> Pre re \<longrightarrow> resafe n (resources_re ers re) s h \<Gamma> (Post re))"
  and    a1: "\<forall>re\<in>es. Post re \<sqsubseteq> Q"
  and    a2: "\<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<sqsubseteq> Pre (aa, ba)"
  and    a3: "get_int_pre (s, h) es Pre"
  then show "ressafe n (ers, EvtSys es) s h \<Gamma> Q"
    apply (induct n arbitrary: s h, simp_all)
    apply (rule conjI)
     apply (simp add: esaborts.simps resaborts_def)
    apply (rule conjI)
     apply (simp add: reaccesses_def resaccesses_def)
    apply (clarify, erule resred.cases, simp_all)
    apply (simp add: resllocked_def resources_re_def user_revent_def rellocked_def)
    apply (subgoal_tac "user_event e")
    apply (rule_tac x = "ha" in exI, clarsimp)
    apply (rule_tac Q = "Post (rs, e)" in ressafe_EvtSeq)
      apply (subgoal_tac "(ab, ha) \<Turnstile> Pre (rs, e)")
       apply auto[1]
      apply (simp add: get_int_pre_def)
     apply (clarsimp, drule_tac a = "s'" and b = "h'" in mall2_impD)
      apply (metis a2 pre_conj prod.exhaust_sel)
    using ressafe_mon apply blast
    by auto
qed

theorem rule_rEvtSys :  "\<lbrakk>\<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re)} (resources_re ers re) {Post re};
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q; \<forall> re \<in> es. P \<sqsubseteq> (Pre re); 
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} (ers, (EvtSys es)) {Q}"
  apply (simp add: resCSL_def)
  apply (rule conjI, simp add: reCSL_def resources_re_def user_resys_def user_revent_def)
  apply (clarsimp, drule ressafe_EvtSys, simp_all)
  by (simp add: pre_conj)

lemma ressafe_conseq : "\<lbrakk> ressafe n res s h \<Gamma> Q; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> ressafe n res s h \<Gamma> Q'"
  apply (induct n arbitrary: res s h, simp)
  apply (clarsimp, simp add : implies_def)
  apply (erule resred.cases, simp_all, clarify)
    apply (drule_tac a = "hJ" and b = "hF" and c = "ers" and d = "EvtSeq (ae, be) res" 
          and e = "af" and f = "bf" in all6_impD)
     apply (simp add: resred.red_EvtSeq1)
    apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
   apply (clarsimp, drule_tac a = "hJ" and b = "hF" and c = "ers" 
          and d = "res" and e = "ad" and f = "h ++ hJ ++ hF" in all6_impD)
    apply (simp add: resred.red_EvtSeq2)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (clarsimp, drule_tac a = "hJ" and b = "hF" and c = "ers" and 
        d = "EvtSeq (ers @ rs, e) (EvtSys revts)" and e = "ac" and f = "h ++ hJ ++ hF" in all6_impD)
   apply (simp add: resred.red_EvtSet)
  apply (simp add: resllocked_def, clarify, rule_tac x = "h'" in exI, simp)
  done

theorem rule_resconseq : "\<lbrakk> P \<sqsubseteq> P'; Q' \<sqsubseteq> Q; \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P'} res {Q'} \<rbrakk> \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} res {Q}"
  by (meson implies_def resCSL_def ressafe_conseq)

end