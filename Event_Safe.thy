theory Event_Safe
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
   apply (drule_tac a = "hJ" and b = "hF" and c = "AnonyEvent C'" 
          and d = "ab" and e = "bb" in all5_impD)
    apply (simp add: ered.red_AnonyEvt)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "AnonyEvent C" 
          and d = "a" and e = "b" in all5_impD)
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
  apply (drule_tac a = "hJ" and b = "hF" and c = "AnonyEvent C'" 
        and d = "ac" and e = "bc" in all5_impD)
   apply (simp add: ered.red_AnonyEvt)
  apply (simp add : rellocked_def, clarify)
  apply (rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  done

theorem rule_rInner: "\<Gamma> \<turnstile> {P} C {Q} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} (rs, AnonyEvent C) {Q}"
  using eCSL_def reCSL_def resafe_AnonyEvt rule_Inner user_revent_def by auto

theorem rule_rBasicEvt: "\<Gamma> \<turnstile> {Aconj P (Apure guard)} (Cresources rs C) {Q}
                     \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} (rs, BasicEvent (guard, C)) {Q}"
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
   apply (drule_tac a = "hJ" and b = "hF" and c = "rs" and d = "AnonyEvent C'" 
          and e = "ad" and f = "bd" in all6_impD)
  apply (simp add: rered.red_AnonyEvt)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "rs" and d = "AnonyEvent (Cresources rs C)" 
         and e = "ab" and f = "bb" in all6_impD)
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
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> (Q ** (Aistar (map \<Gamma> (esllocked esys)))) 
                \<longrightarrow> essafe m esys s' h' \<Gamma> R\<rbrakk> 
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
    apply (drule_tac a = "hJ" and b = "hF" and c = "EvtSeq (ac, bc) res" 
          and d = "ad" and e = "bd" in all5_impD)
     apply (simp add: esred.red_EvtSeq1)
    apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
   apply (drule_tac a = "hJ" and b = "hF" and c = "res" and d = "a" and e = "b" in all5_impD)
    apply (simp add: esred.red_EvtSeq2)
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "EvtSeq re (EvtSys revts)" and d = "a" 
        and e = "b" in all5_impD)
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
                        \<Longrightarrow> \<forall>n s h. get_int_pre (s, h) es Pre
                             \<longrightarrow> ressafe n (ers, (EvtSys es)) s h \<Gamma> Q"
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

primrec 
  pessafe :: "nat \<Rightarrow>paresys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
  where
  "pessafe 0 pes s h \<Gamma> Q = True"
| "pessafe (Suc n) pes s h \<Gamma> Q =  (
 (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> pesaborts pes (s, h ++ hF))
\<and> (\<forall>hJ hF pes' \<sigma>'. 
      pesred pes (s, h ++ hJ ++ hF) pes' \<sigma>'
    \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (pesllocked pes') (pesllocked pes)
    \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
    \<longrightarrow> (\<exists>h' hJ'.
            snd \<sigma>' = h' ++ hJ' ++ hF
          \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
          \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (pesllocked pes) (pesllocked pes')
          \<and> pessafe n pes' (fst \<sigma>') h' \<Gamma> Q)))"


primrec hplus_list :: "heap list \<Rightarrow> heap"
  where
    "hplus_list     [] = Map.empty"
  | "hplus_list (x # l)  =  x ++ (hplus_list l)"
                                                             

lemma hplus_list_expand : "\<lbrakk> \<forall>x y. x \<in> set l \<and> y \<in> set l \<and> x \<noteq> y \<longrightarrow> disjoint (dom x) (dom y); r \<in> set l\<rbrakk> 
      \<Longrightarrow> hplus_list l = r ++  hplus_list (removeAll r l)"
  apply (induct l, simp, clarsimp) 
  apply (rule conjI, clarsimp)
  apply (metis map_add_assoc map_add_subsumed1 map_le_map_add removeAll_id)
  apply (case_tac "r \<in> set l", clarsimp)
   apply (simp add: map_add_assoc map_add_commute)
  by simp

lemma disjoint_hplus_list : " disjoint (dom (hplus_list l)) (dom h)
                       \<longleftrightarrow> (\<forall>r \<in> set l.  disjoint (dom r) (dom h))"
proof
  assume a0 :"disjoint (dom (hplus_list l)) (dom h)"
  then show  "(\<forall>r\<in>set l. disjoint (dom r) (dom h))"
    by (induct l, simp_all)
next
  assume a0 :"\<forall>r \<in> set l.  disjoint (dom r) (dom h)"
  then show "disjoint (dom (hplus_list l)) (dom h)"
    by (induct l, simp_all)
qed

primrec disjoint_heap_with_list :: "heap \<Rightarrow> heap list \<Rightarrow> bool"
  where
    "disjoint_heap_with_list h [] = True"                              
  | "disjoint_heap_with_list h (x # xs) = 
    (disjoint (dom h) (dom x) \<and> disjoint_heap_with_list h xs)"

lemma disjoint_heap_with_equiv1 : "disjoint_heap_with_list a l 
                               \<longleftrightarrow> (\<forall>x \<in> set l. disjoint (dom a) (dom x))"
  apply (induct l, simp)
  by auto

lemma disjoint_heap_with_equiv2 : "disjoint_heap_with_list a l 
                              \<longleftrightarrow> (\<forall> k < length l.  disjoint (dom a) (dom (l ! k)))"
  by (metis disjoint_heap_with_equiv1 in_set_conv_nth)

lemma disjoint_with_hplus :
      "disjoint_heap_with_list a l \<Longrightarrow> disjoint (dom a) (dom (hplus_list l))"
  by (simp add: disjoint_hplus_list disjoint_heap_with_equiv1 disjoint_search(1))

primrec disjoint_heap_list :: "heap list \<Rightarrow> bool"
  where
  "disjoint_heap_list [] = True"
| "disjoint_heap_list (x # xs) = ((disjoint_heap_with_list x xs) \<and> (disjoint_heap_list xs))"

lemma disjoint_hplus_list1 : "\<lbrakk>k < length l; disjoint (dom (hplus_list l)) (dom hF)\<rbrakk> 
       \<Longrightarrow> disjoint (dom (l ! k)) (dom hF)"
  by (simp add: disjoint_hplus_list)

lemma disjoint_hplus_list2 : 
      "\<lbrakk> k < length l; disjoint (dom (hplus_list l)) (dom hF); l' = l[k := Map.empty]\<rbrakk> 
       \<Longrightarrow> disjoint (dom (hplus_list l')) (dom hF)"
proof-
  assume a0: "k < length l"
  and    a1: " disjoint (dom (hplus_list l)) (dom hF)"
  and    a2: "l' = l[k := Map.empty]"
  then have "\<forall>k < length l. disjoint (dom (l ! k)) (dom hF)"
    by (simp add: disjoint_hplus_list1)
  then have "\<forall>k < length l'. disjoint (dom (l ! k)) (dom hF)"
    by (simp add: a2)
  then show ?thesis
    by (metis (mono_tags, lifting) a1 a2 disjoint_hplus_list disjoint_search(1) disjoint_simps(2) 
              dom_empty insert_iff set_update_subset_insert subset_eq)
qed

lemma disjoint_remove_property : "disjoint_heap_list l 
              \<Longrightarrow>  \<forall>k. k < length l \<longrightarrow> disjoint_heap_with_list (l ! k) (l[k:= Map.empty])"
  apply (intro allI, induct l, simp)
  apply (case_tac k, simp, clarsimp)
  using disjoint_heap_with_equiv2 disjoint_search(1) by blast

lemma disjoint_list_equiv : "disjoint_heap_list l \<longleftrightarrow> 
                            (\<forall>k1 k2. k1 < length l \<and> k2 < length l \<and> k1 \<noteq> k2
                            \<longrightarrow> disjoint (dom (l ! k1)) (dom (l ! k2)))"
proof(induct l)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    apply (auto simp add: Cons nth_Cons split: nat.split_asm)
      apply (metis (no_types, lifting) disjoint_hplus_list1 
              Nitpick.case_nat_unfold One_nat_def Suc_pred 
              disjoint_with_hplus disjoint_search(1) less_Suc0 not_less_eq)
     apply (metis disjoint_heap_with_equiv2 not_less_eq not_less_zero)
    by blast
qed

lemma disjoint_hplus_list3 : "\<lbrakk>disjoint_heap_list l; k < length l;
                              l' = l[k := Map.empty]\<rbrakk> 
                          \<Longrightarrow> disjoint (dom (l ! k)) (dom (hplus_list l'))"
  by (simp add: disjoint_with_hplus disjoint_remove_property)

lemma hplus_list_exchange : "disjoint_heap_list l \<Longrightarrow> 
               \<forall>k. k < length l \<longrightarrow> (l ! k) ++ (hplus_list (l[k:= Map.empty])) = hplus_list l"
  apply (induct l, simp)
  apply (intro allI impI)
  apply (case_tac k, simp, clarsimp)
  apply (drule_tac a = "nat" in allD, simp)
proof-
  fix a l nat
  assume a0: "nat < length l"
  and    a1: "disjoint_heap_with_list a l"
  and    a2: "disjoint_heap_list l"
  and    a3: " l ! nat ++ hplus_list (l[nat := Map.empty]) = hplus_list l"
  then have "disjoint (dom a) (dom (l ! nat))"
    by (simp add: disjoint_heap_with_equiv2)
  moreover have "disjoint (dom a) (dom (hplus_list (l[nat := Map.empty])))"
    by (metis a0 a1 disjoint_with_hplus disjoint_search(1) disjoint_hplus_list2)
  ultimately show "l ! nat ++ (a ++ hplus_list (l[nat := Map.empty])) = a ++ hplus_list l"
    by (simp add: a3 map_add_left_commute)
qed

lemma disjoint_locked_heap_update : 
        "\<lbrakk> \<forall>k'. k' < length l \<and> k' \<noteq> k \<longrightarrow> disjoint (dom x) (dom (l ! k'));
        disjoint_heap_list l ; k < length l; l' = l[k := x] \<rbrakk>
    \<Longrightarrow> disjoint_heap_list l'"
  by (metis disjoint_list_equiv disjoint_search(1) length_list_update 
      nth_list_update_eq nth_list_update_neq)

lemma disjoint_locked_heap_update1 : "\<lbrakk> disjoint (dom x) (dom (hplus_list (l[k := Map.empty])));
        disjoint_heap_list l ; k < length l; l' = l[k := x] \<rbrakk>
    \<Longrightarrow> disjoint_heap_list l'"
  apply (rule disjoint_locked_heap_update, simp_all)
  by (metis disjoint_search(1) length_list_update nth_list_update_neq disjoint_hplus_list1)

lemma pessafe_hsimps : "\<lbrakk>disjoint_heap_list l;  k < length l;
                        disjoint (dom (hplus_list l)) (dom hF)\<rbrakk> 
               \<Longrightarrow> (l ! k) ++ (hplus_list (l[k := Map.empty]) ++ hF) = hplus_list l ++ hF"
  by (simp add: hplus_list_exchange map_add_assoc)

lemma pessafe_noaborts : "\<lbrakk>\<forall>k<length l. (\<forall>hF. disjoint (dom (l ! k)) (dom hF) 
                          \<longrightarrow> \<not> resaborts (pes ! k) (a, l ! k ++ hF)); 
                          disjoint_heap_list l; k < length l;
                        disjoint (dom (hplus_list l)) (dom hF)\<rbrakk>
                  \<Longrightarrow> \<not> resaborts (pes ! k) (a, hplus_list l ++ hF)"
  apply (drule_tac a = "k" in allD, clarsimp)
  apply (drule_tac a = "hplus_list (l[k := Map.empty]) ++ hF" in all_impD)
   apply (simp add: disjoint_hplus_list3 disjoint_hplus_list1)
  by (simp add: pessafe_hsimps)

lemma pessafe_hsimps2 : "\<lbrakk>disjoint_heap_list l; k < length l;
                        disjoint (dom (hplus_list l)) (dom hF); 
                        disjoint (dom (hplus_list l)) (dom hJ); 
                        disjoint (dom hJ) (dom hF)\<rbrakk>
                    \<Longrightarrow> l ! k ++ hJ ++ (hplus_list (l[k := Map.empty]) ++ hF)
                      = hplus_list l ++ hJ ++ hF"
proof-
  assume a0: "disjoint_heap_list l"
  and    a1: "disjoint (dom (hplus_list l)) (dom hF)"
  and    a2: "disjoint (dom (hplus_list l)) (dom hJ)"
  and    a3: "disjoint (dom hJ) (dom hF)"
  and    a4: "k < length l"
  then have "disjoint (dom (l ! k)) (dom hF)  \<and> disjoint (dom (l ! k)) (dom hJ) 
          \<and> (l ! k) ++ (hplus_list (l[ k:= Map.empty])) = hplus_list l"
    by (simp add: disjoint_hplus_list1 hplus_list_exchange)
  then show ?thesis 
    by (metis a2 map_add_assoc map_add_commute)
qed

primrec disjoint_locked_with_list :: "resys \<Rightarrow> resys list \<Rightarrow> bool"
  where
    "disjoint_locked_with_list r [] = True"
  | "disjoint_locked_with_list r ( x # xs) = (disjoint (reslocked r) (reslocked x)
                                              \<and> disjoint_locked_with_list r xs)"

lemma disjoint_locked_with_equiv1 : "disjoint_locked_with_list r l 
                                 \<longleftrightarrow> (\<forall>x \<in> set l. disjoint (reslocked r) (reslocked x))"
  by (induct l, simp_all)

lemma disjoint_locked_with_equiv2 : "disjoint_locked_with_list r l 
                                \<longleftrightarrow> (\<forall> k < length l. disjoint (reslocked r) (reslocked (l ! k)))"
  by (metis disjoint_locked_with_equiv1 in_set_conv_nth)

lemma disjoint_locked_with_property : "disjoint_locked_with_list r l 
                              \<Longrightarrow> disjoint (reslocked r) (peslocked l)"
  apply (induct l, simp add: empty_peslock)
  by (simp add: induct_peslock)

primrec disjoint_locked_list :: "resys list \<Rightarrow> bool"
  where
    "disjoint_locked_list [] = True"
  | "disjoint_locked_list (x # xs) = ((disjoint_locked_with_list x xs)
                                  \<and> disjoint_locked_list xs)"

primrec disjoint_locked_between_list :: "resys list \<Rightarrow> resys list \<Rightarrow> bool"
  where
    "disjoint_locked_between_list [] l = True"
  | "disjoint_locked_between_list (x # xs) l = ((disjoint_locked_with_list x l)
                                              \<and> (disjoint_locked_between_list xs l))"

lemma disjoint_locked_between_equiv1 : "disjoint_locked_between_list l1 l2 
                                 \<longleftrightarrow> (\<forall>x \<in> set l1. disjoint_locked_with_list x l2)"
  by (induct l1, simp_all)

lemma disjoint_locked_between_equiv2 : "disjoint_locked_between_list l1 l2 
                                 \<longleftrightarrow> (\<forall> k < length l1. disjoint_locked_with_list (l1 ! k) l2)"
  by (metis disjoint_locked_between_equiv1 in_set_conv_nth)

lemma disjoint_locked_between_property : 
    "disjoint_locked_between_list l1 l2 \<Longrightarrow> disjoint (peslocked l1) (peslocked l2)"
  apply (induct l1, simp add : empty_peslock)
  by (simp add: disjoint_locked_with_property induct_peslock)

lemma disjoint_locked_list_equiv : "disjoint_locked_list l \<longleftrightarrow> 
                            (\<forall>k1 k2. k1 < length l \<and> k2 < length l \<and> k1 \<noteq> k2
                            \<longrightarrow> disjoint (reslocked (l ! k1)) (reslocked (l ! k2)))"
proof(induct l)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    apply (auto simp add: Cons nth_Cons split: nat.split_asm)
      defer
      apply (metis Suc_mono disjoint_locked_with_equiv2 less_numeral_extra(3) zero_less_Suc)
     apply blast
    apply (case_tac k1, clarsimp)
     apply (case_tac k2, clarsimp)
     apply (simp add: disjoint_locked_with_equiv2)
    apply (case_tac k2, clarsimp)
    using disjoint_locked_with_equiv2 disjoint_search(1) apply blast
    by simp
qed

lemma disjoint_with_res : "disjoint_locked_with_list r l  
                           \<Longrightarrow> disjoint (reslocked r) (peslocked l)"
  apply (induct l, simp add: empty_peslock)
  by (simp add: induct_peslock)

lemma disjoint_with_pes : "disjoint_locked_between_list l1 l2 
                           \<Longrightarrow> disjoint (peslocked l1) (peslocked l2)"
  apply (induct l1, simp add: empty_peslock)
  by (simp add: disjoint_with_res induct_peslock)

lemma disjoint_with_take : "\<lbrakk> disjoint_locked_list l; k < length l\<rbrakk> \<Longrightarrow>
                            disjoint_locked_with_list (l ! k) (take k l)"
  by (simp add: disjoint_locked_list_equiv disjoint_locked_with_equiv2)

lemma disjoint_with_drop : "\<lbrakk> disjoint_locked_list l; k < length l\<rbrakk> \<Longrightarrow>
                            disjoint_locked_with_list (l ! k) (drop (Suc k) l)"
  by (simp add: disjoint_locked_list_equiv disjoint_locked_with_equiv2)

lemma disjoint_between_take_drop : "\<lbrakk> disjoint_locked_list l; k < length l\<rbrakk> \<Longrightarrow>
                            disjoint_locked_between_list (take k l) (drop (Suc k) l)"
  by (simp add: disjoint_locked_list_equiv 
          disjoint_locked_between_equiv2 disjoint_locked_with_equiv2)

lemma envs_app' : "disjoint (set a) (set b) \<Longrightarrow> disjoint (set a) (set c) \<Longrightarrow> disjoint (set b) (set c)
    \<Longrightarrow> envs \<Gamma> (a @ b @ c) (a @ b' @ c) = envs \<Gamma> b b'"
  by (simp add: envs_app(1) envs_app(2))

lemma disjoint_locked_list_update : 
        "\<lbrakk> \<forall>k'. k' < length l \<and> k' \<noteq> k \<longrightarrow> disjoint (reslocked re) (reslocked (l ! k'));
        disjoint_locked_list l ; k < length l \<rbrakk>
    \<Longrightarrow> disjoint_locked_list (l [k := re])"
  apply (simp add: disjoint_locked_list_equiv, clarify)
  apply (case_tac "k1 = k", simp)
  apply (case_tac "k2 = k")
   apply auto[1]
  by simp

lemma pesllocked_cancel : "\<lbrakk>disjoint_locked_list pes; pes ! k = res;
             pes' = pes[k := res']; k < length pes\<rbrakk>
        \<Longrightarrow> envs \<Gamma> (pesllocked pes) (pesllocked pes')
          = envs \<Gamma> (resllocked res) (resllocked res')"
  apply (simp add: peslocked_split)
  apply (rule envs_app')
    apply (metis disjoint_locked_with_property disjoint_search(1)
              disjoint_with_take peslocked_def reslocked_eq)
   apply (simp add: peslocked_eq disjoint_between_take_drop disjoint_locked_between_property)
  by (metis disjoint_locked_with_property disjoint_with_drop peslocked_def reslocked_eq)

lemma pessafe_pesllocked_cancel :
        "\<lbrakk> disjoint_locked_list pes; pes' = pes[k := res']; pes ! k = res; k < length pes;
         \<forall>k'. k' < length pes \<and> k \<noteq> k' \<longrightarrow> disjoint (reslocked res') (reslocked (pes ! k'))\<rbrakk>
        \<Longrightarrow> envs \<Gamma> (pesllocked pes') (pesllocked pes)
          = envs \<Gamma> (resllocked res') (resllocked res)"
  apply (rule pesllocked_cancel, simp_all)
  using disjoint_locked_list_update apply blast
  by auto

lemma pessafe: 
" \<lbrakk>\<forall>k. k < length pes \<longrightarrow> ressafe n (pes ! k) s (hs ! k) \<Gamma> (Qs ! k);
   disjoint_heap_list hs; disjoint_locked_list pes;
   \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvA (Qs ! k1) \<union> fvAs \<Gamma>) (wrREsv (pes ! k2));
    length pes = length hs\<rbrakk>
   \<Longrightarrow> pessafe n pes s (hplus_list hs) \<Gamma> (Aistar Qs)"
  apply (induct n arbitrary: pes s hs, simp, clarsimp)
  apply (rule conjI, clarsimp, erule pesaborts.cases, clarsimp)
    apply (simp add: pessafe_noaborts, clarsimp)
  apply (meson disjoint_list_equiv disjoint_search(2) disjoint_search(4) reswrites_accesses)
  apply (clarsimp, erule pesred.cases, simp)
  apply (frule_tac a = "k" in allD, clarsimp)
  apply (drule_tac a = "hJ" and b = "(hplus_list (hs[ k:= Map.empty]) ++ hF)"
          and c = "ac" and d = "bc" and e = "ad" and f = "bd" in all6_impD)
   apply (simp add: pessafe_hsimps2)
  apply (drule imp2D)
    apply (simp add: pessafe_pesllocked_cancel)
   apply (rule conjI, simp add: disjoint_hplus_list1)
   apply (rule conjI, simp add: disjoint_hplus_list3 disjoint_hplus_list1 )
    apply (simp add: disjoint_hplus_list3)
   apply (metis (no_types, lifting) disjoint_search(1) 
          disjoint_simps(4) dom_map_add hplus_list_exchange)
  apply (clarsimp, rule_tac x = "h' ++ (hplus_list (hs[k := Map.empty]))" and y = "hJ'" in ex2I, simp)
  apply (rule conjI)
   apply (metis map_add_assoc map_add_commute)
  apply (rule conjI) apply auto[1]
  apply (rule conjI)
   apply (simp add: disjoint_hplus_list2)
  apply (rule conjI)
  apply (simp add: pesllocked_cancel)
   apply (drule resred_properties)
   apply (clarsimp, drule_tac a = "pesa[k := (ac, bc)]" and b = "ad"
                              and c = "hs[k := h']" in mall3_impD)
   apply (clarsimp, case_tac "ka = k", simp, simp)
   apply (rule_tac s = "ab" in ressafe_agrees)
    apply (rule_tac n = "Suc n" in ressafe_mon, simp, simp)
   apply (drule_tac a = "ka" and b = "k" in all2_impD, simp, simp)
   apply auto[1]
  apply (drule mimp4D)
  using disjoint_locked_heap_update1 apply presburger
  using disjoint_locked_list_update apply force
    apply (clarsimp, drule_tac a = "k1" and b = "k2" in all2_impD, simp)
    apply (case_tac "k1 \<noteq> k") apply (case_tac "k2 \<noteq> k", simp)
     apply auto[1] apply auto[1]
   apply simp
  apply (subgoal_tac "h' ++ hplus_list (hs[k := Map.empty]) = hplus_list (hs[k := h'])", simp)
  by (metis disjoint_locked_heap_update1 hplus_list_exchange 
        length_list_update list_update_overwrite nth_list_update_eq)

primrec user_pesys :: "paresys \<Rightarrow> bool"
  where "user_pesys [] = True"
  |     "user_pesys (x # xs) = ((user_resys x) \<and> (user_pesys xs))"

primrec wf_pesys :: "paresys \<Rightarrow> bool"
  where "wf_pesys [] = True"
  |     "wf_pesys (x # xs) = ((wf_resys x) \<and> (wf_pesys xs) \<and> 
    (disjoint_locked_list (x # xs)))"

lemma wf_peslocked : "wf_pesys pes \<Longrightarrow> disjoint_locked_list pes"
  by (induct pes, simp, simp)

lemma user_pesysD : "user_pesys pes \<Longrightarrow> wf_pesys pes \<and> peslocked pes = {}"
  apply (induct pes, simp add: empty_peslock)
  apply (rule conjI, simp add: wf_pesys.simps)
   apply (rule conjI, simp add: user_resysD)
   apply (metis disjoint_locked_list.simps(1) disjoint_locked_with_equiv1 disjoint_simps(1) 
          list.exhaust user_resysD wf_pesys.simps(2))
  by (simp add: induct_peslock user_resysD)

lemma user_pesys_wf[intro] : "user_pesys pes \<Longrightarrow> wf_pesys pes"
  by (drule user_pesysD, simp)

lemma user_pesys_llocked[simp]: "user_pesys pes \<Longrightarrow> pesllocked pes = []"
  by (drule user_pesysD, simp add: peslocked_def)

lemma user_pesysI[simp] : "\<forall>k < length pes. user_resys (pes ! k) \<Longrightarrow> user_pesys pes"
  apply (induct pes, simp)
  by force

definition 
  pesCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> paresys \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>p\<^sub>e\<^sub>s { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>p\<^sub>e\<^sub>s {P} pes {Q} \<equiv> (user_pesys pes) \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> pessafe n pes s h \<Gamma> Q)"

lemma split_Aistar : "(s, h) \<Turnstile> Aistar Ps \<Longrightarrow> (\<exists>hs. length hs = length Ps  \<and> disjoint_heap_list hs 
                          \<and> (\<forall>k < length Ps. (s, hs ! k) \<Turnstile> Ps ! k ) \<and> hplus_list hs = h)" 
  apply (induct Ps arbitrary: s h, simp, clarsimp)
  apply (drule mall2_impD, simp, clarsimp)
  apply (rule_tac x = "h1 # hs" in exI, simp)
  apply (rule conjI) 
  using disjoint_heap_with_equiv2 disjoint_hplus_list1 disjoint_search(1) apply blast
  using less_Suc_eq_0_disj by auto

theorem rule_pes : " \<lbrakk>\<forall>k. k < length pes \<longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s  {Ps ! k} (pes ! k) {Qs ! k};
                  \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
                  \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvA (Qs ! k1) \<union> fvAs \<Gamma>) (wrREsv (pes ! k2));
                  length pes = length Ps \<rbrakk> 
                  \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {Aistar Ps} pes {Aistar Qs}"
  apply (simp add: resCSL_def pesCSL_def, clarify)
  apply (drule split_Aistar, clarify)
  apply (rule pessafe, simp_all)
  apply (simp add: user_pesysD wf_peslocked)
  by blast

lemma pessafe_conseq : "\<lbrakk> pessafe n pes s h \<Gamma> Q; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> pessafe n pes s h \<Gamma> Q'"
    apply (induct n arbitrary: pes s h, simp)
  apply (clarsimp, simp add : implies_def)
  apply (erule pesred.cases, simp_all, clarsimp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "pesa[k := (ac, bc)]" 
          and d = "ad" and e = "bd" in all5_impD)
  using pesred.red_Par apply blast
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  done

theorem rule_pesconseq : "\<lbrakk> P \<sqsubseteq> P'; Q' \<sqsubseteq> Q; \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {P'} pes {Q'} \<rbrakk> \<Longrightarrow>  \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {P} pes {Q}"
  apply (simp add: pesCSL_def)
  using implies_def pessafe_conseq by blast

corollary rule_pes2' : "\<lbrakk>\<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P1} res1 {Q1} ; \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P2} res2 {Q2};
           disjoint ((fvREsv res1) \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrREsv res2);
           disjoint ((fvREsv res2) \<union> fvA Q2 \<union> fvAs \<Gamma>) (wrREsv res1)\<rbrakk>
           \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {Aistar [P1, P2]} [res1, res2] {Aistar [Q1, Q2]}"
  apply (rule rule_pes, simp_all add: less_Suc_eq)
  by auto

corollary rule_pes2 : "\<lbrakk>\<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P1} res1 {Q1} ; \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P2} res2 {Q2};
           disjoint ((fvREsv res1) \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrREsv res2);
           disjoint ((fvREsv res2) \<union> fvA Q2 \<union> fvAs \<Gamma>) (wrREsv res1)\<rbrakk>
           \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {P1 ** P2} [res1, res2] {Q1 ** Q2}"
  apply (rule_tac P' = "Aistar [P1, P2]" and Q' = "Aistar [Q1, Q2]" in rule_pesconseq)
    apply (simp add: implies_def)
   apply (simp add: implies_def)
  using rule_pes2' by auto

primrec 
  rpessafe :: "nat \<Rightarrow> rparesys \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> (rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> bool"
  where
  "rpessafe 0 rpes s h \<Gamma> Q = True"
| "rpessafe (Suc n) rpes s h \<Gamma> Q =  (
 (\<forall>hF. disjoint (dom h) (dom hF) \<longrightarrow> \<not> rpesaborts rpes (s, h ++ hF))
\<and> (\<forall>hJ hF rpes' \<sigma>'. 
      rpesred rpes (s, h ++ hJ ++ hF) rpes' \<sigma>'
    \<longrightarrow> (s, hJ) \<Turnstile> envs \<Gamma> (rpesllocked rpes') (rpesllocked rpes)
    \<longrightarrow> (disjoint (dom h) (dom hJ) \<and> disjoint (dom h) (dom hF) \<and> disjoint (dom hJ) (dom hF))
    \<longrightarrow> (\<exists>h' hJ'.
            snd \<sigma>' = h' ++ hJ' ++ hF
          \<and> disjoint (dom h') (dom hJ') \<and> disjoint (dom h') (dom hF) \<and> disjoint (dom hJ') (dom hF)
          \<and> (fst \<sigma>', hJ') \<Turnstile> envs \<Gamma> (rpesllocked rpes) (rpesllocked rpes')
          \<and> rpessafe n rpes' (fst \<sigma>') h' \<Gamma> Q)))"

definition user_rpesys :: "rparesys \<Rightarrow> bool"
  where "user_rpesys rpes = user_pesys (resources_pes (fst rpes) (snd rpes))"

definition wf_rpesys :: "rparesys \<Rightarrow> bool"
  where "wf_rpesys rpes = wf_pesys (resources_pes (fst rpes) (snd rpes))"

lemma user_rpesys_equiv: "user_pesys (resources_pes rs pes) \<Longrightarrow>  user_rpesys (rs, pes)"
  by (simp add: user_rpesys_def)

lemma wf_rpesys_equiv: "wf_pesys (resources_pes rs pes) \<Longrightarrow>  wf_rpesys (rs, pes)"
  by (simp add: wf_rpesys_def)

definition 
  rpesCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> rparesys \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s {P} rpes {Q} \<equiv> (user_rpesys rpes) \<and> (\<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> rpessafe n rpes s h \<Gamma> Q)"

lemma res_pes_update : "k < length pesa \<Longrightarrow>
      resources_pes pres pesa[k := (pres @ ers, es)] = resources_pes pres (pesa[k := (ers, es)])"
  apply (induct pesa arbitrary: k, simp)
  apply (case_tac "k", simp add: resources_res_def)
  apply (simp add: list_update_code)
  done

lemma rpes_equiv : 
  "pessafe n (resources_pes rs pes) s h \<Gamma> Q \<Longrightarrow> rpessafe n (rs, pes) s h \<Gamma> Q"
  apply (induct n arbitrary : pes s h, simp, clarsimp)
  apply (rule conjI, simp add: rpesaborts_def)
  apply (clarsimp, erule rpesred.cases, simp)
  apply (drule_tac a = "hJ" and b = "hF" and c = "resources_pes pres pesa[k := (pres @ ers, es')]" 
        and d = "aa" and e = "ba" in all5_impD, simp)
   apply (rule pesred.red_Par, simp, simp)
    apply (simp add: res_pes_property resources_res_def)
   apply (simp add: res_pes_property resources_res_def)
  apply (drule imp2D, simp add: rpesllocked_def)
    apply (simp add: res_pes_update, simp, clarsimp)
  apply (rule_tac x = "h'" and y = "hJ'" in ex2I, clarsimp)
  apply (simp add: rpesllocked_def res_pes_update)
  done

theorem rule_rpes1 : " \<lbrakk>\<forall>k. k < length pes \<longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s  {Ps ! k} (resources_res rs) (pes ! k) {Qs ! k};
                  \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
                  \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvA (Qs ! k1) \<union> fvAs \<Gamma>) (wrREsv (pes ! k2));
                  length pes = length Ps \<rbrakk> 
                  \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {Aistar Ps} (resources_pes rs pes) {Aistar Qs}"
  apply (rule rule_pes, simp_all, clarify)
   apply (simp add: res_pes_property)
  using res_pes_property by auto

theorem rule_rpes : " \<lbrakk>\<forall>k. k < length pes \<longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s  {Ps ! k} (resources_res rs) (pes ! k) {Qs ! k};
                  \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
                  \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvA (Qs ! k1) \<union> fvAs \<Gamma>) (wrREsv (pes ! k2));
                  length pes = length Ps \<rbrakk> 
                  \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s {Aistar Ps} (rs, pes) {Aistar Qs}"
  apply (drule rule_rpes1, simp_all)
   apply auto[1]
  apply (simp add: pesCSL_def rpesCSL_def rpes_equiv user_rpesys_equiv)
  done

lemma rpessafe_conseq : "\<lbrakk> rpessafe n (rs, pes) s h \<Gamma> Q; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> rpessafe n (rs, pes) s h \<Gamma> Q'"
    apply (induct n arbitrary: pes s h, simp)
  apply (clarsimp, simp add : implies_def)
  apply (erule rpesred.cases, simp_all, clarsimp)
  apply (drule_tac a = "hJ" and b = "hF" and  c = "rs" and 
          d = "pesa[k := (ers, es')]" and e = "ac" and f = "bc" in all6_impD)
  using rpesred.red_Par apply blast
   apply (clarsimp, rule_tac x = "h'" and y = "hJ'" in ex2I, simp)
  done

theorem rule_rpesconseq : "\<lbrakk> P \<sqsubseteq> P'; Q' \<sqsubseteq> Q; \<Gamma>  \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s {P'} rpes {Q'} \<rbrakk> \<Longrightarrow>  \<Gamma>  \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s {P} rpes {Q}"
  apply (simp add: rpesCSL_def)
  by (metis implies_def rpessafe_conseq surj_pair)

corollary rule_rpes2' : "\<lbrakk>\<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P1} (resources_res rs res1) {Q1} ; 
                         \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P2} (resources_res rs res2) {Q2};
           disjoint ((fvREsv res1) \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrREsv res2);
           disjoint ((fvREsv res2) \<union> fvA Q2 \<union> fvAs \<Gamma>) (wrREsv res1)\<rbrakk>
           \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {P1 ** P2} (resources_pes rs [res1, res2]) {Q1 ** Q2}"
  apply (rule_tac P' = "Aistar [P1, P2]" and Q' = "Aistar [Q1, Q2]" in rule_pesconseq)
    apply (simp add: implies_def)
   apply (simp add: implies_def)
  using rule_pes2' by auto

corollary rule_rpes2 : "\<lbrakk>\<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P1} (resources_res rs res1) {Q1} ; 
                         \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P2} (resources_res rs res2) {Q2};
           disjoint ((fvREsv res1) \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrREsv res2);
           disjoint ((fvREsv res2) \<union> fvA Q2 \<union> fvAs \<Gamma>) (wrREsv res1)\<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s {P1 ** P2} (rs, [res1, res2]) {Q1 ** Q2}"
  apply (drule rule_rpes2', simp_all)
   apply auto[1]
  apply (simp add: pesCSL_def rpesCSL_def rpes_equiv user_rpesys_equiv)
  done

end

