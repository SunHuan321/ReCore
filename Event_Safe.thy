theory Event_Safe
  imports CSLsound Event_Computation
begin

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
    "\<Gamma> \<turnstile>\<^sub>e {P} e {Q} \<equiv> \<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> esafe n e s h \<Gamma> Q"


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

theorem rule_BasicEvt: "\<Gamma> \<turnstile> {Aconj (P ** (Aistar (map \<Gamma> (llocked C)))) (Apure guard)} C {Q} 
                    \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e {P} (BasicEvent (guard, C)) {Q}"
  apply (simp add: eCSL_def CSL_def)
proof (intro allI impI)
  fix n s h
  assume a1: "user_cmd C \<and>
       (\<forall>n s h.
           (\<exists>h1. (s, h1) \<Turnstile> P \<and> (\<exists>h2. (s, h2) \<Turnstile> Aistar (map \<Gamma> (llocked C)) \<and> h = h1 ++ h2 \<and> disjoint (dom h1) (dom h2))) \<and> bdenot guard s \<longrightarrow>
           safe n C s h \<Gamma> Q)" 
    and a2: "(s, h) \<Turnstile> P"
  then show "esafe n (BasicEvent (guard, C)) s h \<Gamma> Q"
    apply (induct n, simp_all)
    apply (rule conjI)
    using eaborts.cases apply blast
    apply (clarify, erule ered.cases, simp)
    apply (rule_tac x = "h ++hJ" in exI, clarify, simp)
    by (simp add: esafe_AnonyEvt)
qed

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
    "\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q} \<equiv> \<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> resafe n re s h \<Gamma> Q"

lemma resafe_AnonyEvent: "esafe n (AnonyEvent C) s h \<Gamma> Q  \<Longrightarrow> resafe n (rs, (AnonyEvent C)) s h \<Gamma> Q"
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
  using eCSL_def reCSL_def resafe_AnonyEvent rule_Inner by auto

theorem rule_rBasicEvt: "\<Gamma> \<turnstile> {Aconj (P ** (Aistar (map \<Gamma> (llocked (Cresources rs C)))))
             (Apure guard)} (Cresources rs C) {Q} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} (rs, BasicEvent (guard, C)) {Q}"
    apply (simp add: reCSL_def CSL_def)
proof (intro allI impI)
  fix n s h
  assume a1: " user_cmd C \<and>
       (\<forall>n s h.
           (\<exists>h1. (s, h1) \<Turnstile> P \<and> (\<exists>h2. (s, h2) \<Turnstile> Aistar (map \<Gamma> (list_minus (llocked C) rs)) \<and> h = h1 ++ h2 \<and> disjoint (dom h1) (dom h2))) \<and>
           bdenot guard s \<longrightarrow>
           safe n (Cresources rs C) s h \<Gamma> Q)" 
    and a2: "(s, h) \<Turnstile> P"
  then show " resafe n (rs, BasicEvent (guard, C)) s h \<Gamma> Q"
    apply (induct n, simp_all)
    apply (rule conjI)
    using eaborts.cases reaborts_def apply auto[1]
    apply (rule conjI)
    apply (simp add: reaccesses_def)
    apply (clarify, erule rered.cases, simp_all add: rellocked_def)
    apply (rule_tac x = "h ++hJ"  in exI, clarsimp)
    by (simp add: esafe_AnonyEvt resafe_AnonyEvent)
qed

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
    "\<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} esys {Q} \<equiv> \<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> essafe n esys s h \<Gamma> Q"

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

lemma essafe_EvtSeq' :"\<lbrakk>resafe n re s h \<Gamma> Q;
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Q \<longrightarrow> essafe m (EvtSys es) s' h' \<Gamma> R\<rbrakk> 
      \<Longrightarrow>  essafe n (EvtSeq re (EvtSys es)) s h \<Gamma> R"
  by (simp add: essafe_EvtSeq)

theorem rule_EvtSeq :"\<lbrakk>\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q};
                 \<Gamma> \<turnstile>\<^sub>e\<^sub>s {Q ** (Aistar (map \<Gamma> (esllocked esys)))} esys {R}\<rbrakk> 
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} (EvtSeq re esys) {R}"
  apply (auto simp add: reCSL_def esCSL_def intro!: essafe_EvtSeq)
  done

corollary rule_EvtSeq' :   "\<lbrakk>\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q};  \<Gamma> \<turnstile>\<^sub>e\<^sub>s {Q} (EvtSys es) {R} \<rbrakk> 
                        \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} (EvtSeq re (EvtSys es)) {R}"
  using esCSL_def rule_EvtSeq by auto

definition get_int_pre :: "state \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> assn) \<Rightarrow> bool"
  where "get_int_pre \<sigma> es Pre \<equiv> \<forall> re \<in> es.  \<sigma> \<Turnstile> (Pre re)" 

definition get_union_post :: "state \<Rightarrow> revent set \<Rightarrow> (revent \<Rightarrow> assn) \<Rightarrow> bool"
  where "get_union_post \<sigma> es Post \<equiv>  \<exists>re \<in> es. \<sigma> \<Turnstile> (Post re)" 

lemma pre_conj : "\<lbrakk> \<forall>re \<in> es. P \<sqsubseteq> (Pre re) ; \<sigma> \<Turnstile> P \<rbrakk> \<Longrightarrow> get_int_pre \<sigma> es Pre"
  using get_int_pre_def implies_def by blast

lemma post_dconj : "\<lbrakk>\<forall>re\<in>es. (Post re) \<sqsubseteq> Q; get_union_post \<sigma> es Post\<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> Q"
  using get_union_post_def implies_def by blast

lemma essafe_EvtSys : "\<lbrakk> \<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re) ** (Aistar (map \<Gamma> (rellocked re)))} re {Post re};
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q;
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow> \<forall>n s h. get_int_pre (s, h) es Pre \<longrightarrow> essafe n (EvtSys es) s h \<Gamma> Q"
  apply (simp add: reCSL_def)
proof(intro allI impI)
  fix n s h
  assume a0 : "\<forall>re\<in>es.
          \<forall>n s h.
             (\<exists>h1. (s, h1) \<Turnstile> Pre re \<and> (\<exists>h2. (s, h2) \<Turnstile> Aistar (map \<Gamma> (rellocked re)) \<and> h = h1 ++ h2 \<and> disjoint (dom h1) (dom h2))) \<longrightarrow>
             resafe n re s h \<Gamma> (Post re)"
  and    a1 : "\<forall>re\<in>es. Post re \<sqsubseteq> Q"
  and    a2 : "\<forall>a b aa ba. (a, b) \<in> es \<and> (aa, ba) \<in> es \<longrightarrow> Post (a, b) \<sqsubseteq> Pre (aa, ba)"
  and    a3 : "get_int_pre (s, h) es Pre"
  then show "essafe n (EvtSys es) s h \<Gamma> Q"
    apply (induct n arbitrary: s h, simp_all)
    apply (rule conjI)
     apply (meson esaborts.cases esys.simps(4))
    apply (clarify, erule esred.cases, simp_all)
    apply (rule_tac x = "ha ++ hJ" in exI, clarsimp)
  proof-
    fix n ha hJ hF aa ba ab
    assume a00: "(\<And>s h. get_int_pre (s, h) es Pre \<Longrightarrow> essafe n (EvtSys es) s h \<Gamma> Q)"
    and    a01: " get_int_pre (ab, ha) es Pre"
    and    a02: "(ab, hJ) \<Turnstile> Aistar (map \<Gamma> (rellocked (aa, ba)))"
    and    a03: "disjoint (dom ha) (dom hJ)"
    and    a04: "(aa, ba) \<in> es"
    then have "(ab, ha) \<Turnstile> Pre (aa, ba)" 
      by (simp add: get_int_pre_def)
    with a0  have "resafe n (aa, ba) ab (ha ++ hJ) \<Gamma> (Post (aa, ba))"
      using a02 a03 a04 by blast
    with a2 have "\<forall>re \<in> es. \<forall>\<sigma>. \<sigma> \<Turnstile> Post re \<longrightarrow> get_int_pre \<sigma> es Pre"
      using get_int_pre_def implies_def by auto
    then have "\<forall>s' h'. (s', h') \<Turnstile> Post (aa, ba) \<longrightarrow> essafe n (EvtSys es) s' h' \<Gamma> Q"
      using a00 a04 by auto
    then have "\<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Post (aa, ba) \<longrightarrow> essafe m (EvtSys es) s' h' \<Gamma> Q"
      using essafe_mon by blast
    then show "essafe n (EvtSeq (aa, ba) (EvtSys es)) ab (ha ++ hJ) \<Gamma> Q"
      using \<open>resafe n (aa, ba) ab (ha ++ hJ) \<Gamma> (Post (aa, ba))\<close> essafe_EvtSeq by auto
  qed
qed

theorem rule_EvtSys :  "\<lbrakk> \<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re) ** (Aistar (map \<Gamma> (rellocked re)))} re {Post re};
                         \<forall> re \<in> es. P \<sqsubseteq> Pre re;
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q;
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e\<^sub>s {P} (EvtSys es) {Q}"
  apply (subgoal_tac "\<forall>n s h. get_int_pre (s, h) es Pre \<longrightarrow> essafe n (EvtSys es) s h \<Gamma> Q")
   defer
   apply (simp add: essafe_EvtSys)
  apply (simp add: esCSL_def, clarsimp)
  apply (drule_tac a = "n" and b = "s" and c = "h" in all3_impD)
   apply (simp add: get_int_pre_def implies_def)
  by (simp)

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
    "\<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} resys {Q} \<equiv> \<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> ressafe n resys s h \<Gamma> Q"

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

lemma ressafe_EvtSeq' : "\<lbrakk>resafe n re s h \<Gamma> Q;
        \<forall>m s' h'. m \<le> n \<and> (s', h') \<Turnstile> Q \<longrightarrow> ressafe m (ers, (EvtSys es)) s' h' \<Gamma> R\<rbrakk> 
      \<Longrightarrow>  ressafe n (ers, (EvtSeq re (EvtSys es))) s h \<Gamma> R"
  by (simp add: ressafe_EvtSeq)

theorem rule_rEvtSeq :"\<lbrakk>\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q};
                 \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {Q ** (Aistar (map \<Gamma> (esllocked esys)))} (ers,esys) {R}\<rbrakk> 
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} (ers, (EvtSeq re esys)) {R}"
  apply (auto simp add: reCSL_def resCSL_def intro!: ressafe_EvtSeq)
  done

corollary rule_rEvtSeq' :   "\<lbrakk>\<Gamma> \<turnstile>\<^sub>r\<^sub>e {P} re {Q};  \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {Q} (ers, (EvtSys es)) {R} \<rbrakk> 
                        \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P} (ers, (EvtSeq re (EvtSys es))) {R}"
  using reCSL_def resCSL_def rule_rEvtSeq by simp

lemma essafe_rEvtSys : "\<lbrakk> \<forall> re \<in> es. \<Gamma> \<turnstile>\<^sub>r\<^sub>e {(Pre re) ** (Aistar (map \<Gamma> (rellocked (resources_re ers re))))} (resources_re ers re) {Post re};
                         \<forall> re \<in> es. (Post re) \<sqsubseteq> Q;
                         \<forall> re1 re2. re1 \<in> es \<and> re2 \<in> es \<longrightarrow> Post re1 \<sqsubseteq> Pre re2\<rbrakk>
                        \<Longrightarrow> \<forall>n s h. get_int_pre (s, h) es Pre \<longrightarrow> ressafe n (ers, (EvtSys es)) s h \<Gamma> Q"
  apply (simp add: reCSL_def)
proof(intro allI impI)
  fix n s h
  assume a0: " \<forall>re\<in>es.
          \<forall>n s h.
             (\<exists>h1. (s, h1) \<Turnstile> Pre re \<and>
                   (\<exists>h2. (s, h2) \<Turnstile> Aistar (map \<Gamma> (rellocked (resources_re ers re))) \<and> h = h1 ++ h2 \<and> disjoint (dom h1) (dom h2))) \<longrightarrow>
             resafe n (resources_re ers re) s h \<Gamma> (Post re)"
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
    apply (simp add: resllocked_def, clarify, rule_tac x = "ha ++ hJ" in exI, clarsimp)
  proof-
    fix n ha hJ hF rs e ab
    assume a00: "(\<And>s h. get_int_pre (s, h) es Pre \<Longrightarrow> ressafe n (ers, EvtSys es) s h \<Gamma> Q)"
    and    a01: "get_int_pre (ab, ha) es Pre"
    and    a02: "(ab, hJ) \<Turnstile> Aistar (map \<Gamma> (rellocked (ers @ rs, e)))"
    and    a03: "disjoint (dom ha) (dom hJ)"
    and    a04: "(rs, e) \<in> es"
    then have "(ab, ha) \<Turnstile> Pre (rs,e)"
      by (simp add: get_int_pre_def)
    with a0  have "resafe n (resources_re ers (rs, e)) ab (ha ++ hJ) \<Gamma> (Post (rs, e))"
      using a02 a03 a04 resources_re_def by fastforce
    then have "resafe n (ers @ rs, e) ab (ha ++ hJ) \<Gamma> (Post (rs, e))"
      by (simp add: resources_re_def)
    with a2 have "\<forall>re \<in> es. \<forall>\<sigma>. \<sigma> \<Turnstile> Post re \<longrightarrow> get_int_pre \<sigma> es Pre"
      using get_int_pre_def implies_def by auto
    then have "\<forall>s' h'. (s', h') \<Turnstile> Post (rs, e)  \<longrightarrow>  ressafe n (ers, EvtSys es) s' h' \<Gamma> Q"
      using a00 a04 by blast
    then have "\<forall>m s' h'. m\<le> n \<and> (s', h') \<Turnstile> Post (rs, e) \<longrightarrow> ressafe m (ers, EvtSys es) s' h' \<Gamma> Q"
      using ressafe_mon by blast
    then show "ressafe n (ers, EvtSeq (ers @ rs, e) (EvtSys es)) ab (ha ++ hJ) \<Gamma> Q"
      using \<open>resafe n (ers @ rs, e) ab (ha ++ hJ) \<Gamma> (Post (rs, e))\<close> ressafe_EvtSeq' by auto
  qed
qed

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

definition 
  pesCSL :: "(rname \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> paresys \<Rightarrow> assn \<Rightarrow> bool" 
  ("_ \<turnstile>\<^sub>p\<^sub>e\<^sub>s { _ } _ { _ }")
  where
    "\<Gamma> \<turnstile>\<^sub>p\<^sub>e\<^sub>s {P} pes {Q} \<equiv> \<forall>n s h. (s, h) \<Turnstile> P \<longrightarrow> pessafe n pes s h \<Gamma> Q"

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

lemma disjoint_hplus_list : " disjoint (dom (hplus_list l)) (dom h) \<longleftrightarrow> (\<forall>r \<in> set l.  disjoint (dom r) (dom h))"
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
  | "disjoint_heap_with_list h (x # xs) = (disjoint (dom h) (dom x) \<and> disjoint_heap_with_list h xs)"

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
              Nitpick.case_nat_unfold One_nat_def Suc_pred disjoint_with_hplus disjoint_search(1) less_Suc0 not_less_eq)
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

lemma disjoint_locked_heap_update : "\<lbrakk> \<forall>k'. k' < length l \<and> k' \<noteq> k \<longrightarrow> disjoint (dom x) (dom (l ! k'));
        disjoint_heap_list l ; k < length l; l' = l[k := x] \<rbrakk>
    \<Longrightarrow> disjoint_heap_list l'"
  by (metis disjoint_list_equiv disjoint_search(1) length_list_update nth_list_update_eq nth_list_update_neq)

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
  by (simp add: disjoint_locked_list_equiv disjoint_locked_between_equiv2 disjoint_locked_with_equiv2)

lemma envs_app' : "disjoint (set a) (set b) \<Longrightarrow> disjoint (set a) (set c) \<Longrightarrow> disjoint (set b) (set c)
    \<Longrightarrow> envs \<Gamma> (a @ b @ c) (a @ b' @ c) = envs \<Gamma> b b'"
  by (simp add: envs_app(1) envs_app(2))

lemma disjoint_locked_list_update : "\<lbrakk> \<forall>k'. k' < length l \<and> k' \<noteq> k \<longrightarrow> disjoint (reslocked re) (reslocked (l ! k'));
        disjoint_locked_list l ; k < length l \<rbrakk>
    \<Longrightarrow> disjoint_locked_list (l [k := re])"
  by (smt disjoint_locked_list_equiv disjoint_search(1) length_list_update nth_list_update_eq nth_list_update_neq)

lemma pesllocked_cancel : "\<lbrakk>disjoint_locked_list pes; pes ! k = res; pes' = pes[k := res']; k < length pes\<rbrakk>
        \<Longrightarrow> envs \<Gamma> (pesllocked pes) (pesllocked pes')
          = envs \<Gamma> (resllocked res) (resllocked res')"
  apply (simp add: peslocked_split)
  apply (rule envs_app')
    apply (metis disjoint_locked_with_property disjoint_search(1) disjoint_with_take peslocked_def reslocked_eq)
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
  by (metis disjoint_locked_heap_update1 hplus_list_exchange length_list_update list_update_overwrite nth_list_update_eq)


lemma K1 : "(s, h) \<Turnstile> Aistar Ps \<Longrightarrow> (\<exists>hs. length hs = length Ps  \<and> disjoint_heap_list hs 
                          \<and> (\<forall>k < length Ps. (s, hs ! k) \<Turnstile> Ps ! k ) \<and> hplus_list hs = h)" 
  apply (induct Ps arbitrary: s h, simp, clarsimp)
  apply (drule mall2_impD, simp, clarsimp)
  apply (rule_tac x = "h1 # hs" in exI, simp)
  apply (rule conjI) 
  using disjoint_heap_with_equiv2 disjoint_hplus_list1 disjoint_search(1) apply blast
  using less_Suc_eq_0_disj by auto

theorem rule_pes : "  \<forall>k. k < length pes \<longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s  {Ps ! k} (pes ! k) {Qs ! k} \<Longrightarrow> \<forall>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2 
          \<longrightarrow> disjoint (fvREsv (pes ! k1) \<union> fvA (Qs ! k1) \<union> fvAs \<Gamma>) (wrREsv (pes ! k2))  \<Longrightarrow> disjoint_locked_list pes \<Longrightarrow> length pes = length Ps \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>p\<^sub>e\<^sub>s {Aistar Ps} pes {Aistar Qs}"
  apply (simp add: resCSL_def pesCSL_def, clarify)
  apply (drule K1, clarify)
  apply (rule pessafe, simp_all)
  by blast

corollary "\<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P1} res1 {Q1} \<Longrightarrow> \<Gamma>  \<turnstile>\<^sub>r\<^sub>e\<^sub>s {P2} res2 {Q2} \<Longrightarrow> disjoint ((fvResv res1) \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrREsv res2)
        \<Longrightarrow> disjoint ((fvResv res2) \<union> fvA Q1 \<union> fvAs \<Gamma>) (wrREsv res1) \<Longrightarrow> dis"
  sorry


end

