section \<open>Computation of event systems\<close>
theory Event_Computation
  imports Event_Lang
begin                                                                      

subsection \<open>Operational Semantics for event\<close>

datatype cmd = CMP

datatype act = Cmd cmd
  | EvtEnt event

record actk = Act :: act
                K :: nat

definition get_actk :: "act \<Rightarrow> nat \<Rightarrow> actk" ("_\<sharp>_" [91,91] 90)
  where "get_actk a k \<equiv> \<lparr>Act=a, K=k\<rparr>"

type_synonym x = "nat \<Rightarrow> event"

type_synonym econf = "event \<times> state \<times> x"

definition getspc_e :: " econf \<Rightarrow>  event" where
  "getspc_e conf \<equiv> fst conf"

definition gets_e :: " econf \<Rightarrow> state" where
  "gets_e conf \<equiv> fst (snd conf)"

definition getx_e :: "econf \<Rightarrow>  x" where
  "getx_e conf \<equiv> snd (snd conf)"

type_synonym esconf = "esys \<times> state \<times> x"

definition getspc_es :: " esconf \<Rightarrow>  esys" where
  "getspc_es conf \<equiv> fst conf"

definition gets_es :: "esconf \<Rightarrow> state" where
  "gets_es conf \<equiv> fst (snd conf)"

definition getx_es :: "esconf \<Rightarrow> x" where
  "getx_es conf \<equiv> snd (snd conf)"

type_synonym pesconf = "paresys \<times> state \<times> x"

definition getspc_pes :: "pesconf \<Rightarrow> paresys" where
  "getspc_pes conf \<equiv> fst conf"

definition gets_pes :: "pesconf \<Rightarrow> state" where
  "gets_pes conf \<equiv> fst (snd conf)"

definition getx_pes :: " pesconf \<Rightarrow>  x" where
  "getx_pes conf \<equiv> snd (snd conf)"

type_synonym rpesconf = "rparesys \<times> state \<times> x"

definition getspc :: "rpesconf \<Rightarrow> rparesys" where
  "getspc conf \<equiv> fst conf"

definition gets :: "rpesconf \<Rightarrow> state" where
  "gets conf \<equiv> fst (snd conf)"

definition getx :: "rpesconf \<Rightarrow>  x" where
  "getx conf \<equiv> snd (snd conf)"

definition getact :: " actk \<Rightarrow>  act" where
  "getact a \<equiv> Act a"

definition getk :: " actk \<Rightarrow> nat" where
  "getk a \<equiv> K a"

subsubsection \<open>Operational Semantics for event and resource event \<close>
inductive
  ered :: "econf \<Rightarrow> actk \<Rightarrow> econf \<Rightarrow> bool" ("_ -et-_\<rightarrow> _" [81,81,81] 80)
  where               
  red_AnonyEvt: "red C \<sigma> C' \<sigma>' \<Longrightarrow> (AnonyEvent C, \<sigma>, x) -et-(Cmd CMP)\<sharp>k\<rightarrow> (AnonyEvent C', \<sigma>', x)"
| red_BasicEvt: "\<lbrakk>bdenot guard (fst \<sigma>); x' = x(k:= BasicEvent (guard, C))\<rbrakk> \<Longrightarrow> 
                 (BasicEvent (guard, C), \<sigma>, x)-et-(EvtEnt (BasicEvent (guard, C)))\<sharp>k\<rightarrow> (AnonyEvent C, \<sigma>, x')"

subsubsection \<open>Operational Semantics for event systems and resource event systems\<close>
inductive
  esred :: "esconf \<Rightarrow> actk \<Rightarrow> esconf \<Rightarrow> bool" ("_ -es-_\<rightarrow> _" [81,81,81] 80)
  where
  red_EvtSeq1: "(e, \<sigma>, x)-et-actk\<rightarrow> (e', \<sigma>', x) \<Longrightarrow> e' \<noteq> (AnonyEvent Cskip) 
                \<Longrightarrow> ((EvtSeq e es), \<sigma>, x) -es-actk\<rightarrow> ((EvtSeq e' es), \<sigma>', x)"
| red_EvtSeq2: "\<lbrakk>(e, \<sigma>, x)-et-actk\<rightarrow>(e', \<sigma>', x); e' = (AnonyEvent Cskip)\<rbrakk> \<Longrightarrow>
                ((EvtSeq e es), \<sigma>, x) -es-atck\<rightarrow> (es, \<sigma>', x)"
| red_EvtSet: " \<lbrakk>e \<in> evts; (e, \<sigma>, x)-et-(EvtEnt evt)\<sharp>k\<rightarrow>(e', \<sigma>', x')\<rbrakk>  
              \<Longrightarrow> ((EvtSys evts), \<sigma>, x) -es-(EvtEnt evt)\<sharp>k\<rightarrow> ((EvtSeq e' (EvtSys evts)), \<sigma>', x')"

subsubsection \<open>Operational Semantics for parallel event systems and resource parallel event systems\<close>

subsection \<open>functions for event\<close>

subsubsection \<open>locks that a event is currently holding \<close>

primrec 
  elocked :: "event \<Rightarrow> rname set"
  where
  "elocked (AnonyEvent C) = locked C"
| "elocked (BasicEvent C) = {}"

primrec
  ellocked :: "event \<Rightarrow> rname list"
  where
  "ellocked (AnonyEvent C) = llocked C"
| "ellocked (BasicEvent _) = []"

lemma elocked_eq: "elocked e = set (ellocked e)"
  by (induct e, simp_all add: locked_eq)

subsubsection \<open>memory accesses and memory writes a event performs in one step \<close>

primrec
  eaccesses :: "event \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "eaccesses (AnonyEvent C) s = accesses C s"
| "eaccesses (BasicEvent _) s = {}"

primrec
  ewrite :: "event \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "ewrite (AnonyEvent C) s = accesses C s"
| "ewrite (BasicEvent _) s = {}"

subsubsection \<open>A event aborts in a given state\<close>

inductive
  eaborts :: "event \<Rightarrow> state \<Rightarrow> bool"
  where
  aborts_Evt: "aborts C \<sigma> \<Longrightarrow> eaborts (AnonyEvent C) \<sigma>"

subsubsection \<open>free variable of event\<close>

fun
  fvEv :: "event \<Rightarrow> var set"
  where
  "fvEv (AnonyEvent C) = fvC C"
| "fvEv (BasicEvent (guard, C)) = (fvB guard) \<union> (fvC C)"

subsubsection \<open>all variables may be updated by a event\<close>

fun
  wrEv :: "event \<Rightarrow> var set"
  where
  "wrEv (AnonyEvent C) = wrC C"
| "wrEv (BasicEvent (guard, C)) = wrC C"

subsubsection \<open>Basic properties about event semantics\<close>

lemma ewrites_accesses : "ewrite e s \<subseteq> eaccesses e s"
  by (induct e arbitrary: s, auto)

lemma ered_properties:
  "(e, \<sigma>, x) -et-actk\<rightarrow> (e', \<sigma>', x') \<Longrightarrow> fvEv e' \<subseteq> fvEv e \<and> wrEv e' \<subseteq> wrEv e \<and> agrees (- wrEv e) (fst \<sigma>') (fst \<sigma>)"
  apply (erule ered.cases, simp_all)
   apply (simp add: red_properties)
  by (simp add: agrees_refl)

lemma eaccesses_agrees:
  "agrees (fvEv e) s s' \<Longrightarrow> eaccesses e s = eaccesses e s'"
  apply (induct e arbitrary: s s', simp_all)
  by (simp add: accesses_agrees)

lemma ewrites_agrees:
  "agrees (fvEv e) s s' \<Longrightarrow> ewrite e s = ewrite e s'"
  apply (induct e arbitrary: s s', simp_all)
  by (simp add: accesses_agrees)

lemma ered_agrees[rule_format]:
  "(e, \<sigma>, x) -et-actk\<rightarrow> (e', \<sigma>', x') \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvEv e \<subseteq> X \<longrightarrow>
    (\<exists>s' h'. (e, (s, h), x) -et-actk\<rightarrow> (e', (s', h'), x') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  apply (induct e, simp_all)
   apply (erule ered.cases, simp_all, clarify)
   apply (meson ered.red_AnonyEvt red_agrees)
  apply (erule ered.cases, simp_all, clarify)
  apply (rule_tac x = "s" in exI, simp_all)
  apply (subgoal_tac "agrees (fvB guard) (fst \<sigma>) s")
   apply (simp add: bexp_agrees ered.red_BasicEvt)
  by auto

lemma eaborts_agrees[rule_format]:
  "eaborts e \<sigma> \<Longrightarrow> \<forall>s'. agrees (fvEv e) (fst \<sigma>) s' \<longrightarrow> snd \<sigma> = h' \<longrightarrow> eaborts e (s', h')"
  apply (induct e)
   apply (erule eaborts.induct, simp)
   apply (simp add: aborts_Evt aborts_agrees)
   apply (erule eaborts.induct, simp)
  apply (simp add: aborts_Evt aborts_agrees)
  done

subsection \<open>functions for event system \<close>

subsubsection \<open>locks that a  event system is currently holding \<close>

primrec
  eslocked :: "esys \<Rightarrow> rname set"
  where
  "eslocked (EvtSeq e esys) = elocked e"
| "eslocked (EvtSys _) = {}"

primrec
  esllocked :: "esys \<Rightarrow> rname list"
  where
  "esllocked (EvtSeq e esys) = ellocked e"
| "esllocked (EvtSys S) = []"


lemma eslocked_eq: "eslocked es = set (esllocked es)"
  by (metis elocked_eq empty_set esllocked.simps(1) esllocked.simps(2) eslocked.simps(1) eslocked.simps(2) esys.exhaust)

subsubsection \<open>memory accesses and memory writes a event system performs in one step \<close>

primrec
  esaccesses :: "esys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "esaccesses (EvtSeq e esys) s = eaccesses e s"
| "esaccesses (EvtSys S) s = {}"

primrec
  eswrite :: "esys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "eswrite (EvtSeq e esys) s = ewrite e s"
| "eswrite (EvtSys S) s = {}"

subsubsection \<open>A event system aborts in a given state\<close>

inductive 
  esaborts :: "esys \<Rightarrow> state \<Rightarrow> bool"
  where
  aborts_EvtSeq: "eaborts e \<sigma> \<Longrightarrow> esaborts (EvtSeq e esys) \<sigma>"
| aborts_EvtSys: "e \<in> es  \<Longrightarrow> eaborts e \<sigma> \<Longrightarrow>  esaborts (EvtSys es) \<sigma>"

subsubsection \<open>free variable of event system\<close>

primrec
  fvEsv :: "esys \<Rightarrow> var set"
  where
  "fvEsv (EvtSeq e esys) = (fvEv e) \<union> (fvEsv) esys"
| "fvEsv (EvtSys es) = {x. \<exists>e \<in> es.  x \<in> (fvEv e)}"

subsubsection \<open>all variables may be updated by a event system\<close>

primrec
  wrEsv :: "esys \<Rightarrow> var set"
  where
  "wrEsv (EvtSeq e esys) = (wrEv e) \<union> (wrEsv esys)"
| "wrEsv (EvtSys es) = {x. \<exists>e \<in> es. x \<in> (wrEv e)}"
                   
subsubsection \<open>Basic properties about event system semantics\<close>

lemma fvEsv_property : "e \<in> es \<Longrightarrow> fvEsv (EvtSeq e (EvtSys es)) = fvEsv (EvtSys es)"
  by auto

lemma wrEsv_property : "e \<in> es \<Longrightarrow> wrEsv (EvtSeq e (EvtSys es)) = wrEsv (EvtSys es)"
  by auto

lemma eswrites_accesses : "eswrite es s \<subseteq> esaccesses es s"
  by (induct es arbitrary: s, simp_all add : ewrites_accesses)

lemma esred_properties :
"(esys, \<sigma>, x) -es-actk\<rightarrow> (esys', \<sigma>', x') \<Longrightarrow> fvEsv esys' \<subseteq> fvEsv esys 
                         \<and> wrEsv esys' \<subseteq> wrEsv esys \<and> agrees (- wrEsv esys) (fst \<sigma>) (fst \<sigma>')"
  apply (erule esred.cases, simp_all)
    apply (simp add: le_supI1 ered_properties agrees_def)
    apply (metis (mono_tags, lifting) IntD1 agrees_def ered_properties)
  apply (meson Int_lower1 agreesC agrees_search(2) ered_properties)
  apply (rule conjI, clarsimp)
   apply (meson contra_subsetD ered_properties)
  apply (rule conjI, clarsimp)
  using ered_properties apply blast
  using ered_properties by fastforce

lemma esaccesses_agrees: 
"agrees (fvEsv esys) s s' \<Longrightarrow> esaccesses esys s = esaccesses esys s'"
  apply (induct esys arbitrary: s s', simp_all add: exp_agrees, clarsimp)
  by (simp add: eaccesses_agrees)

lemma eswrites_agrees: 
"agrees (fvEsv esys) s s' \<Longrightarrow> eswrite esys s = eswrite esys s'"
  apply (induct esys arbitrary: s s', simp_all add: exp_agrees, clarsimp)
  by (simp add: ewrites_agrees)

lemma esred_agrees[rule_format] : 
"(esys, \<sigma>, x) -es-actk\<rightarrow> (esys', \<sigma>', x') \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvEsv esys \<subseteq> X \<longrightarrow>
   (\<exists>s' h'. (esys, (s, h), x) -es-actk\<rightarrow> (esys', (s', h'), x') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  apply (erule esred.cases, simp_all, clarsimp)
    apply (drule_tac X = "X" and s = "s" in ered_agrees, simp_all)
    apply (clarsimp, rule_tac x = "s'" in exI, simp add: esred.red_EvtSeq1)
  apply (meson esred.red_EvtSeq2 ered_agrees snd_conv)
  apply (clarsimp, drule ered_agrees, simp_all)
   apply blast
  using esred.red_EvtSet by blast

lemma esaborts_agrees[rule_format] :
"esaborts esys \<sigma> \<Longrightarrow> \<forall>s'. agrees (fvEsv esys) (fst \<sigma>) s' \<longrightarrow> snd \<sigma> = h' \<longrightarrow> esaborts esys (s', h')"
  apply (erule esaborts.induct, simp_all)
   apply (auto simp add: ewrites_agrees eaccesses_agrees exp_agrees, auto simp add: agrees_def)
   apply (simp add: aborts_EvtSeq agrees_def eaborts_agrees)
  by (metis (mono_tags, lifting) agrees_def eaborts_agrees esaborts.simps prod.sel(1) prod.sel(2))

subsection \<open>functions for parallel event system \<close>

subsubsection \<open>locks that a parallel system is currently holding \<close>

definition
  pesllocked :: "paresys \<Rightarrow> rname list"
  where
  "pesllocked pes = List.maps esllocked pes"

definition
  peslocked :: "paresys \<Rightarrow> rname set"
  where
  "peslocked pes = set (pesllocked pes)"

lemma empty_peslock : "peslocked [] = {}"
  by (simp add: maps_simps(2) pesllocked_def peslocked_def)

lemma pesllocked_induct : "pesllocked (es # pes) = esllocked es @ pesllocked pes"
  by (simp add: maps_simps(1) pesllocked_def)

lemma peslock_notin : "r \<notin> peslocked pes \<Longrightarrow> \<forall>k < length pes. r \<notin> eslocked (pes ! k)"
  apply (simp add: peslocked_def pesllocked_def eslocked_eq)
  apply (induct pes, simp, clarsimp)
  apply (case_tac k, simp add: maps_simps(1))
  by (simp add: maps_simps(1))

lemma induct_peslock : "peslocked (x # xs) = (eslocked x) \<union> peslocked (xs)"
  by (simp add: maps_simps(1) pesllocked_def peslocked_def eslocked_eq)

lemma peslocked_eq : "set (pesllocked pes) = peslocked pes"
  by (simp add: peslocked_def)

lemma maps_append : "List.maps f (l1 @ l2) = List.maps f l1 @ List.maps f l2"
  apply (induct l1, simp add: maps_simps)
  by (simp add: List.append.append_Cons maps_simps)

lemma peslocked_split : "k < length pes \<Longrightarrow> pesllocked pes = 
       pesllocked (take k pes) @ esllocked (pes ! k) @ pesllocked (drop (Suc k) pes)"
proof-
  assume a0: "k < length pes"
  then have " pes = take k pes @ (pes ! k) # drop (Suc k) pes"
    by (simp add: id_take_nth_drop)
  then have "pesllocked pes = pesllocked (take k pes @ (pes ! k) # drop (Suc k) pes)"
    by simp
  then have "pesllocked pes = List.maps esllocked (take k pes @ (pes ! k) # drop (Suc k) pes)"
    by (simp add: pesllocked_def)
  then have "pesllocked pes = List.maps esllocked (take k pes) 
           @ esllocked (pes ! k) @ List.maps esllocked (drop (Suc k) pes)"
    by (simp add: maps_append maps_simps(1))
  then show ?thesis
    by (simp add: pesllocked_def)
qed

inductive
  pesred :: "pesconf \<Rightarrow> actk \<Rightarrow> pesconf \<Rightarrow> bool" ("_ -pes-_\<rightarrow> _" [81,81,81] 80)
  where
  red_Par : "\<lbrakk>k < length pes;  pes ! k = es ; (es, \<sigma>, x) -es-(a\<sharp>k)\<rightarrow> (es', \<sigma>', x');
             \<forall>k'. k' < length pes \<and> k \<noteq> k' \<longrightarrow> disjoint (eslocked es') (eslocked (pes ! k'))\<rbrakk> 
             \<Longrightarrow> (pes, \<sigma>, x) -pes-a\<sharp>k\<rightarrow> ((pes[k := es']), \<sigma>', x')"

subsubsection \<open>A parallel system aborts in a given state\<close>

inductive
  pesaborts :: "paresys \<Rightarrow> state \<Rightarrow> bool"
  where
  aborts_Par : " \<exists>k. k < length pes \<and> esaborts (pes ! k) \<sigma> \<Longrightarrow> pesaborts pes \<sigma>"
| aborts_Race : "\<exists>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2  \<and> \<not> disjoint (esaccesses (pes ! k1) (fst \<sigma>)) 
                 (eswrite (pes ! k2) (fst \<sigma>)) \<Longrightarrow> pesaborts pes \<sigma>"

subsubsection \<open>memory accesses and memory writes a parallel event system performs in one step \<close>

primrec
  pesaccesses :: "paresys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "pesaccesses [] s = {}"
| "pesaccesses (es # pes) s = (esaccesses es s) \<union> (pesaccesses pes s)"

primrec
  peswrite :: "paresys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "peswrite [] s = {}"
| "peswrite (es # pes) s = (eswrite es s) \<union> (peswrite pes s)"

subsubsection \<open>free variable of parallel event system\<close>

fun
  fvPEsv :: "paresys \<Rightarrow> var set"
  where
  "fvPEsv [] = {}"
| "fvPEsv (es # pes) = (fvEsv es) \<union> (fvPEsv pes)"

subsubsection \<open>all variables may be updated by a parallel event system\<close>

fun 
  wrPEsv :: "paresys \<Rightarrow> var set"
  where 
  "wrPEsv [] = {}"
| "wrPEsv (es # pes) = (wrEsv es) \<union> (wrPEsv pes)"

lemma peswrites_accesses : "peswrite pes s \<subseteq> pesaccesses pes s"
  apply (induct pes, simp, simp)
  apply (rule conjI, simp add: le_supI1 eswrites_accesses)
  by (simp add: le_supI2)

lemma K1 : "fvPEsv pes \<subseteq> A \<longleftrightarrow> (\<forall>es \<in> set pes. fvEsv es \<subseteq> A)"
  by (induct pes, simp, simp)

lemma K2 : "wrPEsv pes \<subseteq> A \<longleftrightarrow> (\<forall>es \<in> set pes. wrEsv es \<subseteq> A)"
  by (induct pes, simp, simp)

lemma fvPEsv_equiv : "fvPEsv pes = {x. \<exists>es \<in> set pes. x \<in> fvEsv es}"
  by (induct pes, simp, simp add: Collect_disj_eq)

lemma wrPEsv_equiv : "wrPEsv pes = {x. \<exists>es \<in> set pes. x \<in> wrEsv es}"
  by (induct pes, simp, simp add: Collect_disj_eq)

lemma pesred_properties:
  "(pes, \<sigma>, x) -pes-actk\<rightarrow> (pes', \<sigma>', x') \<Longrightarrow> fvPEsv pes' \<subseteq> fvPEsv pes \<and> wrPEsv pes' \<subseteq> wrPEsv pes 
          \<and> agrees (- wrPEsv pes) (fst \<sigma>') (fst \<sigma>)"
  apply (erule pesred.cases, simp_all)
  apply (simp add: le_supI1 esred_properties agrees_def fvPEsv_equiv wrPEsv_equiv)
  apply (rule conjI, clarsimp)
   apply (metis (no_types, lifting) insertE nth_mem 
          esred_properties set_update_subset_insert subset_iff)
  apply (rule conjI, clarsimp)
   apply (metis (no_types, lifting) insertE nth_mem esred_properties set_update_subset_insert  subset_iff, clarsimp)
  by (metis (mono_tags, lifting) ComplI agrees_def  list_update_id esred_properties set_update_memI)

lemma pesaccesses_agrees:
  "agrees (fvPEsv pes) s s' \<Longrightarrow> pesaccesses pes s = pesaccesses pes s'"
  apply (induct pes arbitrary: s s', simp_all)
  using esaccesses_agrees by blast

lemma peswrites_agrees:
  "agrees (fvPEsv pes) s s' \<Longrightarrow> peswrite pes s = peswrite pes s'"
  apply (induct pes arbitrary: s s', simp_all)
  using eswrites_agrees by blast

subsection \<open>functions for resource parallel event system \<close>

subsubsection \<open>locks that resource parallel system is currently holding \<close>

definition
  rpesllocked :: "rparesys \<Rightarrow> rname list"                
  where
  "rpesllocked rpes = list_minus (pesllocked (snd rpes)) (fst rpes)"

definition
  rpeslocked :: "rparesys \<Rightarrow> rname set"
  where
  "rpeslocked rpes = (peslocked (snd rpes))- set (fst rpes)"

lemma empty_rpeslock : "rpeslocked (rs,[]) = {}"
  by (simp add: empty_peslock rpeslocked_def)

lemma rpeslocked_eq : "set (rpesllocked rpes) = rpeslocked rpes"
  by (simp add: peslocked_def rpesllocked_def rpeslocked_def)

inductive
  rpesred :: "rpesconf \<Rightarrow> actk \<Rightarrow> rpesconf \<Rightarrow> bool" ("_ -rpes-_\<rightarrow> _" [81,81,81] 80)
  where
  red_Par: "\<lbrakk>k < length pes;  pes ! k = res ; (res, \<sigma>, x) -es-(a\<sharp>k)\<rightarrow> (res', \<sigma>', x');
             \<forall>k'. k' < length pes \<and> k \<noteq> k' \<longrightarrow> disjoint (eslocked res') (eslocked (pes ! k'))\<rbrakk> 
          \<Longrightarrow> ((r, pes), \<sigma>, x) -rpes-a\<sharp>k\<rightarrow> ((r, pes[k := res']), \<sigma>', x')"

lemma rpes_invres : "(rpes, \<sigma>, x)-rpes-actk\<rightarrow> (rpes', \<sigma>', x') \<Longrightarrow> fst rpes = fst rpes'"
  by (erule rpesred.cases, simp_all)

lemma rpes_equiv1 : "(pes, \<sigma>, x) -pes-actk\<rightarrow> (pes', \<sigma>', x') \<Longrightarrow> ((r, pes), \<sigma>, x)-rpes-actk\<rightarrow> ((r, pes'), \<sigma>', x')"
  by (erule pesred.cases, simp add: rpesred.red_Par)

lemma rpes_equiv2 : "((r, pes), \<sigma>, x)-rpes-actk\<rightarrow> ((r, pes'), \<sigma>', x') \<Longrightarrow> (pes, \<sigma>, x) -pes-actk\<rightarrow> (pes', \<sigma>', x')"
  by (erule rpesred.cases, simp add: pesred.red_Par)

lemma rpes_equiv3 : "((r, pes), \<sigma>, x)-rpes-actk\<rightarrow> ((r, pes'), \<sigma>', x') \<Longrightarrow> ((r', pes), \<sigma>, x)-rpes-actk\<rightarrow> ((r', pes'), \<sigma>', x')"
  by (simp add: rpes_equiv1 rpes_equiv2)

subsubsection \<open>A resource parallel system aborts in a given state\<close>

inductive
  rpesaborts :: "rparesys \<Rightarrow> state \<Rightarrow> bool"
  where
  aborts_Par : " \<exists>k. k < length pes \<and> esaborts  (pes ! k) \<sigma> 
                 \<Longrightarrow> rpesaborts (r, pes) \<sigma>"
| aborts_Race : "\<exists>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2  \<and> 
                  \<not> disjoint (esaccesses (pes ! k1) (fst \<sigma>)) 
                         (eswrite (pes ! k2) (fst \<sigma>)) \<Longrightarrow> rpesaborts (r, pes) \<sigma>"

lemma rpesaborts_equiv : "rpesaborts (r, pes) \<sigma> = pesaborts pes \<sigma>"
proof
  assume "rpesaborts (r, pes) \<sigma>"
  then show "pesaborts pes \<sigma>"
    apply (rule rpesaborts.cases, simp_all)
    apply (simp add: pesaborts.aborts_Par)
    by (simp add: pesaborts.aborts_Race esaccesses_def eswrite_def)
next
  assume "pesaborts pes \<sigma>"
  then show "rpesaborts (r, pes) \<sigma>"
    apply (rule pesaborts.cases, simp_all)
     apply (simp add: rpesaborts.aborts_Par)
    by (simp add: rpesaborts.aborts_Race)
qed

subsubsection \<open>memory accesses and memory writes a parallel resource 
                event system performs in one step \<close>

definition
  rpesaccesses :: "rparesys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "rpesaccesses rpes = pesaccesses (snd rpes)"

definition
  rpeswrite :: "rparesys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "rpeswrite rpes s = peswrite (snd rpes) s"

subsubsection \<open>free variable of parallel event system\<close>

fun
  fvRPEsv :: "rparesys \<Rightarrow> var set"
  where
  "fvRPEsv rpes = fvPEsv (snd rpes)"

subsubsection \<open>all variables may be updated by a parallel event system\<close>

fun 
  wrRPEsv :: "rparesys \<Rightarrow> var set"
  where 
  "wrRPEsv rpes = wrPEsv (snd rpes)"

lemma rpeswrites_accesses : "rpeswrite rpes s \<subseteq> rpesaccesses rpes s"
  by (simp add: rpeswrite_def rpesaccesses_def peswrites_accesses)

lemma rpesred_properties:
  "(rpes, \<sigma>, x) -rpes-actk\<rightarrow> (rpes', \<sigma>', x') \<Longrightarrow> fvRPEsv rpes' \<subseteq> fvRPEsv rpes \<and> wrRPEsv rpes' \<subseteq> wrRPEsv rpes 
          \<and> agrees (- wrRPEsv rpes) (fst \<sigma>') (fst \<sigma>)"
  by (metis (no_types, lifting) fvRPEsv.elims pesred_properties prod.collapse rpes_equiv2 rpes_invres wrRPEsv.elims)

lemma rpesaccesses_agrees:
  "agrees (fvRPEsv rpes) s s' \<Longrightarrow> rpesaccesses rpes s = rpesaccesses rpes s'"
  by (simp add: pesaccesses_agrees rpesaccesses_def)

lemma rpeswrites_agrees:
  "agrees (fvRPEsv rpes) s s' \<Longrightarrow> rpeswrite rpes s = rpeswrite rpes s'"
  by (simp add: peswrites_agrees rpeswrite_def)

end

