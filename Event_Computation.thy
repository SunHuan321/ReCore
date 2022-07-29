section \<open>Computation of event systems\<close>
theory Event_Computation
  imports Event_Lang
begin

subsection \<open>Operational Semantics for event\<close>

subsubsection \<open>Operational Semantics for event and resource event \<close>
inductive
  ered :: "event \<Rightarrow> state \<Rightarrow> event \<Rightarrow> state \<Rightarrow> bool"
  where
  red_AnonyEvt: "red C \<sigma> C' \<sigma>' \<Longrightarrow> ered (AnonyEvent C) \<sigma> (AnonyEvent C') \<sigma>'"
| red_BasicEvt: "bdenot guard (fst \<sigma>) \<Longrightarrow> ered (BasicEvent (guard, C)) \<sigma> (AnonyEvent C) \<sigma>"

inductive 
  rered :: "revent \<Rightarrow> state \<Rightarrow> revent \<Rightarrow> state \<Rightarrow> bool"
  where     
  red_AnonyEvt: "red C \<sigma> C' \<sigma>' \<Longrightarrow> rered (rs,(AnonyEvent C)) \<sigma> (rs, (AnonyEvent C')) \<sigma>'"
| red_BasicEvt: "bdenot guard (fst \<sigma>) 
                 \<Longrightarrow> rered (rs ,(BasicEvent (guard, C))) \<sigma> (rs ,(AnonyEvent (Cresources rs C))) \<sigma>"

subsubsection \<open>Operational Semantics for event systems and resource event systems\<close>
inductive
  esred :: "esys \<Rightarrow> state \<Rightarrow> esys \<Rightarrow> state \<Rightarrow> bool"
  where
  red_EvtSeq1: "rered re \<sigma> re' \<sigma>' \<Longrightarrow> snd re' \<noteq> (AnonyEvent Cskip) 
                \<Longrightarrow> esred (EvtSeq re res) \<sigma> (EvtSeq re' res) \<sigma>'"
| red_EvtSeq2: "snd re = (AnonyEvent Cskip) \<Longrightarrow> esred (EvtSeq re res) \<sigma> res \<sigma>"
| red_EvtSet: " re \<in> revts  \<Longrightarrow> esred (EvtSys revts) \<sigma> (EvtSeq re (EvtSys revts)) \<sigma>"

inductive
  resred :: "resys \<Rightarrow> state \<Rightarrow> resys \<Rightarrow> state \<Rightarrow> bool"
  where
  red_EvtSeq1: "rered re \<sigma> re' \<sigma>' \<Longrightarrow> snd re' \<noteq> (AnonyEvent Cskip) 
           \<Longrightarrow> resred (ers, (EvtSeq re res)) \<sigma> (ers, (EvtSeq re' res)) \<sigma>'"
| red_EvtSeq2: "snd re = (AnonyEvent Cskip) \<Longrightarrow> resred (ers, (EvtSeq re res)) \<sigma> (ers,  res) \<sigma>"
| red_EvtSet: "(rs, e) \<in> revts \<Longrightarrow> resred (ers ,(EvtSys revts)) \<sigma> 
                                   (ers, (EvtSeq ((ers @ rs), e) (EvtSys revts))) \<sigma>"

subsubsection \<open>Operational Semantics for parallel event systems and resource parallel event systems\<close>

(*
inductive
  pesred :: "paresys \<Rightarrow> state \<Rightarrow> paresys \<Rightarrow> state \<Rightarrow> bool"
  where
  red_Par : "k < length pes \<Longrightarrow>  pes ! k = res \<Longrightarrow> resred res \<sigma> res' \<sigma>' \<Longrightarrow> pesred pes \<sigma> (pes[k := res']) \<sigma>'"
*)

inductive
  rpesred :: "rparesys \<Rightarrow> state \<Rightarrow> rparesys \<Rightarrow> state \<Rightarrow> bool"
  where
  red_Par: "pes ! k = (ers, es) \<Longrightarrow> resred (pres @ ers, es) \<sigma> (pres @ ers, es') \<sigma>' \<Longrightarrow> rpesred (pres, pes)  \<sigma> (pres, pes[k := (ers, es')]) \<sigma>'"

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
  " ered e \<sigma> e' \<sigma>' \<Longrightarrow> fvEv e' \<subseteq> fvEv e \<and> wrEv e' \<subseteq> wrEv e \<and> agrees (- wrEv e) (fst \<sigma>') (fst \<sigma>)"
  apply (erule ered.induct, simp_all)
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
  "ered e \<sigma> e' \<sigma>' \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvEv e \<subseteq> X \<longrightarrow>
    (\<exists>s' h'. ered e (s, h) e' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  apply (induct e, simp_all)
   apply (erule ered.cases, simp_all, clarify)
   apply (meson ered.red_AnonyEvt red_agrees)
  apply (erule ered.cases, simp_all, clarify)
  apply (rule_tac x = "s" in exI, simp_all)
  apply (subgoal_tac "agrees (fvB guard) aa s")
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

subsection \<open>functions for resource event  \<close>

subsubsection \<open>locks that a resource event is currently holding \<close>
definition
  relocked :: "revent \<Rightarrow> rname set"
  where
  "relocked re = elocked (snd re)"

definition 
  rellocked :: "revent \<Rightarrow> rname list"
  where
  "rellocked re = ellocked (snd re)"

lemma relocked_eq: "relocked re = set (rellocked re)"
  by (simp add: elocked_eq rellocked_def relocked_def)

subsubsection \<open>memory accesses and memory writes a resource event performs in one step \<close>

definition
  reaccesses :: "revent \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "reaccesses re s = eaccesses (snd re) s"

definition 
  rewrite :: "revent \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "rewrite re s = ewrite (snd re) s"

subsubsection \<open>A resource event aborts in a given state\<close>

definition 
  reaborts :: "revent \<Rightarrow> state \<Rightarrow> bool"
  where
  "reaborts re \<sigma> = eaborts (snd re) \<sigma>"

subsubsection \<open>free variable of resource event\<close>

definition
  fvREv :: "revent \<Rightarrow> var set"
  where
  "fvREv re = fvEv (snd re)"

subsubsection \<open>all variables may be updated by a event\<close>

definition
  wrREv :: "revent \<Rightarrow> var set"
  where
  "wrREv re = wrEv (snd re)"

subsubsection \<open>Basic properties about resource event semantics\<close>

lemma rewrites_accesses : "rewrite re s \<subseteq> reaccesses re s"
  by (simp add: rewrite_def reaccesses_def ewrites_accesses)

lemma rered_properties:
  " rered re \<sigma> re' \<sigma>' \<Longrightarrow> fvREv re' \<subseteq> fvREv re \<and> wrREv re' \<subseteq> wrREv re \<and> agrees (- wrREv re) (fst \<sigma>') (fst \<sigma>)"
  apply (erule rered.induct, simp_all add: fvREv_def wrREv_def)
   apply (simp add: red_properties)
  by (simp add: agrees_refl)

lemma reaccesses_agrees:
  "agrees (fvREv re) s s' \<Longrightarrow> reaccesses re s = reaccesses re s'"
  apply (induct re arbitrary: s s', simp_all add: fvREv_def reaccesses_def)
  by (simp add: eaccesses_agrees)

lemma rewrites_agrees:
  "agrees (fvREv re) s s' \<Longrightarrow> rewrite re s = rewrite re s'"
  apply (induct re arbitrary: s s', simp_all add: fvREv_def rewrite_def)
  by (simp add: ewrites_agrees)

lemma rered_agrees[rule_format]:
  "rered re \<sigma> re' \<sigma>' \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvREv re \<subseteq> X \<longrightarrow>
    (\<exists>s' h'. rered re (s, h) re' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
    apply (induct re, simp_all)
  apply (erule rered.cases, simp_all, clarsimp)
   apply (metis fst_conv fvEv.simps(1) fvREv_def red_agrees rered.red_AnonyEvt snd_conv)
  apply (clarsimp, rule_tac x = "s" in exI, simp)
  apply (subgoal_tac "agrees (fvB guard) aa s")
   apply (simp add: bexp_agrees rered.red_BasicEvt)
  using fvREv_def by auto

lemma reaborts_agrees[rule_format]:
  "reaborts re \<sigma> \<Longrightarrow> \<forall>s'. agrees (fvREv re) (fst \<sigma>) s' \<longrightarrow> snd \<sigma> = h' \<longrightarrow> reaborts re (s', h')"
  apply (induct re, simp add: fvREv_def reaborts_def)
  by (simp add: eaborts_agrees)

subsection \<open>functions for event system \<close>

subsubsection \<open>locks that a  event system is currently holding \<close>
primrec
  eslocked :: "esys \<Rightarrow> rname set"
  where
  "eslocked (EvtSeq re esys) = relocked re"
| "eslocked (EvtSys _) = {}"

primrec
  esllocked :: "esys \<Rightarrow> rname list"
  where
  "esllocked (EvtSeq re esys) = rellocked re"
| "esllocked (EvtSys S) = []"

lemma eslocked_eq: "eslocked es = set (esllocked es)"
  by (induct es, simp_all add: elocked_eq rellocked_def relocked_def)

subsubsection \<open>memory accesses and memory writes a event system performs in one step \<close>

primrec
  esaccesses :: "esys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "esaccesses (EvtSeq re esys) s = reaccesses re s"
| "esaccesses (EvtSys S) s = {}"

primrec
  eswrite :: "esys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "eswrite (EvtSeq re esys) s = rewrite re s"
| "eswrite (EvtSys S) s = {}"

subsubsection \<open>A event system aborts in a given state\<close>

inductive 
  esaborts :: "esys \<Rightarrow> state \<Rightarrow> bool"
  where
  aborts_Esys: "reaborts re \<sigma> \<Longrightarrow> esaborts (EvtSeq re esys) \<sigma>"

subsubsection \<open>free variable of event system\<close>

primrec
  fvEsv :: "esys \<Rightarrow> var set"
  where
  "fvEsv (EvtSeq re esys) = (fvREv re) \<union> (fvEsv) esys"
| "fvEsv (EvtSys es) = {x. \<exists>re \<in> es.  x \<in> (fvREv re)}"

subsubsection \<open>all variables may be updated by a event system\<close>

primrec
  wrEsv :: "esys \<Rightarrow> var set"
  where
  "wrEsv (EvtSeq re esys) = (wrREv re) \<union> (wrEsv esys)"
| "wrEsv (EvtSys es) = {x. \<exists>re \<in> es. x \<in> (wrREv re)}"
                   
subsubsection \<open>Basic properties about event system semantics\<close>

lemma fvEsv_property : "re \<in> es \<Longrightarrow> fvEsv (EvtSeq re (EvtSys es)) = fvEsv (EvtSys es)"
  by auto

lemma wrEsv_property : "re \<in> es \<Longrightarrow> wrEsv (EvtSeq re (EvtSys es)) = wrEsv (EvtSys es)"
  by auto

lemma eswrites_accesses : "eswrite es s \<subseteq> esaccesses es s"
  by (induct es arbitrary: s, simp_all add : rewrites_accesses)

lemma esred_properties :
"esred esys \<sigma> esys' \<sigma>' \<Longrightarrow> fvEsv esys' \<subseteq> fvEsv esys 
                         \<and> wrEsv esys' \<subseteq> wrEsv esys \<and> agrees (- wrEsv esys) (fst \<sigma>) (fst \<sigma>')"
  apply (erule esred.induct, simp_all)
    apply (simp add: le_supI1 rered_properties agrees_def)
    apply (metis (mono_tags, lifting) IntD1 agrees_def rered_properties)
   apply (simp add: agrees_refl)
  apply (simp add: le_supI1 rered_properties agrees_def)
  by auto

lemma esaccesses_agrees: 
"agrees (fvEsv esys) s s' \<Longrightarrow> esaccesses esys s = esaccesses esys s'"
  apply (induct esys arbitrary: s s', simp_all add: exp_agrees, clarsimp)
  by (simp add: reaccesses_agrees)

lemma eswrites_agrees: 
"agrees (fvEsv esys) s s' \<Longrightarrow> eswrite esys s = eswrite esys s'"
  apply (induct esys arbitrary: s s', simp_all add: exp_agrees, clarsimp)
  by (simp add: rewrites_agrees)

lemma esred_agrees[rule_format] : 
"esred esys \<sigma> esys' \<sigma>' \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvEsv esys \<subseteq> X \<longrightarrow>
   (\<exists>s' h'. esred esys (s, h) esys' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  apply (erule esred.induct, simp_all, clarsimp)
  apply (drule_tac X = "X" and s = "s" in rered_agrees, simp_all)
    apply (clarsimp, rule_tac x = "s'" in exI, simp add: esred.red_EvtSeq1)
   apply (clarsimp, rule_tac x = "s" in exI, simp add: esred.red_EvtSeq2)
  apply (clarsimp, rule_tac x = "s" in exI, simp add: esred.red_EvtSet)
  done

lemma esaborts_agrees[rule_format] :
"esaborts esys \<sigma> \<Longrightarrow> \<forall>s'. agrees (fvEsv esys) (fst \<sigma>) s' \<longrightarrow> snd \<sigma> = h' \<longrightarrow> esaborts esys (s', h')"
  apply (erule esaborts.induct, simp_all)
  apply (auto simp add: rewrites_agrees reaccesses_agrees exp_agrees, auto simp add: agrees_def)
  by (simp add: aborts_Esys agrees_def reaborts_agrees)

subsection \<open>functions for resource event system \<close>

subsubsection \<open>locks that a resource event system is currently holding \<close>

definition 
  reslocked :: "resys \<Rightarrow> rname set"
  where
  "reslocked res = eslocked (snd res)"

definition 
  resllocked :: "resys \<Rightarrow> rname list"
  where
  "resllocked res = esllocked (snd res)"

lemma reslocked_eq: "reslocked res = set (resllocked res)"
  by (simp add: eslocked_eq resllocked_def reslocked_def)

subsubsection \<open>memory accesses and memory writes a resouce event system performs in one step \<close>

definition
  resaccesses :: "resys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "resaccesses res s = esaccesses (snd res) s"

definition 
  reswrite :: "resys \<Rightarrow> stack \<Rightarrow> nat set"
  where
  "reswrite res s = eswrite (snd res) s"

subsubsection \<open>A resource event system aborts in a given state\<close>

definition 
  resaborts :: "resys \<Rightarrow> state \<Rightarrow> bool"
  where
  "resaborts res \<sigma> = esaborts (snd res) \<sigma>"

subsubsection \<open>free variable of resource event system\<close>

definition
  fvREsv :: "resys \<Rightarrow> var set"
  where
  "fvREsv resys = fvEsv (snd resys)"

subsubsection \<open>all variables may be updated by a resource event system\<close>

definition
  wrREsv :: "resys \<Rightarrow> var set"
  where
  "wrREsv resys = wrEsv (snd resys)"
                   
subsubsection \<open>Basic properties about resource event system semantics\<close>

lemma reswrites_accesses : "reswrite res s \<subseteq> resaccesses res s"
  by (simp add: reswrite_def resaccesses_def eswrites_accesses)

lemma resred_properties :
"resred resys \<sigma> resys' \<sigma>' \<Longrightarrow> fvREsv resys' \<subseteq> fvREsv resys 
                         \<and> wrREsv resys' \<subseteq> wrREsv resys \<and> agrees (- wrREsv resys) (fst \<sigma>) (fst \<sigma>')"
  apply (erule resred.induct, simp_all add: fvREsv_def wrREsv_def)
    apply (metis agrees_search(1) agrees_simps(4) le_supI1 rered_properties sup_inf_absorb)
   apply (simp add: wrREv_def agrees_refl)
  apply (simp add: wrREv_def fvREv_def)
  by (metis (mono_tags, lifting) Ball_Collect agrees_def snd_conv)

lemma resaccesses_agrees: 
"agrees (fvREsv resys) s s' \<Longrightarrow> resaccesses resys s = resaccesses resys s'"
  apply (induct resys arbitrary: s s', simp add: fvREsv_def resaccesses_def)
  by (simp add: esaccesses_agrees)

lemma reswrites_agrees: 
"agrees (fvREsv resys) s s' \<Longrightarrow> reswrite resys s = reswrite resys s'"
  apply (induct resys arbitrary: s s', simp_all add: fvREsv_def reswrite_def)
  by (simp add: eswrites_agrees)

lemma resred_agrees[rule_format] : 
"resred resys \<sigma> resys' \<sigma>' \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvREsv resys \<subseteq> X \<longrightarrow>
   (\<exists>s' h'. resred resys (s, h) resys' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  apply (erule resred.induct, simp_all add: fvREsv_def wrREsv_def, clarsimp)
  apply (drule_tac X = "X" and s = "s" in rered_agrees, simp_all)
    apply (clarsimp, rule_tac x = "s'" in exI, simp add: resred.red_EvtSeq1)
   apply (clarsimp, rule_tac x = "s" in exI, simp add: resred.red_EvtSeq2)
  apply (clarsimp, rule_tac x = "s" in exI, simp add: resred.red_EvtSet)
  done

lemma resaborts_agrees[rule_format] :
"resaborts resys \<sigma> \<Longrightarrow> \<forall>s'. agrees (fvREsv resys) (fst \<sigma>) s' 
                      \<longrightarrow> snd \<sigma> = h' \<longrightarrow> resaborts resys (s', h')"
  apply (simp add: resaborts_def fvREsv_def)
  by (simp add: esaborts_agrees)

subsection \<open>functions for parallel event system \<close>

subsubsection \<open>locks that a parallel system is currently holding \<close>

definition
  pesllocked :: "paresys \<Rightarrow> rname list"
  where
  "pesllocked pes = List.maps resllocked pes"

definition
  peslocked :: "paresys \<Rightarrow> rname set"
  where
  "peslocked pes = set (pesllocked pes)"

lemma empty_peslock : "peslocked [] = {}"
  by (simp add: maps_simps(2) pesllocked_def peslocked_def)

lemma induct_peslock : "peslocked (x # xs) = (reslocked x) \<union> peslocked (xs)"
  by (simp add: maps_simps(1) pesllocked_def peslocked_def reslocked_eq)

lemma peslocked_eq : "set (pesllocked pes) = peslocked pes"
  by (simp add: peslocked_def)

lemma maps_append : "List.maps f (l1 @ l2) = List.maps f l1 @ List.maps f l2"
  apply (induct l1, simp add: maps_simps)
  by (simp add: List.append.append_Cons maps_simps)

lemma peslocked_split : "k < length pes \<Longrightarrow> pesllocked pes = 
       pesllocked (take k pes) @ resllocked (pes ! k) @ pesllocked (drop (Suc k) pes)"
proof-
  assume a0: "k < length pes"
  then have " pes = take k pes @ (pes ! k) # drop (Suc k) pes"
    by (simp add: id_take_nth_drop)
  then have "pesllocked pes = pesllocked (take k pes @ (pes ! k) # drop (Suc k) pes)"
    by simp
  then have "pesllocked pes = List.maps resllocked (take k pes @ (pes ! k) # drop (Suc k) pes)"
    by (simp add: pesllocked_def)
  then have "pesllocked pes = List.maps resllocked (take k pes) 
           @ resllocked (pes ! k) @ List.maps resllocked (drop (Suc k) pes)"
    by (simp add: maps_append maps_simps(1))
  then show ?thesis
    by (simp add: pesllocked_def)
qed

inductive
  pesred :: "paresys \<Rightarrow> state \<Rightarrow> paresys \<Rightarrow> state \<Rightarrow> bool"
  where
  red_Par : "\<lbrakk>k < length pes;  pes ! k = res ; resred res \<sigma> res' \<sigma>';
             \<forall>k'. k' < length pes \<and> k \<noteq> k' \<longrightarrow> disjoint (reslocked res') (reslocked (pes ! k'))\<rbrakk> 
             \<Longrightarrow> pesred pes \<sigma> (pes[k := res']) \<sigma>'"

subsubsection \<open>A parallel system aborts in a given state\<close>

inductive
  pesaborts :: "paresys \<Rightarrow> state \<Rightarrow> bool"
  where
  aborts_Par : " \<exists>k. k < length  pes \<and> resaborts (pes ! k) \<sigma> \<Longrightarrow> pesaborts pes \<sigma>"
| aborts_Race : "\<exists>k1 k2. k1 < length pes \<and> k2 < length pes \<and> k1 \<noteq> k2  \<and> \<not> disjoint (resaccesses (pes ! k1) (fst \<sigma>)) 
                         (reswrite (pes ! k2) (fst \<sigma>)) \<Longrightarrow> pesaborts pes \<sigma>"


end

