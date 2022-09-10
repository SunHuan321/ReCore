theory Event_Helper
  imports Lang VHelper Event_Computation AuxillaryLemma
begin

subsection \<open>definition of disjoint of locked list\<close>

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

lemma disjoint_locked_list_update : 
        "\<lbrakk> \<forall>k'. k' < length l \<and> k' \<noteq> k \<longrightarrow> disjoint (reslocked re) (reslocked (l ! k'));
        disjoint_locked_list l ; k < length l \<rbrakk>
    \<Longrightarrow> disjoint_locked_list (l [k := re])"
  apply (simp add: disjoint_locked_list_equiv, clarify)
  apply (case_tac "k1 = k", simp)
  apply (case_tac "k2 = k")
   apply auto[1]
  by simp

subsection \<open>user-defined and well-formed function\<close>
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

definition user_rpesys :: "rparesys \<Rightarrow> bool"
  where "user_rpesys rpes = user_pesys (resources_pes (fst rpes) (snd rpes))"

definition wf_rpesys :: "rparesys \<Rightarrow> bool"
  where "wf_rpesys rpes = wf_pesys (resources_pes (fst rpes) (snd rpes))"

lemma user_rpesys_equiv: "user_pesys (resources_pes rs pes) \<Longrightarrow>  user_rpesys (rs, pes)"
  by (simp add: user_rpesys_def)

lemma wf_rpesys_equiv: "wf_pesys (resources_pes rs pes) \<Longrightarrow>  wf_rpesys (rs, pes)"
  by (simp add: wf_rpesys_def)

subsection \<open>auxillary lemma used to prove parallel event system\<close>

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

end

