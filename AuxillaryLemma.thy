theory AuxillaryLemma
  imports Lang VHelper Event_Computation
begin

subsection \<open>definition of addition of a list of heaps\<close>

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

lemma disjoint_map_list : "\<forall>r. r \<in> set l \<longrightarrow> disjoint (dom (\<Gamma> r)) (dom h)
      \<Longrightarrow> disjoint(dom h) (dom (hplus_list (map \<Gamma> l)))"
  using disjoint_hplus_list by force

lemma hplus_list_map_expand : "\<lbrakk> distinct l; r \<in> set l; \<forall>r1 r2. r1 \<in> set l \<and> r2 \<in> set l \<and> r1 \<noteq> r2 
                            \<longrightarrow> disjoint (dom (\<Gamma> r1)) (dom (\<Gamma> r2))\<rbrakk>
      \<Longrightarrow> hplus_list (map \<Gamma> l) =  \<Gamma> r ++ hplus_list (map \<Gamma> (removeAll r l))"
  apply (induct l, simp, clarsimp)
  apply (rule hsimps)
   apply (simp add: disjoint_map_list)
  by simp

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

lemma disjoint_heap_update : 
        "\<lbrakk> \<forall>k'. k' < length l \<and> k' \<noteq> k \<longrightarrow> disjoint (dom x) (dom (l ! k'));
        disjoint_heap_list l ; k < length l; l' = l[k := x] \<rbrakk>
    \<Longrightarrow> disjoint_heap_list l'"
  by (metis disjoint_list_equiv disjoint_search(1) length_list_update 
      nth_list_update_eq nth_list_update_neq)

lemma disjoint_heap_update1 : "\<lbrakk> disjoint (dom x) (dom (hplus_list (l[k := Map.empty])));
        disjoint_heap_list l ; k < length l; l' = l[k := x] \<rbrakk>
    \<Longrightarrow> disjoint_heap_list l'"
  apply (rule disjoint_heap_update, simp_all)
  by (metis disjoint_search(1) length_list_update nth_list_update_neq disjoint_hplus_list1)


end

