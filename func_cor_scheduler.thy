theory func_cor_scheduler
  imports Stack_Aux
begin

definition s6_pre_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s6_pre_noframe p t r x xs = ((thread_node p t) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[sched \<diamondop> SECOND_READY]\<^sub>v =\<^sub>b [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_ready_sl (thd_next x) xs) ** ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n)"

definition s6_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s6_post p t r x xs = ((thread_node p (t :=\<^sub>s\<^sub>t READY)) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[sched \<diamondop> SECOND_READY]\<^sub>v =\<^sub>b [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_ready_sl (thd_next x) xs) ** ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n)"

definition s7_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s7_post p t r x xs = ((thread_node p ((t :=\<^sub>s\<^sub>t READY) :=\<^sub>n\<^sub>x (thd_next x))) \<and>\<^sub>S\<^sub>L 
  \<langle>[sched \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L  \<langle>[sched \<diamondop> SECOND_READY]\<^sub>v =\<^sub>b [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** 
  (thread_ready_sl (thd_next x) xs) ** ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n)"

definition s8_pre :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s8_pre p t r x xs = (thread_node p ((t :=\<^sub>s\<^sub>t READY) :=\<^sub>n\<^sub>x (thd_next x))) ** 
  (thread_ready_sl (thd_next x) xs) ** ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma s7_post_implies : "s7_post p t r x xs \<sqsubseteq> s8_pre p t r x xs"
   apply (simp add: s7_post_def s8_pre_def implies_def) by blast

definition s8_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s8_post p t r x xs = (thread_node p ((t :=\<^sub>s\<^sub>t READY) :=\<^sub>n\<^sub>x (thd_next x))) ** 
  (thread_ready_sl (thd_next x) xs) ** ([A_Readyq]\<^sub>v \<longmapsto> [p]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma s8_post_implies : "s8_post p t r x xs \<sqsubseteq> inv_readyq1 p ((Suc K_NO_WAIT, thd_next x, thd_data t) # xs)"
  apply (rule_tac Q = "(thread_node p ((t :=\<^sub>s\<^sub>t READY) :=\<^sub>n\<^sub>x (thd_next x))) ** (thread_ready_sl 
  (thd_next x) xs) ** ([A_Readyq]\<^sub>v \<longmapsto> [p]\<^sub>n)" in implies_trans)
   apply (simp add: s8_post_def implies_def) apply auto[1]
  apply (rule equiv_implies)
  apply (rule_tac Q = "([A_Readyq]\<^sub>v \<longmapsto> [p]\<^sub>n) ** (thread_node p (t :=\<^sub>s\<^sub>t EBUSY :=\<^sub>n\<^sub>x thd_next x) ** 
  thread_ready_sl (thd_next x) xs)" in assn_equiv_trans, simp add: Astar_commute_equiv)
  apply (simp add: inv_readyq1_def, rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (rule_tac Q = "thread_ready_sl p ((Suc K_NO_WAIT, thd_next x, thd_data t) # xs)" in
  assn_equiv_trans)
   apply (rule_tac Q = "thread_node p (READY, thd_next x, thd_data t) ** thread_ready_sl (thd_next 
  (READY, thd_next x, thd_data t)) xs" in assn_equiv_trans)
    apply (rule assn_equiv_cong_star, simp add: uptcb_state_def uptcb_next_def thd_st_def thd_data_def)
     apply (simp add: assn_equiv_def, simp add: assn_equiv_reflex thd_next_def)
   apply (simp add: thd_st_def thread_ready_sl_insert)
  by (simp add: assn_equiv_symmetry readyq_equiv)

lemma safe_s68_noframe: "fvAs \<Gamma> = {} \<Longrightarrow>  
         \<Gamma>(Stack := inv_stack, Readyq := Aemp, Cur := Aemp) \<turnstile> 
              {s6_pre_noframe p t r x xs}
             \<lbrakk>[sched \<diamondop> CUR_RUNNING]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [READY]\<^sub>n ;;
             \<lbrakk>[sched \<diamondop> CUR_RUNNING]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [sched \<diamondop> SECOND_READY]\<^sub>v;;
             \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> :=\<^sub>C [sched \<diamondop> CUR_RUNNING]\<^sub>v 
             {inv_readyq1 p ((READY, thd_next x, thd_data t) # xs)}"
   apply (rule_tac Q = "s7_post p t r x xs" in rule_seq)
    apply (rule_tac Q = "s6_post p t r x xs" in rule_seq)
     apply (simp add: s6_pre_noframe_def s6_post_def, intro rule_frame)
  apply (rule_tac Pa = "(thread_node p t \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>[sched \<diamondop>SECOND_READY]\<^sub>v =\<^sub>b
   [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and Qa = "(thread_node p (t :=\<^sub>s\<^sub>t READY) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
   ** (\<langle>[sched \<diamondop>SECOND_READY]\<^sub>v =\<^sub>b [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"in safe_assn_equiv)
         apply (simp add: assn_equiv_def, simp add: assn_equiv_def)
       apply (rule rule_frame, simp add: thread_node_write_st', simp_all)
    apply (simp add: s6_post_def s7_post_def, intro rule_frame,simp add: thread_node_write_next_fromvar, simp_all)
   apply (rule_tac P = "s8_pre p t r x xs" and Q = "s8_post p t r x xs" in rule_conseq)
    apply (simp add: s8_pre_def s8_post_def, rule rule_frame1, rule rule_write_var2, simp)
   apply (simp add: s7_post_implies, simp add: s8_post_implies)
  done

lemma rule_inv_readyq : "\<forall>r xs. \<Gamma> \<turnstile> { (inv_readyq1 r xs)} C {Q} \<Longrightarrow>
        \<Gamma> \<turnstile> {inv_readyq} C {Q}"
  apply (simp add: CSL_def inv_readyq_def) 
  by auto
  

lemma rule_inv_post: "\<exists>r xs p x. \<Gamma> \<turnstile> {P} C { inv_cur1 p x ** inv_readyq1 r xs} \<Longrightarrow> 
       \<Gamma> \<turnstile> {P} C {inv_readyq ** inv_cur}"
  apply (simp add: inv_readyq_def inv_cur_def CSL_def)
  by (metis implies_star inv_cur_def inv_cur_implies2 inv_readyq_def inv_readyq_implies 
      safe_conseq safe_post_commute)
                                                
lemma rule_inv_pre: "\<forall>p t. \<Gamma> \<turnstile> {P ** inv_cur1 p t} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {P ** (Aexcur inv_cur1)} C {Q}"
  apply (simp add: CSL_def) by blast

definition s1_post :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s1_post r xs = ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n \<rangle>\<^sub>S\<^sub>L) ** 
        (is_readyq r xs)"

lemma s1_post_implies : "(s1_post r xs \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<sqsubseteq> inv_readyq1 r xs"
  apply (simp add: s1_post_def inv_readyq1_def implies_def) by auto

definition s3_pre :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s3_pre r a list = ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n) ** (thread_node r a \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b 
  [r]\<^sub>n \<rangle>\<^sub>S\<^sub>L) ** (thread_ready_sl (thd_next a) list)"

lemma s3_pre_implies_aux : "(P1 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L) ** (P3 ** P4) \<equiv>\<^sub>S\<^sub>L P1 ** (P3 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L) ** P4"
  apply (rule_tac Q = "P1 ** (P3 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P1 ** P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj, simp add: Astar_assoc_equiv assn_equiv_symmetry)
   apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def)
  by auto

lemma s3_pre_implies : "xs = a # list \<Longrightarrow> (s1_post r xs \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [sched \<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
                       \<sqsubseteq> s3_pre r a list"
  apply (rule_tac Q = "s1_post r xs" in implies_trans, simp add: implies_def)
  apply (rule_tac Q = "([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n \<rangle>\<^sub>S\<^sub>L) ** 
        (thread_ready_sl r (a # list))" in implies_trans, simp add: s1_post_def)
   apply (rule equiv_implies, rule assn_equiv_cong_star)
    apply (simp add: assn_equiv_reflex, simp add: readyq_equiv)
  apply (rule_tac Q = "([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n \<rangle>\<^sub>S\<^sub>L) ** 
  ((thread_node r a ) ** (thread_ready_sl (thd_next a) list))" in implies_trans)
   apply (rule implies_star, simp add: implies_def, simp add: ready_sl_implies)
  by (rule equiv_implies, simp add: s3_pre_def, simp add: s3_pre_implies_aux)

definition s3_post :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s3_post r a list = ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n) ** (thread_node r a \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b 
  [r]\<^sub>n \<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> SECOND_READY]\<^sub>v =\<^sub>b [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_ready_sl (thd_next a) list)"

definition s4_pre1 :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s4_pre1 r a list = (s3_post r a list) ** ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n)"

definition s4_pre2 :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s4_pre2 r a list = (s3_post r a list) ** (Aexcur inv_cur1)"

definition s4_post1 :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s4_post1 r a list = (s3_post r a list) ** ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>CUR_RUNNING]\<^sub>v 
  =\<^sub>b [NULL]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition s4_post2 :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "s4_post2 r a list p t = (s3_post r a list) ** (([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>CUR_RUNNING]\<^sub>v 
  =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node p t)"

definition s5_frame :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs  \<Rightarrow> assn"
  where "s5_frame r x xs  = ((thread_node r x) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** 
        thread_ready_sl (thd_next x) xs ** ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n)"

definition s5_pre :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s5_pre r a list = ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> SECOND_READY]\<^sub>v =\<^sub>b 
  [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** s5_frame r a list"

lemma s5_pre_implies_aux : "P1 ** (P2 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L) ** P5 ** P6 \<equiv>\<^sub>S\<^sub>L
                            (P1 \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L) ** ((P2 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L) ** P5 ** P6)"
  apply (rule_tac Q = "P1 ** P2 ** P5 ** P6 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P1 ** (P2 ** P5 ** P6) \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj, simp add: stack_node_equiv1_aux)
   apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by blast

lemma s5_pre_implies : "(s4_post1 r a list \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<sqsubseteq> s5_pre r a list"
  apply (rule_tac Q = "s4_post1 r a list" in implies_trans, simp add: implies_def)
  apply (simp add: s4_post1_def s3_post_def s5_pre_def s5_frame_def)
  apply (rule_tac Q = "[A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n ** (thread_node r a \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L 
  \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>SECOND_READY]\<^sub>v =\<^sub>b [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_ready_sl (thd_next a) list **
  ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n)" in implies_trans, simp add: implies_def) apply auto[1]
  by (rule equiv_implies, simp add: s5_pre_implies_aux) 
  
definition s5_post :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s5_post r a list = ([A_Readyq]\<^sub>v \<longmapsto> [thd_next a]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> SECOND_READY]\<^sub>v =\<^sub>b 
  [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** s5_frame r a list"

lemma s5_post_implies : " s5_post r a list \<sqsubseteq> [A_Readyq]\<^sub>v \<longmapsto> [thd_next a]\<^sub>n ** s5_frame r a list"
  apply (simp add: s5_post_def implies_def) by auto

definition s6_frame :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> assn"
  where "s6_frame r a p = ((thread_node r a) ** ([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v 
  =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma s6_pre_frame_implies_aux : "P1 ** (P2 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L) ** P5 ** ((P6 \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L) ** P8) \<equiv>\<^sub>S\<^sub>L
                                  (P8 \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L) ** P5 ** P1 ** (P2 ** P6 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** P5 ** (P6 ** P8) \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P8 ** P5 ** P1 ** (P2 ** P6) \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj)
    apply (rule_tac Q = "P8 ** (P5 ** P1 ** P2) ** P6" in assn_equiv_trans)
     apply (metis Astar_assoc_equiv Astar_commute_equiv assn_equiv_cong_star assn_equiv_trans)
    apply (meson Astar_assoc_equiv assn_equiv_cong_star assn_equiv_reflex assn_equiv_symmetry assn_equiv_trans)
   apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by auto

lemma s6_pre_frame_implies : "(s4_post2 r a list p t \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [sched \<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
      \<sqsubseteq> s6_pre_noframe p t r a list ** s6_frame r a p"
  apply (rule_tac Q = "s4_post2 r a list p t" in implies_trans, simp add: implies_def)
  apply (rule equiv_implies, simp add: s4_post2_def s3_post_def s6_pre_noframe_def s6_frame_def)
  by (simp add: s6_pre_frame_implies_aux)


definition s9_frame1 :: "nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s9_frame1 r a list = ([A_Readyq]\<^sub>v \<longmapsto> [thd_next a]\<^sub>n) ** (thread_ready_sl (thd_next a) list)"

definition s9_frame2 :: "nat \<Rightarrow> tcb \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> assn"
  where "s9_frame2 p t x xs  = ([A_Readyq]\<^sub>v \<longmapsto> [p]\<^sub>n) ** (thread_ready_sl p ((READY, thd_next x, thd_data t)
        # xs))"

definition s9_pre_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> assn"
  where "s9_pre_noframe r x p = (thread_node r x \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
                          ** ([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n)"

lemma s9_pre_frame1_equiv : "s9_pre_noframe r a NULL ** s9_frame1 r a list  \<equiv>\<^sub>S\<^sub>L 
                            [A_Readyq]\<^sub>v \<longmapsto> [thd_next a]\<^sub>n ** s5_frame r a list"
  apply (simp add: s9_pre_noframe_def s9_frame1_def s5_frame_def)
  by (meson Astar_assoc_equiv Astar_commute_equiv assn_equiv_symmetry assn_equiv_trans 
      stack_node_equiv2_aux)

definition s10_pre_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> assn"
  where "s10_pre_noframe r x p = (thread_node r (x :=\<^sub>s\<^sub>t RUNNING) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L)
        ** ([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n)"

lemma safe_s9_noframe : "fvAs \<Gamma> = {} \<Longrightarrow>
                        \<Gamma>(Stack := inv_stack, Readyq := Aemp,Cur :=Aemp) \<turnstile> 
                        { s9_pre_noframe r a p } 
                        \<lbrakk>[sched \<diamondop>FIRST_READY]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [EAGAIN]\<^sub>n 
                        { s10_pre_noframe r a p}"
  apply (simp add: s9_pre_noframe_def s10_pre_noframe_def)
  by (rule rule_frame, simp add: thread_node_write_st', simp add: disjoint_def)

definition s10_post_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "s10_post_noframe r x  = (thread_node r (x :=\<^sub>s\<^sub>t RUNNING) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L)
        ** ([A_Cur]\<^sub>v \<longmapsto> [r]\<^sub>n)"

lemma safe_s10_noframe : "fvAs \<Gamma> = {} \<Longrightarrow>
         \<Gamma>(Stack := inv_stack, Readyq := Aemp, Cur := Aemp) \<turnstile> 
         { s10_pre_noframe r a p } 
        \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> :=\<^sub>C [sched \<diamondop>FIRST_READY]\<^sub>v 
        { s10_post_noframe r a}"
  apply (simp add: s10_pre_noframe_def s10_post_noframe_def)
  apply (rule_tac Pa = "(([A_Cur]\<^sub>v \<longmapsto>[p]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
         ** (thread_node r (a :=\<^sub>s\<^sub>t RUNNING))" and Qa = "(([A_Cur]\<^sub>v \<longmapsto>[r]\<^sub>n) 
         \<and>\<^sub>S\<^sub>L \<langle>[sched \<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L)** (thread_node r (a :=\<^sub>s\<^sub>t RUNNING))" in safe_assn_equiv)
     apply (simp add: assn_equiv_def) using disjoint_search(1) map_add_commute apply blast
   apply (simp add: assn_equiv_def) using disjoint_search(1) map_add_commute apply blast
  by (simp add: rule_frame rule_write_var2)

lemma s9_pre_frame2_implies : "inv_readyq1 p ((READY, thd_next a, thd_data t) # list) ** 
      s6_frame r a p \<sqsubseteq> s9_pre_noframe r a p ** s9_frame2 p t a list"
  apply (rule_tac Q = "s9_frame2 p t a list ** s9_pre_noframe r a p" in implies_trans)
   apply (rule implies_star, simp add: inv_readyq1_def s9_frame2_def)
    apply (rule implies_star, simp add: implies_def)
    apply (rule equiv_implies, simp add: readyq_equiv)
   apply (simp add: s6_frame_def s9_pre_noframe_def implies_def)
  by (simp add: Astar_commute_equiv equiv_implies)

lemma s10_post_frame1_implies : " s10_post_noframe r a  ** s9_frame1 r a list \<sqsubseteq> 
                                  inv_readyq ** inv_cur"
  apply (rule_tac Q = " inv_cur1 r (a :=\<^sub>s\<^sub>t RUNNING) ** inv_readyq1 (thd_next a) list" in implies_trans)
  apply (rule_tac Q = "(thread_node r (a :=\<^sub>s\<^sub>t RUNNING) ** ([A_Cur]\<^sub>v \<longmapsto> [r]\<^sub>n)) ** s9_frame1 r a list"
  in implies_trans, rule implies_star, simp add: s10_post_noframe_def)
     apply (simp add: implies_def) apply auto[1] apply (simp add: implies_def)
   apply (rule equiv_implies, rule assn_equiv_cong_star)
    apply (simp add: inv_cur1_def is_cur_def inv_is_running_def is_running_def uptcb_state_def)
    apply (simp add: thd_st_def) using Astar_commute_equiv Conj_true_equiv assn_equiv_conj_Apure 
    assn_equiv_symmetry assn_equiv_trans apply blast
  apply (simp add: s9_frame1_def inv_readyq1_def)
   apply (simp add: assn_equiv_cong_star assn_equiv_reflex assn_equiv_symmetry readyq_equiv)
  apply (rule_tac Q = "inv_cur ** inv_readyq" in implies_trans) 
   apply (simp add: implies_star inv_cur_implies2 inv_readyq_implies)
  by (simp add: Astar_commute_equiv equiv_implies)

lemma s10_post_frame2_implies : " s10_post_noframe r a ** s9_frame2 p t a list \<sqsubseteq> inv_readyq ** inv_cur"
  apply (rule_tac Q = " inv_cur1 r (a :=\<^sub>s\<^sub>t RUNNING) ** inv_readyq1 p ((READY, thd_next a, thd_data t) 
  # list)" in implies_trans)
   apply (rule implies_star, simp add: s10_post_noframe_def inv_cur1_def is_cur_def)
    apply (rule_tac Q = "thread_node r (a :=\<^sub>s\<^sub>t RUNNING) ** ([A_Cur]\<^sub>v \<longmapsto> [r]\<^sub>n)" in implies_trans)
  apply (simp add: implies_def) apply auto
    apply (simp add: inv_is_running_def is_running_def thd_st_def uptcb_state_def)
  using Astar_commute_equiv Conj_true_equiv assn_equiv_conj_Apure assn_equiv_symmetry assn_equiv_trans 
  equiv_implies apply blast
   apply (rule equiv_implies, simp add: s9_frame2_def inv_readyq1_def)
   apply (simp add: assn_equiv_cong_star assn_equiv_reflex assn_equiv_symmetry readyq_equiv)
  apply (rule_tac Q = "inv_cur ** inv_readyq" in implies_trans)
   apply (simp add: implies_star inv_cur_implies2 inv_readyq_implies)
  by (simp add: Astar_commute_equiv equiv_implies)

lemma safe_scheduler : "fvAs \<Gamma> = {} \<Longrightarrow> 
                      \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                      {Aemp} scheduler {Aemp}"
  apply (rule rule_with_true', simp) 
  apply (rule_tac Pa = "inv_readyq" and Qa = "inv_readyq" in safe_assn_equiv)
    apply (simp add: assn_equiv_def, simp add: assn_equiv_def)
  apply (rule rule_inv_readyq, intro allI)
  apply (rule_tac Q = "s1_post r xs" in rule_seq, simp add: inv_readyq1_def s1_post_def)
   apply (rule rule_frame, rule rule_read)
    apply (simp add: fvA_Gamma fvA_inv_cur fvA_inv_stack)
  using local_resource_distinct2 apply force
   apply (simp add: fvA_is_readyq)
  apply (rule rule_if)
(* Readyq = NULL *)
   apply (rule_tac P = "inv_readyq1 r xs" and Q = "inv_readyq1 r xs" in rule_conseq)
     apply (rule rule_skip, simp add: s1_post_implies, simp add: inv_readyq_implies)
(* Readyq \<noteq> NULL *)
  apply (case_tac r, simp add: s1_post_def CSL_def) using stm_def apply auto[1]
  apply (case_tac xs, simp add: s1_post_def is_readyq_def thread_sl_def CSL_def)
  apply (rule_tac Q = "s3_post r a list" in rule_seq)
   apply (rule_tac P = "s3_pre r a list" and Q = "s3_post r a list" in rule_conseq)
  apply (simp only: s3_pre_def s3_post_def, rule rule_frame, rule rule_frame1)
       apply (rule thread_node_readnext, simp add: local_distinct2)
        apply (simp add: fvA_Gamma fvA_inv_cur fvA_inv_stack)
  using local_resource_distinct2 apply force
       apply (simp add: fvA_Gamma fvA_inv_cur fvA_inv_stack)
  using local_resource_distinct2 apply force
      apply (simp add: disjoint_def)
  using local_resource_distinct2 apply force
  apply (simp add: fvA_thread_ready_sl)
    apply (simp add: s3_pre_implies, simp add: implies_def)
  apply (rule rule_with_true', simp)
    apply (rule_tac Pa = "(s4_pre1 r a list) \<or>\<^sub>S\<^sub>L (s4_pre2 r a list)" and Qa = "(inv_readyq ** inv_cur)
    \<or>\<^sub>S\<^sub>L (inv_readyq ** inv_cur)" in safe_assn_equiv)
    apply (simp add: inv_cur_def s4_pre1_def s4_pre2_def assn_equiv_symmetry Astar_disj_dist)
   apply (simp add: assn_equiv_def)
  apply (rule rule_disj)
(* cur = NULL *)
   apply (rule_tac Q = "s10_pre_noframe r a NULL ** s9_frame1 r a list" in rule_seq)
    apply (rule_tac Q = "[A_Readyq]\<^sub>v \<longmapsto> [thd_next a]\<^sub>n ** s5_frame r a list " in rule_seq)
     apply (rule_tac Q = "s4_post1 r a list" in rule_seq, simp add: s4_post1_def s4_pre1_def)
      apply (rule rule_frame1, rule rule_read)
       apply (simp add: fvA_Gamma1 fvA_inv_stack fvA_inv_cur)
  using local_resource_distinct2 apply force
      apply (simp add: s3_post_def fvA_thread_ready_sl disjoint_def)
  using local_resource_distinct2 local_distinct2 apply force
  apply (rule rule_if)
      apply (rule_tac P = "s5_pre r a list" and Q = "s5_post r a list" in rule_conseq)
        apply (simp add: s5_pre_def s5_post_def, rule rule_frame)
         apply (rule rule_write_var2, simp add: s5_frame_def)
       apply (simp add: s5_pre_implies, simp add: s5_post_implies)
     apply (simp add: s4_post1_def CSL_def) using stm_def apply auto[1]
  apply (rule_tac Pa = "s9_pre_noframe r a NULL ** s9_frame1 r a list" and Qa = "s10_pre_noframe r a
  NULL ** s9_frame1 r a list" in safe_assn_equiv)
      apply (simp add: s9_pre_frame1_equiv, simp add: assn_equiv_reflex)
    apply (rule rule_frame, simp add: safe_s9_noframe, simp)
  apply (rule_tac P = "s10_pre_noframe r a NULL ** s9_frame1 r a list" and Q = "s10_post_noframe r a 
   ** s9_frame1 r a list" in rule_conseq)
     apply (rule rule_frame, simp add: safe_s10_noframe, simp, simp add: implies_def)
   apply (simp add: s10_post_frame1_implies)
(* cur \<noteq> NULL *)
  apply (simp add: s4_pre2_def, rule rule_inv_pre, intro allI)
  apply (rule_tac Q = "s10_pre_noframe r a p ** s9_frame2 p t a list" in rule_seq)
   apply (rule_tac Q = "s9_pre_noframe r a p ** s9_frame2 p t a  list" in rule_seq)
    apply (rule_tac Q = "s4_post2 r a list p t" in rule_seq, simp add: s4_post2_def)
     apply (rule rule_frame1, simp add: inv_cur1_def is_cur_def)
  apply (rule_tac P = "[A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n **  (thread_node p t)" and Q = "([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n \<and>\<^sub>S\<^sub>L 
  \<langle>[sched \<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node p t" in rule_conseq)
        apply (rule rule_frame, rule rule_read, simp add: fvA_Gamma1 fvA_inv_stack)
  using local_resource_distinct2 apply force
        apply (simp add: fvA_thread_node, simp add: implies_def) apply auto[1]
      apply (simp add: implies_def, simp add: s3_post_def fvA_thread_ready_sl disjoint_def)
  using local_resource_distinct2 local_distinct2 apply force
    apply (rule rule_if, simp add: s4_post2_def, case_tac p, simp add: CSL_def)
     apply (simp add: CSL_def) using stm_def apply linarith
  apply (rule_tac P = "s6_pre_noframe p t r a list ** s6_frame r a p" and Q = "inv_readyq1 p ((READY, 
  thd_next a, thd_data t) # list) ** s6_frame r a p" in rule_conseq)
      apply (rule rule_frame) using safe_s68_noframe apply auto[1]
      apply (simp, simp add: s6_pre_frame_implies) using s9_pre_frame2_implies apply auto[1]
   apply (rule rule_frame, simp add: safe_s9_noframe, simp)
  apply (rule_tac P = "s10_pre_noframe r a p ** s9_frame2 p t a list" and Q = "s10_post_noframe r a 
  ** s9_frame2 p t a list" in rule_conseq)
    apply (rule rule_frame, simp add: safe_s10_noframe)
    apply (simp, simp add: implies_def)
  apply (simp add: s10_post_frame2_implies)
  done

end