theory func_cor_push
  imports Stack_Aux
begin

definition p1_post :: "nat \<Rightarrow> assn"
  where "p1_post t = (\<langle>[t\<diamondop>END]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"


definition p4_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p4_post_noframe t s st = ([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L
      \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> TOP]\<^sub>v =\<^sub>b [stack_top st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma safe_p24_noframe : "fvAs \<Gamma> = {} \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          {([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** stack_node s st}
                            (t \<^enum> (t \<diamondop> ADDR) :=\<^sub>C \<lbrakk>[A_Stack]\<^sub>v\<rbrakk>) ;;
                            (t \<^enum> (t \<diamondop> NEXT) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
                            (t \<^enum> (t \<diamondop> TOP) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>stop\<rbrakk>) 
                          {p4_post_noframe t s st}"
  apply (rule_tac Q = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L
      \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in rule_seq)
   apply (rule_tac Q = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in rule_seq)
  apply (rule_tac Pa = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** stack_node s st" and Qa = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n \<and>\<^sub>S\<^sub>L 
  \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node s st" in safe_assn_equiv, simp add: assn_equiv_reflex)
     apply (simp add: assn_equiv_def) apply auto[1]
    apply (rule rule_frame, rule rule_stm_stack', simp_all)
         apply (simp add: disjoint_def Thread_Local_def, simp add: Thread_Local_def, simp add: Thread_Local_def)
      apply (rule rule_read, simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_inv_stack)
  apply (simp add: Thread_Local_def, simp add: Thread_Local_def)
    apply (simp add: stack_node_def) apply (rule rule_frame1)
    apply (rule rule_stm_stack' , simp_all, simp add: disjoint_def Thread_Local_def)
       apply (simp add: stack_node_def Thread_Local_def)
      apply (simp add: stack_node_def Thread_Local_def)
    apply (rule stack_node_read_next, simp add: Thread_Local_def)
     apply (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_inv_stack)
     apply (simp add: Thread_Local_def, simp add: Thread_Local_def)
    apply (simp add: Thread_Local_def, simp add: disjoint_def stm_def Thread_Local_def)
  apply (simp add: p4_post_noframe_def, rule rule_frame1, rule rule_stm_stack', simp_all)
       apply (simp add: disjoint_def Thread_Local_def)
      apply (simp add: stack_node_def Thread_Local_def)
     apply (simp add: stack_node_def Thread_Local_def)
    apply (rule stack_node_read_top1)
      apply (simp add: Thread_Local_def, simp add: Thread_Local_def)
     apply (simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_readyq fvA_inv_cur Thread_Local_def)
  apply (simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_readyq fvA_inv_cur Thread_Local_def)
   apply (simp add: Thread_Local_def, simp add: disjoint_def stm_def Thread_Local_def)
  done

definition p4_frame :: " stack_mem \<Rightarrow> assn"
  where "p4_frame s = ((is_waitq (stack_wait s) (stack_tcbs s) **
         (buf (stack_base s) (stack_top s) (stack_buf s))) \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq s) 
         \<and>\<^sub>S\<^sub>L (inv_stack_pt s))"

lemma safe_p24_pre_equiv_aux : "P1 ** (P2 ** P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                                P1 ** P2 ** (P3 ** P4 \<and>\<^sub>S\<^sub>L  \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** (P2 ** (P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L))" in assn_equiv_trans)
   apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex) 
   apply (rule_tac Q = "P2 ** (P3 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
    apply (simp add: Astar_assoc_equiv assn_equiv_conj)
  using assn_equiv_def apply auto[1]
  by (simp add: Astar_assoc_equiv assn_equiv_symmetry)

lemma safe_p24_pre_equiv : "inv_stack1 s st \<equiv>\<^sub>S\<^sub>L  (([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** stack_node s st) **
                            p4_frame st"
  apply (simp add: inv_stack1_def is_stack_def p4_frame_def inv_stack_buf_waitq_def inv_stack_pt_def)
  by (simp add: safe_p24_pre_equiv_aux)

lemma safe_p24 : "fvAs \<Gamma> = {} \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          {p1_post t ** inv_stack1 s st}
                            (t \<^enum> (t \<diamondop> ADDR) :=\<^sub>C \<lbrakk>[A_Stack]\<^sub>v\<rbrakk>) ;;
                            (t \<^enum> (t \<diamondop> NEXT) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
                            (t \<^enum> (t \<diamondop> TOP) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>stop\<rbrakk>) 
                          {p1_post t ** (p4_post_noframe t s st ** p4_frame st)}"
  apply (rule rule_frame1, rule_tac Pa = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** stack_node s st ** p4_frame st"
  and Qa = "p4_post_noframe t s st ** p4_frame st" in safe_assn_equiv)
     apply (simp add: assn_equiv_symmetry safe_p24_pre_equiv, simp add: assn_equiv_reflex)
   apply (rule rule_frame, simp add: safe_p24_noframe)
   apply (simp add: p4_frame_def fvA_is_waitq fvA_buf inv_stack_pt_def inv_stack_buf_waitq_def)
  apply (simp add: p1_post_def stm_def disjoint_def Thread_Local_def)
  done

lemma p5_pre_implies : "(p1_post t ** (p4_post_noframe t s st ** p4_frame st) \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>NEXT]\<^sub>v =\<^sub>b [t\<diamondop>TOP]\<^sub>v\<rangle>\<^sub>S\<^sub>L)
                         \<sqsubseteq> inv_stack1 s st"
  apply (rule_tac Q = "(([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** stack_node s st) **  p4_frame st" in implies_trans)
   apply (simp add: p1_post_def p4_post_noframe_def implies_def) apply blast
  by (rule equiv_implies, simp add: assn_equiv_symmetry safe_p24_pre_equiv)

lemma safe_p56 : "fvAs \<Gamma> = {} \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          { inv_stack1 s st}
                          (t \<^enum> (t \<diamondop> RET) :=\<^sub>C [ENOMEM]\<^sub>n) ;;
                          (t \<^enum> (t \<diamondop> END) :=\<^sub>C [1]\<^sub>n)
                          { inv_stack1 s st}"
  apply (rule_tac Q = "inv_stack1 s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> RET]\<^sub>v =\<^sub>b [ENOMEM]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_seq)
   apply (rule rule_stm_stack', simp_all)
        apply (simp add: disjoint_def Thread_Local_def)
      apply (simp add: inv_stack1_def fvA_is_stack Thread_Local_def)
     apply (simp add: inv_stack1_def fvA_is_stack Thread_Local_def)
    apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
    apply (simp add: inv_stack1_def fvA_is_stack Thread_Local_def, simp add: Thread_Local_def)
  apply (rule_tac P = "inv_stack1 s st" and Q = "inv_stack1 s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> END]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_conseq)
    apply (rule rule_stm_stack', simp_all)
        apply (simp add: disjoint_def Thread_Local_def)
       apply (simp add: inv_stack1_def fvA_is_stack Thread_Local_def)
      apply (simp add: inv_stack1_def fvA_is_stack Thread_Local_def)
     apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
  apply (simp add: inv_stack1_def fvA_is_stack Thread_Local_def, simp add: Thread_Local_def)
  by (simp_all add: implies_def)

definition p7_pre_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p7_pre_noframe t s st = ([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L
          \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition p7_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p7_post_noframe t s st = ([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L
  \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma safe_p7_noframe : "fvAs \<Gamma> = {} \<Longrightarrow> 
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          { p7_pre_noframe t s st}
                     t\<diamondop>FIRST_PENDING_THREAD :=\<^sub>C \<lbrakk>[t\<diamondop>ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk>
                          { p7_post_noframe t s st}"
  apply (simp add: p7_pre_noframe_def p7_post_noframe_def, rule rule_frame1)
  apply (rule_tac Pa = "(stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b 
  [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and Qa = "(stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L  \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  in safe_assn_equiv, simp_all add: assn_equiv_def) apply auto[1]
   apply (rule rule_frame, rule stack_node_read_wait, simp add: Thread_Local_def)
  by (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_stack fvA_inv_readyq disjoint_def Thread_Local_def)

definition p9_pre_noframe :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p9_pre_noframe t s a list st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** is_waitq (stack_wait st) (a # list)"

definition p9_pre :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p9_pre t s a list st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_node 
  (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_wait_sl (thd_next a)
  list )"

lemma p9_pre_implies_aux : "(P1 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L) ** (P4 ** P5) \<equiv>\<^sub>S\<^sub>L 
                            (P1 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L) ** (P4 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L) ** P5"
  apply (rule_tac Q = "P1 ** (P4 ** P5) \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P1 ** P4 ** P5 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj, simp add: Astar_assoc_equiv assn_equiv_symmetry)
  apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by auto

lemma p9_pre_implies : "p9_pre_noframe t s a list st \<sqsubseteq> p9_pre t s a list st"
  apply (rule_tac Q = "(stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b 
  [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl (stack_wait st) (a # list)" in implies_trans)
  apply (rule equiv_implies, simp add: p9_pre_noframe_def)
  using assn_equiv_cong_star assn_equiv_reflex waitq_equiv apply auto[1]
  apply (rule_tac Q = "(stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b 
  [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_node (stack_wait st) a ** thread_wait_sl (thd_next a) list)" in implies_trans)
   apply (rule implies_star, simp add: implies_def)
   apply (case_tac "stack_wait st", simp add: thread_wait_sl_def, simp add: implies_def)
   apply (simp add: thread_wait_sl_def implies_def) apply auto[1]
  by (rule equiv_implies, simp add: p9_pre_def p9_pre_implies_aux)
  
definition p9_post :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p9_post t s a list st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_node 
  (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>WAITQ]\<^sub>v =\<^sub>b [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** (thread_wait_sl (thd_next a) list)"

definition p10_pre :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p10_pre t s a list st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>WAITQ]\<^sub>v =\<^sub>b [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** (thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L ) 
  ** (thread_wait_sl (thd_next a) list)"

lemma p9_post_equiv_aux : "(P1 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L) ** (P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L) ** P6 \<equiv>\<^sub>S\<^sub>L
                           (P1 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L) ** (P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L) ** P6"
  apply (rule_tac Q = "P1 ** P4 ** P6 \<and>\<^sub>S\<^sub>L \<langle>P2\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp_all add: assn_equiv_def) by auto

lemma p9_post_equiv : "p10_pre t s a list st  \<equiv>\<^sub>S\<^sub>L p9_post t s a list st"
  by (simp add: p10_pre_def p9_post_def p9_post_equiv_aux) 

definition p10_post :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p10_post t s a list st = (stack_node s (st:=\<^sub>w\<^sub>a thd_next a) \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>WAITQ]\<^sub>v =\<^sub>b [thd_next a]\<^sub>n\<rangle>\<^sub>S\<^sub>L)  ** (thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v 
  =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_wait_sl (thd_next a) list)"

definition p10_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> tcbs \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p10_post_noframe t s a list st = stack_node s (st:=\<^sub>w\<^sub>a thd_next a) ** (is_waitq (thd_next a) 
  list) ** (thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) "

lemma p10_post_implies : " p10_post t s a list st \<sqsubseteq> p10_post_noframe t s a list st"
  apply (rule_tac Q = "stack_node s (st :=\<^sub>w\<^sub>a thd_next a) ** (thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl (thd_next a) list" in implies_trans)
   apply (simp add: p10_post_def implies_def) apply auto[1]
  apply (rule equiv_implies, simp add: p10_post_noframe_def)
  apply (rule_tac Q = "stack_node s (st :=\<^sub>w\<^sub>a thd_next a) ** (thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** is_waitq (thd_next a) list" in assn_equiv_trans)
   apply (meson Astar_commute_equiv assn_equiv_cong_star assn_equiv_symmetry assn_equiv_trans waitq_equiv)
  by (simp add: Astar_assoc_equiv2)

lemma safe_p910_noframe : "\<lbrakk>fvAs \<Gamma> = {}; stack_pt st; stack_next st \<noteq> stack_top st\<rbrakk> \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          { p9_pre_noframe t s a list st}
                          t\<diamondop>WAITQ :=\<^sub>C \<lbrakk>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk>;;
                          \<lbrakk>[t\<diamondop>ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [t\<diamondop>WAITQ]\<^sub>v
                          { p10_post_noframe t s a list st}"
  apply (rule_tac P = "p9_pre t s a list st" and Q = "p10_post t s a list st" in rule_conseq)
    apply (rule_tac Q = "p9_post t s a list st" in rule_seq, simp add: p9_pre_def p9_post_def)
     apply (rule rule_frame, rule rule_frame1, rule thread_node_readnext, simp add: Thread_Local_def)
        apply (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_stack fvA_inv_readyq fvA_thread_wait_sl stack_node_def)
       apply (simp add: Thread_Local_def, simp add: Thread_Local_def, simp add: disjoint_def Thread_Local_def)
    apply (rule_tac Pa = "p10_pre t s a list st" and Qa = "p10_post t s a list st" in safe_assn_equiv)
      apply (simp add: p9_post_equiv, simp add: assn_equiv_reflex)
    apply (simp add: p10_pre_def p10_post_def, intro rule_frame, rule stack_node_write_wait_with_var)
      apply (simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_stack fvA_inv_readyq Thread_Local_def)
     apply (simp add: fvA_thread_node fvA_thread_wait_sl, simp add: fvA_thread_wait_sl)
  by (simp add: p9_pre_implies, simp add: p10_post_implies)

definition p9_frame :: " nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p9_frame s st = (([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** buf (stack_base st) (stack_top st) (stack_buf st) 
        \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq st) \<and>\<^sub>S\<^sub>L (inv_stack_pt st))"

definition p13_pre_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p13_pre_noframe t a st = (thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v 
  =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma p9_pre_frame_implies_aux : "P1 ** P2 ** (P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                            P2 ** P3 ** (P1 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P3 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P2 ** P3 ** (P1 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj) apply (meson Astar_assoc_equiv assn_equiv_symmetry 
   assn_equiv_trans stack_node_equiv1_aux stack_node_equiv3_aux)
   apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by blast

lemma p9_pre_frame_implies : "stack_tcbs st = a # list \<Longrightarrow> (p1_post t ** (p7_post_noframe t s st ** p4_frame st) 
  \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<sqsubseteq> p9_pre_noframe t s a list st ** p9_frame s st"
  apply (rule_tac Q = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** p4_frame st" in implies_trans)
   apply (simp add: p1_post_def p7_post_noframe_def implies_def) apply auto[1]
  apply (rule equiv_implies, simp add: p4_frame_def p9_pre_noframe_def p9_frame_def)
  by (simp add: inv_stack_buf_waitq_def inv_stack_pt_def p9_pre_frame_implies_aux)

lemma p10_post_frame_equiv_aux : "P1 ** P2 ** P3 ** (P4 ** P5 \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                                  P3 ** (P4 ** (P1 ** P2 ** P5 \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L))"
  apply (rule_tac Q = "P1 ** P2 ** P3 ** (P4 ** P5) \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P3 ** (P4 **(P1 ** P2 ** P5)) \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj, rule_tac Q = "P3 ** (P1 ** P2 ** (P4 ** P5))" in assn_equiv_trans)
     apply (simp add: stack_node_equiv3_aux, rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  using Astar_assoc_equiv assn_equiv_symmetry assn_equiv_trans stack_node_equiv3_aux apply blast
  apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by blast

lemma p10_post_frame_equiv : "\<lbrakk> stack_next st \<noteq> stack_top st; stack_base st = stack_next st; 
        stack_pt st; stack_wait st \<noteq> NULL\<rbrakk> \<Longrightarrow> p10_post_noframe t s a list st ** p9_frame s st \<equiv>\<^sub>S\<^sub>L 
        p13_pre_noframe t a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)"
  apply (simp add: inv_stack1_def p10_post_noframe_def p9_frame_def p13_pre_noframe_def)
  apply (rule_tac Q = "(thread_node (stack_wait st) a \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** (([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s (st :=\<^sub>w\<^sub>a thd_next a) ** is_waitq (thd_next a) list ** buf 
  (stack_base st) (stack_top st) (stack_buf st) \<and>\<^sub>S\<^sub>L  inv_stack_buf_waitq st \<and>\<^sub>S\<^sub>L inv_stack_pt st))" 
  in assn_equiv_trans, simp add: inv_stack_buf_waitq_def inv_stack_pt_def p10_post_frame_equiv_aux)
  apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (simp add: is_stack_def, rule assn_equiv_cong_conj, intro assn_equiv_cong_star)
  by (simp_all add: upstack_wait_def upstack_tcbs_def stack_base_def stack_next_def stack_top_def
      stack_buf_def stack_tcbs_def stack_wait_def stack_node_def inv_stack_buf_waitq_def 
      stack_buf_waitq_def inv_stack_pt_def stack_pt_def assn_equiv_reflex) 

lemma safe_p910 : "\<lbrakk>fvAs \<Gamma> = {}; stack_next st \<noteq> stack_top st; stack_base st = stack_next st; 
                    stack_pt st; stack_wait st \<noteq> NULL; stack_tcbs st = a # list\<rbrakk> \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
{(p1_post t ** (p7_post_noframe t s st ** p4_frame st) \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L)}
                          t\<diamondop>WAITQ :=\<^sub>C \<lbrakk>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk>;;
                          \<lbrakk>[t\<diamondop>ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [t\<diamondop>WAITQ]\<^sub>v  
{p13_pre_noframe t a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)}"
  apply (rule_tac P = "p9_pre_noframe t s a list st ** p9_frame s st" and Q = "p10_post_noframe t s 
  a list st ** p9_frame s st" in rule_conseq)
    apply (rule rule_frame, rule safe_p910_noframe, simp_all)
    apply (simp add: p9_frame_def fvA_buf inv_stack_pt_def inv_stack_buf_waitq_def disjoint_def Thread_Local_def)
  by (simp add: p9_pre_frame_implies, rule equiv_implies, rule p10_post_frame_equiv, simp_all)

definition p11_pre_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p11_pre_noframe t s st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (buf (stack_base st) 
  (stack_top st) (stack_buf st) \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition p12_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p12_post_noframe t s data st = stack_node s (st:=\<^sub>n\<^sub>e (stack_next st + 1)) ** buf (stack_base st) 
  (stack_top st) ((stack_buf st)[(stack_next st - stack_base st) := data])"

definition p11_post :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p11_post t s data st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (buf (stack_base st) 
  (stack_top st) ((stack_buf st)[(stack_next st -stack_base st) := data]) \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition p12_pre :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p12_pre t s data st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** buf (stack_base st) (stack_top st) ((stack_buf st)[(stack_next st -stack_base st) := data])"

lemma p12_pre_equiv : " p12_pre t s data st \<equiv>\<^sub>S\<^sub>L p11_post t s data st"
  apply (simp add: assn_equiv_def p12_pre_def p11_post_def) by auto

definition p12_post :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p12_post t s data st = (stack_node s (st:=\<^sub>n\<^sub>e (stack_next st + 1)) \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L 
  \<and>\<^sub>S\<^sub>L \<langle>[t \<diamondop> NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** buf (stack_base st) (stack_top st) ((stack_buf st)
  [(stack_next st -stack_base st) := data])"

lemma p12_post_implies : "p12_post t s data st \<sqsubseteq> p12_post_noframe t s data st"
  apply (simp add: p12_post_def p12_post_noframe_def implies_def) by auto

lemma safe_p1112_noframe : "\<lbrakk>fvAs \<Gamma> = {}; stack_pt st; stack_next st \<noteq> stack_top st; t \<noteq> NULL\<rbrakk> \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          { p11_pre_noframe t s st}
                      (t \<^enum> \<lbrakk>[t \<diamondop> NEXT]\<^sub>v\<rbrakk> :=\<^sub>C [data]\<^sub>n) ;;
                      (t \<^enum>  \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk> :=\<^sub>C [t \<diamondop> NEXT]\<^sub>v +\<^sub>e [1]\<^sub>n)
                          { p12_post_noframe t s data st}"
  apply (rule_tac Q = "p11_post t s data st" in rule_seq, simp add: p11_pre_noframe_def p11_post_def)
   apply (rule rule_frame1, rule rule_stm_stack', simp, simp)
        apply (simp add: fvA_buf Thread_Local_def, simp add: fvA_buf Thread_Local_def, simp)
  apply (simp add: fvA_buf, simp add: Thread_Local_def)
    apply (rule update_buf_with_var, simp add: stack_pt_def, simp add: stack_node_def)
  apply (simp add: stm_def disjoint_def Thread_Local_def stack_node_def)
  apply (rule_tac P = "p12_pre t s data st" and Q = "p12_post t s data st" in rule_conseq)
    apply (simp only: p12_post_def p12_pre_def, rule rule_frame, rule rule_stm_stack', simp, simp)
       apply (simp add: stack_node_def Thread_Local_def, simp)
  apply (simp add: stack_node_def Thread_Local_def)
     apply (rule stack_node_write_next_add1, simp add: Thread_Local_def)
      apply (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_buf fvA_inv_stack Thread_Local_def)
  by (simp add: assn_equiv_symmetry equiv_implies p12_pre_equiv, simp add: p12_post_implies)

definition p11_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p11_frame s st = ((([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** is_waitq (stack_wait st) (stack_tcbs st))
   \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq st) \<and>\<^sub>S\<^sub>L (inv_stack_pt st))"

lemma p11_pre_frame_implies_aux : "P1 ** (P2 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L) ** (P5 ** P6  \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P8\<rangle>\<^sub>S\<^sub>L)
                              \<equiv>\<^sub>S\<^sub>L (P2 \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L) ** (P6 \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L) ** (P1 ** P5  \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P8\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P5 ** P6) \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P8\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P2 ** P6 ** (P1 ** P5) \<and>\<^sub>S\<^sub>L \<langle>P3\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P4\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P8\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj) apply (metis Astar_assoc_equiv Astar_commute_equiv assn_equiv_trans 
   stack_node_equiv1_aux stack_node_equiv2_aux)
   apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by blast

lemma p11_pre_frame_implies : "(p7_post_noframe t s st ** p4_frame st \<and>\<^sub>S\<^sub>L\<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v 
                        =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<sqsubseteq> p11_pre_noframe t s st ** p11_frame s st"
  apply (rule_tac Q = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L
      \<langle>[t\<diamondop>NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)) ** p4_frame st" in implies_trans)
   apply (simp add: p7_post_noframe_def implies_def) apply auto[1]
  apply (rule equiv_implies, simp add: p4_frame_def p11_pre_noframe_def p11_frame_def)
  by (simp add: inv_stack_buf_waitq_def inv_stack_pt_def p11_pre_frame_implies_aux)

lemma p12_post_equiv_aux : "P1 ** P2 ** (P3 ** P4  \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                           P3 ** (P1 ** P4 ** P2  \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P3 ** P4 ) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply blast 
  apply (rule_tac Q = "P3 ** (P1 ** P4 ** P2) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj) 
  apply (meson Astar_assoc_equiv Astar_commute_equiv assn_equiv_trans stack_node_equiv2_aux)
  apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by blast

lemma p12_post_frame_equiv : "\<lbrakk>stack_next st \<noteq> stack_top st; stack_pt st; stack_wait st = NULL\<rbrakk> \<Longrightarrow>
       p12_post_noframe t s data st ** p11_frame s st \<equiv>\<^sub>S\<^sub>L inv_stack1 s 
      (st :=\<^sub>n\<^sub>e (stack_next st + 1) :=\<^sub>b\<^sub>f ((stack_buf st)[(stack_next st -stack_base st) := data]))"
  apply (simp add: inv_stack1_def p12_post_noframe_def p11_frame_def)
  apply (rule_tac Q = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** (stack_node s (st :=\<^sub>n\<^sub>e stack_next st + 1) ** is_waitq 
  (stack_wait st) (stack_tcbs st) **  buf (stack_base st) (stack_top st) ((stack_buf st)[stack_next st - stack_base st := data]) 
  \<and>\<^sub>S\<^sub>L inv_stack_buf_waitq st \<and>\<^sub>S\<^sub>L inv_stack_pt st)" in assn_equiv_trans)
   apply (simp add: inv_stack_buf_waitq_def inv_stack_pt_def p12_post_equiv_aux)
  apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex, simp add: is_stack_def)
  apply (rule assn_equiv_cong_conj, intro assn_equiv_cong_star)
  by (simp_all add: upstack_next_def upstack_buf_def stack_base_def stack_next_def stack_top_def
      stack_buf_def stack_tcbs_def stack_wait_def stack_node_def inv_stack_buf_waitq_def 
      stack_buf_waitq_def inv_stack_pt_def stack_pt_def assn_equiv_reflex)

thm p11_pre_frame_implies
lemma safe_p1112 : "\<lbrakk>fvAs \<Gamma> = {}; stack_pt st; stack_next st \<noteq> stack_top st; stack_wait st = NULL; 
                     t \<noteq> NULL\<rbrakk> \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
           {  p7_post_noframe t s st ** p4_frame st \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L }
                (t \<^enum> \<lbrakk>[t \<diamondop> NEXT]\<^sub>v\<rbrakk> :=\<^sub>C [data]\<^sub>n) ;;
                (t \<^enum>  \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk> :=\<^sub>C [t \<diamondop> NEXT]\<^sub>v +\<^sub>e [1]\<^sub>n)
                 { inv_stack }"
  apply (rule_tac P = " p11_pre_noframe t s st ** p11_frame s st" and Q = "p12_post_noframe t s data st 
  ** p11_frame s st" in rule_conseq, rule rule_frame, rule safe_p1112_noframe, simp_all)
    apply (simp add: p11_frame_def stm_def disjoint_def fvA_is_waitq inv_stack_pt_def)
    apply (simp add: inv_stack_buf_waitq_def, simp add: Thread_Local_def)
  apply (rule p11_pre_frame_implies)
  apply (rule_tac Q = "inv_stack1 s (st :=\<^sub>n\<^sub>e (stack_next st + 1) :=\<^sub>b\<^sub>f ((stack_buf st)[(stack_next st 
  -stack_base st) := data]))" in implies_trans)
   apply (rule equiv_implies, rule p12_post_frame_equiv, simp_all)
  by (simp add: inv_stack_implies)

definition p14_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p14_post_noframe t d a st = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d) 
  \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition p13_post :: "nat  \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p13_post t a st = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY) \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma safe_p1314_noframe : "\<lbrakk>fvAs \<Gamma> = {}; stack_pt st; stack_next st \<noteq> stack_top st\<rbrakk> \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          {p13_pre_noframe t a st}
              \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [READY]\<^sub>n ;;
              \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tdata\<rbrakk> :=\<^sub>C [d]\<^sub>n
                          { p14_post_noframe t d a st}"
  apply (rule_tac Q = "p13_post t a st" in rule_seq, simp only: p13_pre_noframe_def p13_post_def)
   apply (rule thread_node_write_st', simp only: p13_post_def p14_post_noframe_def)
  by (rule thread_node_write_data)

lemma safe_p1314 : "\<lbrakk>fvAs \<Gamma> = {}; stack_pt st; stack_next st \<noteq> stack_top st\<rbrakk> \<Longrightarrow>
                 \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
   {p13_pre_noframe t a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list) \<and>\<^sub>S\<^sub>L 
            \<langle>\<not>\<^sub>b [t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
              \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [READY]\<^sub>n ;;
              \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tdata\<rbrakk> :=\<^sub>C [d]\<^sub>n
                { p14_post_noframe t d a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)}"
  apply (rule_tac P = "p13_pre_noframe t a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)" and 
  Q = "p14_post_noframe t d a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)" in rule_conseq)
    apply (rule rule_frame, rule safe_p1314_noframe, simp_all)
  by (simp_all add: implies_def)

definition p15_post :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "p15_post t d a st r xs = p14_post_noframe t d a st ** (([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** is_readyq r xs)"

definition p16_pre :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "p16_pre t d a st r xs = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d) \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (([A_Readyq]\<^sub>v
   \<longmapsto> [r]\<^sub>n) ** is_readyq r xs)"

lemma p15_post_equiv : "p16_pre t d a st r xs  \<equiv>\<^sub>S\<^sub>L p15_post t d a st r xs"
  apply (simp add: p16_pre_def p15_post_def p14_post_noframe_def assn_equiv_def) by auto

definition p16_post :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "p16_post t d a st r xs = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r) \<and>\<^sub>S\<^sub>L 
  \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_READY]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (([A_Readyq]\<^sub>v
   \<longmapsto> [r]\<^sub>n) ** is_readyq r xs)"

definition p17_pre :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "p17_pre t d a st r xs = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r)) ** (
  ([A_Readyq]\<^sub>v  \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** is_readyq r xs)"

lemma p16_post_implies : " p16_post t d a st r xs \<sqsubseteq> p17_pre t d a st r xs"
  apply (simp add: p16_post_def p17_pre_def implies_def) by blast

definition p17_post :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "p17_post t d a st r xs = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r)) ** (
  ([A_Readyq]\<^sub>v  \<longmapsto> [stack_wait st]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** is_readyq r xs)"

definition p18_pre :: "nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> stack_mem \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "p18_pre t d a st r xs = (thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r)) ** (
  ([A_Readyq]\<^sub>v  \<longmapsto> [stack_wait st]\<^sub>n) ** is_readyq r xs)"

lemma p17_post_implies : "p17_post t d a st r xs \<sqsubseteq> inv_readyq1 (stack_wait st) 
                                                (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r # xs)"
    apply (rule_tac Q = "([A_Readyq]\<^sub>v \<longmapsto> [stack_wait st]\<^sub>n) ** (thread_node (stack_wait st) 
    (a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r) ** is_readyq r xs)" in implies_trans, simp add: p17_post_def)
  apply (rule_tac Q = "thread_node (stack_wait st) (a :=\<^sub>s\<^sub>t Suc K_NO_WAIT :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r) **
    (([A_Readyq]\<^sub>v \<longmapsto> [stack_wait st]\<^sub>n) ** is_readyq r xs)" in implies_trans)
    apply (simp add: implies_def) apply auto[1]
   apply (meson Astar_assoc_equiv Astar_assoc_equiv2 Astar_commute_equiv assn_equiv_trans equiv_implies)
  apply (rule equiv_implies, simp add: inv_readyq1_def)
  apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (rule thread_ready_sl_insert', simp_all add: uptcb_data_def uptcb_next_def uptcb_state_def)
  by (simp add: thd_st_def, simp add: thd_next_def)

lemma safe_p1517_noframe : "fvAs \<Gamma> = {} \<Longrightarrow> 
                \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                  {p14_post_noframe t d a st ** inv_readyq1 r xs}
                  t\<diamondop>FIRST_READY :=\<^sub>C \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk>;; 
                  \<lbrakk>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [t\<diamondop>FIRST_READY]\<^sub>v;;
                  \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> :=\<^sub>C [t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v
            {inv_readyq1 (stack_wait st) ((a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r) # xs)}"
  apply (rule_tac Q = "p16_post t d a st r xs" in rule_seq)
    apply (rule_tac Q = "p15_post t d a st r xs" in rule_seq, simp add: p15_post_def)
     apply (rule rule_frame1, simp add: inv_readyq1_def, rule rule_frame)
  apply (rule_tac P = "[A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n" and Q = "[A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FIRST_READY]\<^sub>v =\<^sub>b 
  [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_conseq, rule rule_read, simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_stack fvA_inv_stack)
         apply (simp add: fvA_inv_readyq Thread_Local_def, simp add: implies_def, simp add: implies_def)
  apply (simp add: disjoint_def fvA_is_readyq, simp add: p14_post_noframe_def fvA_thread_node)
     apply (simp add: disjoint_def Thread_Local_def)
    apply (rule_tac Pa = "p16_pre t d a st r xs" and Qa = "p16_post t d a st r xs" in safe_assn_equiv)
      apply (simp add: p15_post_equiv, simp add: assn_equiv_reflex)
    apply (simp add: p16_pre_def p16_post_def, rule rule_frame, rule thread_node_write_next_fromvar)
    apply (simp, rule_tac P = "p17_pre t d a st r xs" and Q = "p17_post t d a st r xs" in rule_conseq)
     apply (simp add: p17_pre_def p17_post_def, rule rule_frame1, rule rule_frame, rule rule_write_var2)
     apply (simp add: fvA_is_readyq, simp, simp add: p16_post_implies)
  using p17_post_implies by auto

lemma safe_p1517 : "fvAs \<Gamma> = {} \<Longrightarrow> 
                \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
      {p14_post_noframe t d a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list) ** inv_readyq1 r xs}
                  t\<diamondop>FIRST_READY :=\<^sub>C \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk>;; 
                  \<lbrakk>[t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [t\<diamondop>FIRST_READY]\<^sub>v;;
                  \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> :=\<^sub>C [t\<diamondop>FIRST_PENDING_THREAD]\<^sub>v
                  {inv_stack ** inv_readyq }"
  apply (rule_tac P = "inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list) ** (p14_post_noframe t d a st **
  inv_readyq1 r xs)" and Q = "inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list) ** inv_readyq1 (stack_wait st) 
  ((a :=\<^sub>s\<^sub>t READY :=\<^sub>d\<^sub>t d :=\<^sub>n\<^sub>x r) # xs)" in rule_conseq)
    apply (rule rule_frame1, rule safe_p1517_noframe, simp, simp add: inv_stack1_def fvA_is_stack)
    apply (simp add: disjoint_def Thread_Local_def) apply (rule equiv_implies) 
  using Astar_assoc_equiv2 Astar_commute_equiv assn_equiv_trans apply blast
  by (simp add: implies_star inv_readyq_implies inv_stack_implies)

lemma rule_inv_stack : "\<forall>s st. \<Gamma> \<turnstile> {P ** inv_stack1 s st} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {P ** inv_stack} C {Q}"
  apply (simp add: CSL_def inv_stack_def) by blast

lemma rule_inv_readyq : "\<forall>r xs. \<Gamma> \<turnstile> {P ** inv_readyq1 r xs} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {P ** inv_readyq} C {Q}"
  apply (simp add: CSL_def inv_readyq_def) by blast


lemma safe_push : "fvAs \<Gamma> = {} \<Longrightarrow> 
                   \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                    {Aemp \<and>\<^sub>S\<^sub>L \<langle>[t \<noteq> NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L} stack_push t d { Aemp}"
  apply (simp add: stack_push_def, case_tac t, simp add: CSL_def) using stm_def apply auto[1]
  apply (rule_tac Pa = "Aemp" and Qa = "Aemp" in safe_assn_equiv)
  apply (simp add: assn_equiv_def, simp add: assn_equiv_def)
  apply (rule_tac Q = "Aemp" in rule_seq)
   apply (rule_tac Q = "p1_post t" in rule_seq, simp add: p1_post_def)
    apply (rule rule_stm_stack', simp_all, simp add: disjoint_def Thread_Local_def)
    apply (rule_tac Pa = "Aemp" and Qa = "(Aemp  \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>END]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"
    in safe_assn_equiv, simp add: assn_equiv_def, simp add: assn_equiv_def) apply auto[1]
     apply (simp, rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
  apply (simp add: Thread_Local_def, simp add: Thread_Local_def)
   apply (rule rule_with_true, simp, rule rule_inv_stack, intro allI)
   apply (rule_tac Q = "p1_post t ** (p4_post_noframe t s st ** p4_frame st)" in rule_seq, simp add: safe_p24)
   apply (rule rule_if, rule_tac P = "inv_stack1 s st" and Q = "inv_stack1 s st" in rule_conseq)
  using safe_p56 apply auto[1] apply (simp add: p5_pre_implies) 
  using implies_def inv_stack_implies apply auto[1]
   apply (case_tac "stack_next st = stack_top st", simp add: CSL_def p4_post_noframe_def)
    using stm_def user_cmd.simps(9) apply auto[1]
     apply (case_tac "\<not> stack_pt st", simp add: CSL_def p4_frame_def inv_stack_pt_def)
    using stm_def user_cmd.simps(9) apply auto[1]
   apply (rule_tac P = "p1_post t ** (p7_pre_noframe t s st ** p4_frame st)" and Q = "inv_stack" in rule_conseq)
(* stack_wait st = NULL *)
  apply (case_tac "stack_wait st")
   apply (rule_tac Q = "p7_post_noframe t s st ** p4_frame st" in rule_seq)
         apply (rule rule_stm_stack', simp_all, simp add: disjoint_def Thread_Local_def)
            apply (simp add: p4_frame_def inv_stack_pt_def p1_post_def p7_pre_noframe_def)
            apply (simp add: stack_node_def fvA_is_waitq fvA_buf inv_stack_buf_waitq_def Thread_Local_def)
           apply (simp add: p4_frame_def inv_stack_pt_def p1_post_def p7_pre_noframe_def)
           apply (simp add: stack_node_def fvA_is_waitq fvA_buf inv_stack_buf_waitq_def Thread_Local_def)
    apply (rule_tac Q = "p1_post t ** (p7_post_noframe t s st ** p4_frame st)" in rule_seq)
     apply (simp, rule rule_frame1, rule rule_frame, simp add: safe_p7_noframe)
      apply (simp add: p4_frame_def fvA_buf fvA_is_waitq inv_stack_pt_def inv_stack_buf_waitq_def)
     apply (simp add: p1_post_def, simp add: disjoint_def Thread_Local_def)
    apply (rule rule_if, rule_tac P = "p7_post_noframe t s st ** p4_frame st" and Q = "p7_post_noframe 
    t s st ** p4_frame st" in rule_conseq, simp add: rule_skip, simp add: p1_post_def, simp_all add: implies_def)
         apply (simp add: p7_post_noframe_def CSL_def) apply auto[1]
    apply (simp add: Thread_Local_def)
     apply (rule rule_if, drule_tac t =t and s = s and data = d and st = st in safe_p1112, simp_all)
     apply (simp add: p7_post_noframe_def CSL_def) using stm_def apply auto[1]
(* stack_wait st \<noteq>  NULL *)
    apply (case_tac "stack_tcbs st", simp add: p4_frame_def is_waitq_def thread_sl_def CSL_def)
    using stm_def apply auto[1]
    apply (case_tac "stack_base st \<noteq> stack_next st", simp add: p4_frame_def inv_stack_buf_waitq_def
    stack_buf_waitq_def CSL_def) using stm_def apply auto[1]
    apply (rule_tac Q = "p13_pre_noframe t a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)" in rule_seq)
       apply (rule rule_stm_stack', simp_all)
           apply (simp add: disjoint_def Thread_Local_def)
          apply (simp add: p4_frame_def inv_stack_pt_def p1_post_def p7_pre_noframe_def)
            apply (simp add: stack_node_def fvA_is_waitq fvA_buf inv_stack_buf_waitq_def Thread_Local_def)
           apply (simp add: p4_frame_def inv_stack_pt_def p1_post_def p7_pre_noframe_def)
           apply (simp add: stack_node_def fvA_is_waitq fvA_buf inv_stack_buf_waitq_def Thread_Local_def)
     apply (rule_tac Q = "p1_post t ** (p7_post_noframe t s st ** p4_frame st)" in rule_seq, simp)
      apply (rule rule_frame1, rule rule_frame, simp add: safe_p7_noframe)
       apply (simp add: p4_frame_def fvA_buf fvA_is_waitq inv_stack_pt_def inv_stack_buf_waitq_def)
      apply (simp add: p1_post_def, simp add: disjoint_def Thread_Local_def)
        apply (rule rule_if, simp add: p7_post_noframe_def CSL_def) apply auto[1]
    using safe_p910 apply auto[1] apply (simp add: Thread_Local_def)
     apply (rule rule_if)
     apply (simp add: p13_pre_noframe_def CSL_def) using stm_def apply auto[1]
      apply (rule rule_stm_stack', simp_all)
          apply (simp add: disjoint_def Thread_Local_def)
         apply (simp add: p13_pre_noframe_def inv_stack1_def fvA_is_stack Thread_Local_def)
    apply (simp add: p13_pre_noframe_def inv_stack1_def fvA_is_stack Thread_Local_def)
    apply (rule_tac Q = "p14_post_noframe t d a st ** inv_stack1 s (st :=\<^sub>w\<^sub>a thd_next a :=\<^sub>t\<^sub>c list)" in
    rule_seq) using  safe_p1314 apply auto[1]
       apply (rule rule_with_true, simp, rule rule_inv_readyq, intro allI, simp add: safe_p1517)
    apply (simp add: Thread_Local_def)
     apply (simp add: p4_post_noframe_def p7_pre_noframe_def implies_def) apply blast
   apply (rule rule_if, rule_tac P = Aemp and Q = "Aemp \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>RET]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L"  in rule_conseq)
       apply (rule rule_stm_stack', simp_all)
    apply (simp add: disjoint_def Thread_Local_def)
        apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
    apply (simp add: Thread_Local_def, simp add: Thread_Local_def)
     apply (simp_all add: implies_def) apply (rule_tac P = Aemp and Q = Aemp in rule_conseq)
      apply (simp add: rule_skip, simp_all add: implies_def)
    done

end