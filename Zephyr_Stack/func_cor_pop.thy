theory func_cor_pop
  imports Stack_Aux
begin

definition p1_post :: "nat \<Rightarrow> assn"
  where "p1_post t = (\<langle>[END]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"

definition p4_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p4_post_noframe t s st = ([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L
      \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[ BASE]\<^sub>v =\<^sub>b [stack_base st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"
  
lemma safe_p24_noframe : "fvAs \<Gamma> = {} \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          {([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** stack_node s st}
                          (t \<^enum> ( ADDR) :=\<^sub>C \<lbrakk>[A_Stack]\<^sub>v\<rbrakk>) ;;
                          (t \<^enum> ( NEXT) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
                          (t \<^enum> ( BASE) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>sbase\<rbrakk>) 
                          {p4_post_noframe t s st}"
  apply (rule_tac Q = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L
      \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in rule_seq)
   apply (rule_tac Q = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in rule_seq)
  apply (rule_tac Pa = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** stack_node s st" and Qa = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n \<and>\<^sub>S\<^sub>L 
  \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node s st" in safe_assn_equiv, simp add: assn_equiv_reflex)
     apply (simp add: assn_equiv_def) apply auto[1]
    apply (rule rule_frame, rule rule_stm_stack', simp_all)
  apply (simp add: disjoint_def)
     apply (rule rule_read,  simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_inv_stack)
    apply (simp add: stack_node_def) apply (rule rule_frame1)
    apply (rule rule_stm_stack' , simp_all)
        apply (simp add: disjoint_def)
        apply (simp add: stack_node_def, simp add: stack_node_def)
    apply (rule stack_node_read_next)
     apply (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_inv_stack)
    apply (simp add: disjoint_def stm_def)
  apply (simp add: p4_post_noframe_def, rule rule_frame1, rule rule_stm_stack', simp_all)
       apply (simp add: disjoint_def)
      apply (simp add: stack_node_def , simp add: stack_node_def)
    apply (rule stack_node_read_base1, simp, simp)
     apply (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_inv_stack disjoint_def stm_def )
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
                          (t \<^enum> ( ADDR) :=\<^sub>C \<lbrakk>[A_Stack]\<^sub>v\<rbrakk>) ;;
                          (t \<^enum> ( NEXT) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
                          (t \<^enum> ( BASE) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>sbase\<rbrakk>) 
                          {p1_post t ** (p4_post_noframe t s st ** p4_frame st)}"
  apply (rule rule_frame1, rule_tac Pa = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** stack_node s st ** p4_frame st"
  and Qa = "p4_post_noframe t s st ** p4_frame st" in safe_assn_equiv)
     apply (simp add: assn_equiv_symmetry safe_p24_pre_equiv, simp add: assn_equiv_reflex)
   apply (rule rule_frame, simp add: safe_p24_noframe, simp_all add: disjoint_def)
   apply (simp add: p4_frame_def fvA_is_waitq fvA_buf inv_stack_pt_def inv_stack_buf_waitq_def)
  by (simp add: p1_post_def stm_def )   

definition p5_pre_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p5_pre_noframe t s st = (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b 
  [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (buf (stack_base st) (stack_top st) (stack_buf st))"

definition p5_cond :: "stack_mem \<Rightarrow> bool"
  where "p5_cond st = ((stack_next st > stack_base st) \<and> (stack_next st \<le> stack_top st))"

definition p5_post :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p5_post t s st = (stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L 
  \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b  [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (buf (stack_base st) (stack_top st) (stack_buf st))" 

definition p6_pre :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p6_pre t s st = (stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) 
  \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (buf (stack_base st) (stack_top st) (stack_buf st))"

lemma p5_post_implies : "p5_post t s st \<sqsubseteq> p6_pre t s st"
  apply (simp add: p5_post_def p6_pre_def implies_def) by blast

definition p6_post :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p6_post t s st = (stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L
  \<langle>[ NEXT]\<^sub>v =\<^sub>b [stack_next (st:=\<^sub>n\<^sub>e (stack_next st - 1))]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** 
  (buf (stack_base st) (stack_top st) (stack_buf st))"

definition p7_pre' :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p7_pre' t s st = (stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b 
  [stack_next st - 1]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (buf (stack_base st) (stack_top st) (stack_buf st))"

definition p7_pre :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p7_pre t s st = stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) ** (buf (stack_base st) 
  (stack_top st) (stack_buf st) \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b [stack_next st - 1]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma p6_post_implies : "p6_post t s st \<sqsubseteq> p7_pre t s st"
  apply (rule_tac Q = "p7_pre' t s st" in implies_trans)
   apply (simp add: p6_post_def p7_pre'_def upstack_next_def stack_next_def implies_def) apply auto[1]
  apply (simp add: p7_pre'_def p7_pre_def implies_def) by auto

definition p7_post :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p7_post t s st = stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) ** (buf (stack_base st) 
  (stack_top st) (stack_buf st) \<and>\<^sub>S\<^sub>L \<langle>[ NEXT]\<^sub>v =\<^sub>b [stack_next st - 1]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[ DATA]\<^sub>v =\<^sub>b [(stack_buf st) ! (stack_next st - 1 - stack_base st)]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition p8_pre :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p8_pre t s st = stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) ** (buf (stack_base st) 
  (stack_top st) (stack_buf st)  \<and>\<^sub>S\<^sub>L \<langle>[ DATA]\<^sub>v =\<^sub>b [(stack_buf st) ! (stack_next st 
  - 1 - stack_base st)]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

lemma p7_post_implies : "p7_post t s st \<sqsubseteq> p8_pre t s st"
  apply (simp add: p7_post_def p8_pre_def implies_def) by blast

definition p8_post :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p8_post t s st = (p8_pre t s st \<and>\<^sub>S\<^sub>L \<langle>[( RET)]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition p9_post :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p9_post t s st = (p8_post t s st \<and>\<^sub>S\<^sub>L \<langle>[( END)]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition  p9_post_noframe :: "nat \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p9_post_noframe t s st = stack_node s (st:=\<^sub>n\<^sub>e (stack_next st - 1)) ** buf (stack_base st) 
  (stack_top st) (stack_buf st)"

lemma safe_p59_noframe : "fvAs \<Gamma> = {} \<Longrightarrow> p5_cond st \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          {p5_pre_noframe t s st}
                            (t \<^enum> \<lbrakk>([ ADDR]\<^sub>v\<Down>\<^sub>snext)\<rbrakk> :=\<^sub>C [ NEXT]\<^sub>v -\<^sub>e [1]\<^sub>n);;
                            (t \<^enum> ( NEXT) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
                            (t \<^enum> ( DATA) :=\<^sub>C \<lbrakk>[ NEXT]\<^sub>v\<rbrakk>) ;;
                            (t \<^enum> ( RET) :=\<^sub>C [0]\<^sub>n) ;;
                            (t \<^enum> ( END) :=\<^sub>C [1]\<^sub>n) 
                          {p9_post_noframe t s st}"
  apply (rule_tac Q = "p8_post t s st" in rule_seq)
  apply (rule_tac Q = "p7_post t s st" in rule_seq)
  apply (rule_tac Q = "p6_post t s st" in rule_seq)
     apply (rule_tac Q = "p5_post t s st" in rule_seq)
  apply (simp only: p5_pre_noframe_def p5_post_def, rule rule_frame)
       apply (rule rule_stm_stack', simp, simp, simp)
           apply (simp add: stack_node_def , simp add: )
         apply (simp add: stack_node_def )
       apply (rule stack_node_write_next_minus1, simp add: )
        apply (simp_all add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq fvA_buf fvA_inv_stack)
     apply (rule_tac P = "p6_pre t s st" and Q = "p6_post t s st" in rule_conseq)
  apply (simp only: p6_pre_def p6_post_def, rule rule_frame)
        apply (rule rule_stm_stack', simp_all)
            apply (simp add: disjoint_def )
           apply (simp add: stack_node_def , simp add: stack_node_def )
         apply (rule stack_node_read_next, simp add: )
         apply (simp_all add: fvA_Gamma2 fvA_buf fvA_inv_cur fvA_inv_readyq fvA_inv_stack)
      apply (simp add: p5_post_implies, simp add: implies_def)
    apply (rule_tac P = "p7_pre t s st" and Q = "p7_post t s st" in rule_conseq)
      apply (simp only: p7_pre_def p7_post_def, rule rule_frame1, rule rule_stm_stack', simp)
            apply (simp add: disjoint_def )
           apply (simp add: fvA_buf , simp)
  apply (simp add: fvA_buf )
        apply (rule read_buf_with_var, simp add: fvA_Gamma2 fvA_inv_readyq fvA_inv_cur fvA_inv_stack )
        apply (simp add: p5_cond_def) apply linarith 
        apply (simp add: )
      apply (simp add: stack_node_def, simp add: p6_post_implies, simp add: implies_def)
   apply (rule_tac P = "p8_pre t s st" and Q = "p8_post t s st" in rule_conseq)
     apply (rule rule_stm_stack', simp_all)
         apply (simp add: disjoint_def )
        apply (simp add: p8_pre_def fvA_buf stack_node_def )
  apply (simp add: p8_pre_def fvA_buf stack_node_def )
  apply (simp add: p8_post_def, rule rule_assign_num1)
      apply (simp add: fvA_Gamma2 fvA_inv_readyq fvA_inv_cur fvA_inv_stack p8_pre_def stack_node_def 
      fvA_buf)
    apply (simp add: p7_post_implies, simp add: implies_def)
  apply (rule rule_stm_stack', simp_all) 
      apply (simp add: disjoint_def )
     apply (simp add: p8_post_def p8_pre_def fvA_buf stack_node_def )
  apply (simp add: p8_post_def p8_pre_def fvA_buf stack_node_def )
  apply (rule_tac P = "p8_post t s st" and Q = "p9_post t s st" in rule_conseq)
  apply (simp add: p9_post_def, rule rule_assign_num1)
     apply (simp add: fvA_Gamma2 fvA_inv_readyq fvA_inv_cur fvA_inv_stack p8_post_def p8_pre_def 
      stack_node_def fvA_buf )
   apply (simp_all add: implies_def, simp add: p9_post_def p8_post_def p8_pre_def p9_post_noframe_def)
   apply blast 
  done

definition p5_cond_if :: "stack_mem \<Rightarrow> bool"
  where "p5_cond_if st = ((stack_next st > stack_base st) \<and> (stack_next st \<le> stack_top st) 
                          \<and> (stack_base st < stack_top st) \<and> stack_wait st = K_NO_WAIT \<and> stack_tcbs st = [])"

definition p5_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p5_frame s st = ((([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** is_waitq (stack_wait st) (stack_tcbs st))
   \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq st) \<and>\<^sub>S\<^sub>L (inv_stack_pt st))"

lemma p9_post_equiv_aux : "P1 ** P2 ** (P3 ** P4  \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                           P3 ** (P1 ** P4 ** P2  \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P3 ** P4 ) \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply blast 
  apply (rule_tac Q = "P3 ** (P1 ** P4 ** P2) \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P7\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj) 
  apply (meson Astar_assoc_equiv Astar_commute_equiv assn_equiv_trans stack_node_equiv2_aux)
  apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def) by blast

lemma p9_post_equiv : "p5_cond_if st \<Longrightarrow> p9_post_noframe t s st ** p5_frame s st  \<equiv>\<^sub>S\<^sub>L 
                      inv_stack1 s (st :=\<^sub>n\<^sub>e stack_next st - 1)"
  apply (simp add: p9_post_noframe_def p5_frame_def inv_stack1_def)
  apply (rule_tac Q = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** (stack_node s (st :=\<^sub>n\<^sub>e stack_next st - 1) ** is_waitq 
  (stack_wait st) (stack_tcbs st) ** buf (stack_base st) (stack_top st) (stack_buf st)   \<and>\<^sub>S\<^sub>L 
  inv_stack_buf_waitq st \<and>\<^sub>S\<^sub>L inv_stack_pt st)" in assn_equiv_trans)
   apply (simp add: p9_post_equiv_aux inv_stack_buf_waitq_def inv_stack_pt_def) 
  apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (simp add: is_stack_def, rule assn_equiv_cong_conj, intro assn_equiv_cong_star)
     apply (simp add: assn_equiv_reflex, simp_all add: upstack_next_def)
    apply (simp add: stack_wait_def stack_tcbs_def assn_equiv_reflex)
   apply (simp add: stack_base_def stack_top_def stack_buf_def assn_equiv_reflex)
  apply (simp add: inv_stack_buf_waitq_def stack_buf_waitq_def inv_stack_pt_def stack_pt_def)
  apply (simp add: stack_base_def stack_next_def stack_top_def stack_wait_def p5_cond_if_def)
  apply (simp add: assn_equiv_def) by linarith

lemma p5_pre_implies_aux : "P1 ** P2 ** (P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                            P2 ** P4 ** (P1 ** P3 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P3 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply blast
  apply (rule_tac Q = "P2 ** P4 ** (P1 ** P3) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj) apply (metis Astar_assoc_equiv Astar_commute_equiv assn_equiv_trans
   stack_node_equiv1_aux stack_node_equiv2_aux, simp add: assn_equiv_reflex)
  apply (simp add: assn_equiv_def) by blast

lemma p5_pre_implies : " (p4_post_noframe t s st \<and>\<^sub>S\<^sub>L \<langle>[NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) ** p4_frame st 
                          \<sqsubseteq> p5_pre_noframe t s st ** p5_frame s st"
  apply (rule_tac Q = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** (stack_node s st \<and>\<^sub>S\<^sub>L  \<langle>[ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L 
  \<and>\<^sub>S\<^sub>L \<langle>[NEXT]\<^sub>v =\<^sub>b [stack_next st]\<^sub>n\<rangle>\<^sub>S\<^sub>L ) ** p4_frame st" in implies_trans)
   apply (simp add: p4_post_noframe_def implies_def) apply auto
  apply (rule equiv_implies, simp add: p4_frame_def p5_pre_noframe_def p5_frame_def)
  by (simp add: inv_stack_buf_waitq_def inv_stack_pt_def p5_pre_implies_aux)

lemma safe_p59 : "fvAs \<Gamma> = {} \<Longrightarrow> p5_cond_if st \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                          {p5_pre_noframe t s st ** p5_frame s st}
                            (t \<^enum> \<lbrakk>([ ADDR]\<^sub>v\<Down>\<^sub>snext)\<rbrakk> :=\<^sub>C [ NEXT]\<^sub>v -\<^sub>e [1]\<^sub>n);;
                            (t \<^enum> ( NEXT) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
                            (t \<^enum> ( DATA) :=\<^sub>C \<lbrakk>[ NEXT]\<^sub>v\<rbrakk>) ;;
                            (t \<^enum> ( RET) :=\<^sub>C [0]\<^sub>n) ;;
                            (t \<^enum> ( END) :=\<^sub>C [1]\<^sub>n) 
                          {inv_stack1 s (st:=\<^sub>n\<^sub>e (stack_next st - 1))}"
  apply (rule_tac Pa = "p5_pre_noframe t s st ** p5_frame s st" and Qa = "p9_post_noframe t 
  s st ** p5_frame s st" in safe_assn_equiv, simp add: assn_equiv_reflex)
  using p9_post_equiv apply auto[1] apply (rule rule_frame, rule safe_p59_noframe, simp)
    apply (simp add: p5_cond_if_def p5_cond_def, simp)
  apply (simp add: p5_frame_def fvA_is_waitq stm_def)
  by (simp add:  inv_stack_buf_waitq_def inv_stack_pt_def  disjoint_def )

lemma safe_p1011_noframe : "fvAs \<Gamma> = {} \<Longrightarrow> t \<noteq> NULL \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile> 
                          {inv_stack1 s st}  
                         (t \<^enum> ( RET) :=\<^sub>C ([EBUSY]\<^sub>n)) ;;
                         (t \<^enum> ( END) :=\<^sub>C ([1]\<^sub>n)) 
                          {inv_stack1 s st}"
  apply (rule_tac Q = "inv_stack1 s st \<and>\<^sub>S\<^sub>L \<langle>[ RET]\<^sub>v =\<^sub>b [EBUSY]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_seq)
   apply (rule rule_stm_stack', simp, simp add: disjoint_def )
       apply (simp add: inv_stack1_def fvA_is_stack , simp)
  apply (simp add: inv_stack1_def fvA_is_stack )
    apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq)
    apply (simp add: inv_stack1_def fvA_is_stack fvA_inv_stack )
   apply (simp add: )
  apply (rule_tac P = "inv_stack1 s st" and Q = "inv_stack1 s st \<and>\<^sub>S\<^sub>L \<langle>[END]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_conseq)
    apply (rule rule_stm_stack', simp, simp add: disjoint_def )
        apply (simp add: inv_stack1_def fvA_is_stack , simp)
      apply (simp add: inv_stack1_def fvA_is_stack )
    apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_readyq)
     apply (simp add: inv_stack1_def fvA_is_stack fvA_inv_stack )
  apply (simp add: )
  by (simp_all add: implies_def)

lemma p10_pre_implies : "p4_post_noframe t s st ** p4_frame st \<sqsubseteq> inv_stack1 s st"
  apply (simp add: p4_post_noframe_def) apply (rule_tac Q = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n **
    (stack_node s st) **  p4_frame st" in implies_trans, simp add: implies_def) apply auto[1]
  apply (rule equiv_implies, simp add: p4_frame_def inv_stack1_def is_stack_def)
  by (simp add: assn_equiv_symmetry inv_stack_buf_waitq_def inv_stack_pt_def safe_p24_pre_equiv_aux)

definition p12_pre_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p12_pre_noframe t x s st = (inv_cur1 t x) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

definition p12_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p12_post t x s st = (inv_cur1 t x) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[ FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

definition p13_pre' :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p13_pre' t x s st = (inv_cur1 t x \<and>\<^sub>S\<^sub>L  \<langle>[ FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b 
  [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl 
  (stack_wait st) (stack_tcbs st)"

definition p13_pre :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p13_pre t x s st = (([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n) ** ((thread_node t x) \<and>\<^sub>S\<^sub>L \<langle>[ FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b 
  [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl 
  (stack_wait st) (stack_tcbs st)" 

lemma p12_post_equiv : "p12_post t x s st \<equiv>\<^sub>S\<^sub>L p13_pre' t x s st"
  apply (simp add: p12_post_def p13_pre'_def, rule assn_equiv_cong_star)
  apply (simp add: assn_equiv_def) apply auto[1] by (simp add: assn_equiv_reflex)

lemma p12_post_implies : "p12_post t x s st \<sqsubseteq> p13_pre t x s st"
  apply (rule_tac Q = "p13_pre' t x s st" in implies_trans)
   apply (simp add: equiv_implies p12_post_equiv)
  apply (simp add: p13_pre'_def p13_pre_def, rule implies_star, rule implies_star)
    apply (simp add: inv_cur1_def  is_cur_def implies_def) apply auto[1]
  by (simp_all add: implies_def)

definition p13_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p13_post t x s st = (([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n) ** (thread_node t (x:=\<^sub>n\<^sub>x (stack_wait st)) \<and>\<^sub>S\<^sub>L 
  \<langle>[ FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [stack_wait st]\<^sub>n\<rangle>\<^sub>S\<^sub>L)) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

definition p14_pre :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p14_pre t x s st = (([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n) ** (thread_node t (x:=\<^sub>n\<^sub>x (stack_wait st)))) ** 
  (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

lemma p13_post_implies : "p13_post t x s st \<sqsubseteq> p14_pre t x s st"
  apply (simp add: p13_post_def p14_pre_def implies_def) by blast

definition p14_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p14_post t x s st = (([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n) ** (thread_node t (x:=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED))) ** 
  (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

definition p15_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p15_post t x s st = (([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n) ** (thread_node t (x:=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED))) ** 
  (stack_node s (st:=\<^sub>w\<^sub>a t) \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

definition p16_pre :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p16_pre t x s st = (([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n) ** (thread_node t (x:=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED))) ** 
  stack_node s (st:=\<^sub>w\<^sub>a t) ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

lemma p15_post_implies : "p15_post t x s st \<sqsubseteq> p16_pre t x s st"
  apply (simp add: p15_post_def p16_pre_def implies_def) by blast

definition p16_post :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p16_post t x s st = (([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n) ** (thread_node t (x:=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED))) ** 
  stack_node s (st:=\<^sub>w\<^sub>a t) ** thread_wait_sl (stack_wait st) (stack_tcbs st)"

definition p16_post_noframe :: "nat \<Rightarrow> tcb \<Rightarrow> nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p16_post_noframe t x s st = ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n) ** stack_node s (st :=\<^sub>w\<^sub>a t) ** 
         thread_wait_sl t ((x :=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED) # (stack_tcbs st))"

lemma p16_post_equiv : "p16_post t x s st \<equiv>\<^sub>S\<^sub>L p16_post_noframe t x s st"
  apply (rule_tac Q = "([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n) ** stack_node s (st :=\<^sub>w\<^sub>a t) ** (thread_node t (x:=\<^sub>n\<^sub>x 
  (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED) ** thread_wait_sl (stack_wait st) (stack_tcbs st))" in assn_equiv_trans)
  apply (simp add: p16_post_def) 
  apply (meson Astar_assoc_equiv assn_equiv_symmetry assn_equiv_trans stack_node_equiv2_aux stack_node_equiv3_aux)
  apply (simp add: p16_post_noframe_def, rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (rule thread_wait_sl_insert, simp_all add: uptcb_next_def uptcb_state_def)
  by (simp_all add: thd_st_def thd_data_def thd_next_def)

lemma safe_p1216_noframe : "fvAs \<Gamma> = {} \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile> 
                          {p12_pre_noframe t x s st}  
                          ( FIRST_PENDING_THREAD) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> ;;                  
                          \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [ FIRST_PENDING_THREAD]\<^sub>v ;;
                          \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [BLOCKED]\<^sub>n ;;
                          \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [t]\<^sub>n ;;
                          \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> :=\<^sub>C [NULL]\<^sub>n 
                          {p16_post_noframe t x s st}"
   apply (rule_tac Q = "p15_post t x s st" in rule_seq)
    apply (rule_tac Q = "p14_post t x s st" in rule_seq)
     apply (rule_tac Q = "p13_post t x s st" in rule_seq)
      apply (rule_tac Q = "p12_post t x s st" in rule_seq)
        apply (simp add: p12_pre_noframe_def p12_post_def, rule rule_frame2)
         apply (rule stack_node_read_wait, simp add: )
          apply (simp_all add: fvA_Gamma2 fvA_inv_readyq fvA_is_cur fvA_thread_wait_sl fvA_inv_stack fvA_inv_cur)
       apply (simp add: inv_cur1_def fvA_is_cur disjoint_def )
      apply (rule_tac P = "p13_pre t x s st" and Q = "p13_post t x s st" in rule_conseq)
        apply (simp add: p13_pre_def p13_post_def, rule rule_frame, rule rule_frame, rule rule_frame1)
           apply (rule thread_node_write_next_var, simp_all, simp add: p12_post_implies, simp add: implies_def)
     apply (rule_tac P = "p14_pre t x s st" and Q = "p14_post t x s st" in rule_conseq)
       apply (simp add: p14_pre_def p14_post_def, rule rule_frame, rule rule_frame, rule rule_frame1)
          apply (simp add: thread_node_write_st, simp_all, simp add: p13_post_implies, simp add: implies_def)
    apply (simp add: p14_post_def p15_post_def, rule rule_frame, rule rule_frame1, rule stack_node_write_wait)
      apply (simp_all, simp add: fvA_Gamma2 fvA_inv_readyq fvA_inv_stack fvA_inv_cur )
   apply (rule_tac P = "p16_pre t x s st" and Q = "p16_post t x s st" in rule_conseq)
     apply (simp add: p16_pre_def p16_post_def, intro rule_frame)
       apply (rule rule_write, simp_all, simp add: p15_post_implies)
  by (simp add: equiv_implies p16_post_equiv)

definition p12_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "p12_frame s st \<equiv> ((([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** buf (stack_base st) (stack_top st) (stack_buf st)) 
         \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq st) \<and>\<^sub>S\<^sub>L (inv_stack_pt st))"

lemma p16_post_equiv_aux : "P1 ** P2 ** (P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L
                            P3 ** (P1 ** P2 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P3 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply auto[1]
  apply (rule_tac Q = "P3 ** (P1 ** P2 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
  using Astar_assoc_equiv assn_equiv_conj assn_equiv_symmetry assn_equiv_trans stack_node_equiv3_aux 
   apply blast apply (simp add: assn_equiv_def) by blast

lemma p16_post_frame_equiv : " stack_base st = stack_next st \<Longrightarrow> p16_post_noframe t x s st ** p12_frame s st 
     \<equiv>\<^sub>S\<^sub>L ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n) ** inv_stack1 s (st :=\<^sub>w\<^sub>a t :=\<^sub>t\<^sub>c ((x :=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED) # (stack_tcbs st)))"
  apply (rule_tac Q = "[A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n ** stack_node s (st :=\<^sub>w\<^sub>a t) ** is_waitq t (x :=\<^sub>n\<^sub>x stack_wait st 
  :=\<^sub>s\<^sub>t K_NO_WAIT # stack_tcbs st) ** p12_frame s st" in assn_equiv_trans, simp add: p16_post_noframe_def)
   apply (simp add: assn_equiv_cong_star assn_equiv_reflex assn_equiv_symmetry waitq_equiv)
  apply (rule_tac Q = "[A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n ** (stack_node s (st :=\<^sub>w\<^sub>a t) ** is_waitq t (x :=\<^sub>n\<^sub>x stack_wait st 
  :=\<^sub>s\<^sub>t K_NO_WAIT # stack_tcbs st) ** p12_frame s st)" in assn_equiv_trans, simp add: stack_node_equiv1_aux)
  apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (rule_tac Q = "([A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) **  (stack_node s (st :=\<^sub>w\<^sub>a t) ** is_waitq t (x :=\<^sub>n\<^sub>x 
  stack_wait st :=\<^sub>s\<^sub>t K_NO_WAIT # stack_tcbs st) ** buf (stack_base st) (stack_top st) (stack_buf st)
  \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq st) \<and>\<^sub>S\<^sub>L (inv_stack_pt st))" in assn_equiv_trans)
   apply (simp add: p12_frame_def inv_stack_buf_waitq_def inv_stack_pt_def p16_post_equiv_aux)
  apply (simp add: inv_stack1_def, rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
  apply (simp add: is_stack_def, rule assn_equiv_cong_conj, intro assn_equiv_cong_star)
  by (simp_all add: stack_node_def upstack_wait_def upstack_tcbs_def stack_base_def stack_next_def
     stack_top_def stack_wait_def stack_tcbs_def stack_buf_def inv_stack_buf_waitq_def stack_buf_waitq_def
     inv_stack_pt_def stack_pt_def assn_equiv_reflex)

lemma safe_p1216 : "stack_base st = stack_next st \<Longrightarrow> fvAs \<Gamma> = {} \<Longrightarrow>
                          \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile> 
                          {p12_pre_noframe t x s st ** p12_frame s st}  
                          ( FIRST_PENDING_THREAD) :=\<^sub>C \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> ;;                  
                          \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [ FIRST_PENDING_THREAD]\<^sub>v ;;
                          \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [BLOCKED]\<^sub>n ;;
                          \<lbrakk>[ ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [t]\<^sub>n ;;
                          \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> :=\<^sub>C [NULL]\<^sub>n
                          {[A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n ** inv_stack1 s (st :=\<^sub>w\<^sub>a t :=\<^sub>t\<^sub>c ((x :=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t 
                          BLOCKED) # (stack_tcbs st)))}"
  apply (rule_tac Pa = "p12_pre_noframe t x s st ** p12_frame s st" and Qa = "p16_post_noframe t x s st 
  ** p12_frame s st" in safe_assn_equiv, simp add: assn_equiv_reflex, simp add: p16_post_frame_equiv)
  apply (rule rule_frame, simp add: safe_p1216_noframe, simp add: p12_frame_def fvA_buf)
  by (simp add: disjoint_def inv_stack_buf_waitq_def inv_stack_pt_def )

lemma p12_pre_frame_aux : "P1 ** P2 ** (P3 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L) ** P7 \<equiv>\<^sub>S\<^sub>L
                          P7 ** P2 ** P3 ** (P1 ** P4 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L)"
  apply (rule_tac Q = "P1 ** P2 ** (P3 ** P4) ** P7 \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (simp add: assn_equiv_def) apply blast
  apply (rule_tac Q = "P7 ** P2 ** P3 ** (P1 ** P4) \<and>\<^sub>S\<^sub>L \<langle>P5\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P6\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_cong_conj, rule_tac Q = "P1 ** P4 ** P2 ** P3 ** P7" in assn_equiv_trans)
  apply (rule assn_equiv_cong_star) 
      apply (metis Astar_assoc_equiv Astar_commute_equiv assn_equiv_trans stack_node_equiv2_aux)
     apply (simp add: assn_equiv_reflex, rule_tac Q = "P2 ** P3 ** P7 ** (P1 ** P4)" in assn_equiv_trans)
  using Astar_commute_equiv assn_equiv_trans stack_node_equiv1_aux apply blast
    apply (meson Astar_assoc_equiv Astar_commute_equiv assn_equiv_cong_star assn_equiv_trans)
   apply (simp add: assn_equiv_reflex, simp add: assn_equiv_def)
  by blast

lemma p12_pre_frame_implies : " p4_post_noframe t s st ** p4_frame st ** inv_cur1 t x \<sqsubseteq>
                                p12_pre_noframe t x s st ** p12_frame s st "
  apply (rule_tac Q = "[A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) **
    p4_frame st ** inv_cur1 t x" in implies_trans, simp add: p4_post_noframe_def)
   apply (simp add: implies_def) apply blast apply (rule equiv_implies)
  apply (rule_tac Q = "(inv_cur1 t x) ** (stack_node s st \<and>\<^sub>S\<^sub>L \<langle>[ ADDR]\<^sub>v =\<^sub>b [s]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
  ** is_waitq (stack_wait st) (stack_tcbs st) ** p12_frame s st" in assn_equiv_trans)
  apply (simp add: p4_frame_def p12_frame_def inv_stack_buf_waitq_def inv_stack_pt_def)
   apply (simp add: p12_pre_frame_aux, rule assn_equiv_cong_star)
   apply (simp add: p12_pre_noframe_def, simp add: assn_equiv_cong_star assn_equiv_reflex waitq_equiv)
  by (simp add: assn_equiv_reflex)

lemma rule_inv_stack : "\<forall>s st. \<Gamma> \<turnstile> {P ** inv_stack1 s st} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {P ** inv_stack} C {Q}"
  apply (simp add: CSL_def inv_stack_def) by blast

lemma p5_cond_aux : "\<sigma> \<Turnstile> (p4_post_noframe t s st \<and>\<^sub>S\<^sub>L \<langle>[NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) ** p4_frame st
                      \<Longrightarrow> p5_cond_if st"
  apply (simp add: p4_post_noframe_def p4_frame_def inv_stack_pt_def stack_pt_def p5_cond_if_def
  inv_stack_buf_waitq_def stack_buf_waitq_def)
  apply (case_tac "stack_wait st", case_tac "stack_tcbs st") apply linarith
   apply (simp add: is_waitq_def thread_sl_def) by linarith

lemma p12_cond_aux : "\<sigma> \<Turnstile> ((p4_post_noframe t s st  ** p4_frame st) \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) 
                      ** P \<Longrightarrow> stack_base st = stack_next st"
  by (simp add: p4_post_noframe_def p4_frame_def inv_stack_pt_def stack_pt_def, clarsimp)

lemma p12_cond_aux1 : "user_cmd C \<Longrightarrow> stack_base st = stack_next st \<longrightarrow> \<Gamma> \<turnstile> {((p4_post_noframe t s st  ** p4_frame st) 
     \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) ** P} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {((p4_post_noframe t s st  ** p4_frame st) 
     \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) ** P} C {Q}"
  apply (case_tac "stack_base st = stack_next st", simp, simp)
  apply (simp only: CSL_def) using p12_cond_aux by blast

lemma safe_p1819 : "t \<noteq> NULL \<Longrightarrow> fvAs \<Gamma> = {} \<Longrightarrow>
                    \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) 
                      \<turnstile> {(Aemp \<and>\<^sub>S\<^sub>L \<langle>[END]\<^sub>v =\<^sub>b [K_NO_WAIT]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [RET]\<^sub>v =\<^sub>b [EAGAIN]\<^sub>n\<rangle>\<^sub>S\<^sub>L  } 
                      (t \<^enum> DATA :=\<^sub>C \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tdata\<rbrakk>);; 
                      (t \<^enum> RET :=\<^sub>C [K_NO_WAIT]\<^sub>n) 
                         { Aemp }"
  apply (rule_tac Q = Aemp in rule_seq, rule rule_stm_stack, simp)
  apply (simp add: disjoint_def )
      apply ( simp add: , simp, simp add: , intro allI)
  apply (rule_tac P = "inv_cur1 t ta" and Q = "inv_cur1 t ta \<and>\<^sub>S\<^sub>L \<langle>[DATA]\<^sub>v =\<^sub>b [thd_data ta]\<^sub>n\<rangle>\<^sub>S\<^sub>L"
  in rule_conseq, simp add: inv_cur1_def is_cur_def)
     apply (rule_tac Pa = "([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n \<and>\<^sub>S\<^sub>L inv_is_running ta) ** thread_node t ta" and Qa = "
      ([A_Cur]\<^sub>v \<longmapsto> [t]\<^sub>n  \<and>\<^sub>S\<^sub>L inv_is_running ta) ** (thread_node t ta \<and>\<^sub>S\<^sub>L \<langle>[DATA]\<^sub>v =\<^sub>b [thd_data ta]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" 
       in safe_assn_equiv)
       apply (simp add: inv_is_running_def assn_equiv_def) apply auto[1]
      apply (simp add: inv_is_running_def assn_equiv_def) apply auto[1]
     apply (rule rule_frame1, rule thread_node_read_data, simp add: fvA_Gamma2)
      apply (simp add: fvA_inv_cur fvA_inv_readyq fvA_inv_stack , simp)
     apply (simp add: inv_is_running_def disjoint_def )
      apply (simp add: implies_def) apply (rule_tac Q = "inv_cur1 t ta" in implies_trans)
    apply (simp add: implies_def)
  apply (rule_tac Q = "inv_cur" in implies_trans, simp add: inv_cur_implies2)
   apply (simp add: implies_def, simp add: implies_def)
  apply (rule rule_stm_stack', simp_all)
    apply (simp add: disjoint_def )
   apply (rule_tac P = Aemp and Q = "Aemp \<and>\<^sub>S\<^sub>L \<langle>[RET]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_conseq)
     apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
     apply (simp add: implies_def, simp add: implies_def)
  done
  
lemma safe_pop : "fvAs \<Gamma> = {} \<Longrightarrow> 
                   \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>
                    {Aemp \<and>\<^sub>S\<^sub>L \<langle>[t \<noteq> NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L} stack_pop t timeout { Aemp}"
  apply (simp only: stack_pop_def)
  apply (rule rule_Clocals)
  apply (case_tac t, simp add: CSL_def stm_def)
  apply (rule_tac Q = Aemp in rule_seq)
   apply (rule_tac Q = "p1_post t" in rule_seq, simp add: p1_post_def)
    apply (rule rule_stm_stack', simp, simp add: disjoint_def , simp, simp, simp)
    apply (rule_tac Pa = " Aemp" and Qa = "Aemp \<and>\<^sub>S\<^sub>L \<langle>[END]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L"
    in safe_assn_equiv, simp add: assn_equiv_def, simp add: assn_equiv_def) apply auto[1]
     apply (rule rule_assign_num1, simp add: fvA_Gamma2 fvA_inv_cur fvA_inv_stack fvA_inv_readyq)
  apply (simp , simp)
   apply (rule rule_with_true, simp, rule rule_inv_stack, intro allI)
   apply (rule_tac Q = "p1_post t ** (p4_post_noframe t s st ** p4_frame st)" in rule_seq, simp add: safe_p24)
   apply (rule rule_if, rule_tac P = "(p4_post_noframe t s st \<and>\<^sub>S\<^sub>L \<langle>[NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) 
    ** p4_frame st" and Q = "inv_stack" in rule_conseq)
  apply (case_tac "\<not> p5_cond_if st", simp only: CSL_def) 
  using p5_cond_aux stm_def user_cmd.simps(15) apply fastforce
  apply (rule_tac P = "p5_pre_noframe t s st ** p5_frame s st" and Q = "inv_stack1 s (st:=\<^sub>n\<^sub>e 
  (stack_next st - 1))" in rule_conseq) using safe_p59 apply auto[1]
       apply (simp add: p5_pre_implies, simp add: inv_stack_implies)
     apply (simp add: p1_post_def implies_def) apply auto[1] apply (simp add: implies_def)
   apply (rule rule_if) apply (rule_tac P = "inv_stack1 s st" and Q = "inv_stack1 s st" in rule_conseq)
  using safe_p1011_noframe apply auto[1] 
     apply (rule_tac Q = "p4_post_noframe t s st ** p4_frame st" in implies_trans)
      apply (simp add: implies_def p1_post_def) apply auto[1]
  apply (simp add: p10_pre_implies) 
  using Aemp_equiv assn_equiv_symmetry equiv_implies implies_trans inv_stack_implies apply blast
   apply (rule rule_stm_stack, simp, simp add: disjoint_def )
      apply (simp add: p4_frame_def fvA_buf fvA_is_waitq inv_stack_buf_waitq_def inv_stack_pt_def)
      apply (simp add: p1_post_def p4_post_noframe_def stack_node_def , simp)
    apply (simp add: p4_frame_def fvA_buf fvA_is_waitq inv_stack_buf_waitq_def inv_stack_pt_def)
    apply (simp add: p1_post_def p4_post_noframe_def stack_node_def , intro allI)
   apply (rule_tac P = "((p4_post_noframe t s st ** p4_frame st) \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [NEXT]\<^sub>v >\<^sub>b [BASE]\<^sub>v\<rangle>\<^sub>S\<^sub>L) 
   ** inv_cur1 t ta" and Q = "inv_cur ** inv_stack" in rule_conseq)
     apply (rule p12_cond_aux1, simp add: stm_def, rule impI)
  apply (rule_tac P = "p12_pre_noframe t ta s st ** p12_frame s st" and Q = "[A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n ** 
  inv_stack1 s (st :=\<^sub>w\<^sub>a t :=\<^sub>t\<^sub>c ((ta :=\<^sub>n\<^sub>x (stack_wait st) :=\<^sub>s\<^sub>t BLOCKED) # (stack_tcbs st)))" in rule_conseq)
       apply (simp add:  safe_p1216)     
      apply (rule_tac Q = "(p4_post_noframe t s st ** p4_frame st)
       ** inv_cur1 t ta" in implies_trans, simp add: implies_def) apply auto[1]
      apply (simp add: p12_pre_frame_implies)
     apply (rule implies_star, simp add: inv_cur_implies1, simp add: inv_stack_implies)
    apply (simp add: p1_post_def implies_def) apply fastforce apply (rule equiv_implies)
  using Aemp_equiv Astar_assoc_equiv Astar_commute_equiv assn_equiv_symmetry assn_equiv_trans apply blast
apply (rule rule_if, rule rule_if) 
     apply (rule_tac P = Aemp and Q = Aemp in rule_conseq, simp add: rule_skip)
      apply (simp add: implies_def, simp add: implies_def)
    apply (simp add: safe_p1819, simp_all)
   apply (rule_tac P = Aemp and Q = Aemp in rule_conseq, simp add: rule_skip)
    apply (simp add: implies_def, simp add: implies_def)
  apply (simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq) 
  done

end