theory Stack_Aux
  imports invariant
begin
(* ======================== implie rule for Aex =====================*)
lemma inv_readyq_implies : "inv_readyq1 r xs \<sqsubseteq> inv_readyq"
  apply (simp add: implies_def inv_readyq_def) by blast

lemma inv_stack_implies : "inv_stack1 s st \<sqsubseteq> inv_stack"
  apply (simp add: implies_def inv_stack_def) 
  by (metis prod_cases6)

lemma inv_cur_implies1 : "[A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n \<sqsubseteq> inv_cur"
  by (simp add: inv_cur_def implies_def) 

lemma inv_cur_implies2 : "inv_cur1 p t \<sqsubseteq> inv_cur"
  apply (simp add: inv_cur_def implies_def) 
  by (metis prod_cases3)

(* ========================   fvA of assertions ================ *)
lemma fvA_array : "fvA (buf h tn l) = {}"
  by (induct l arbitrary: h tn, simp_all)

lemma fvA_thread_node : "fvA (thread_node p t) = {}"
  by (case_tac p, simp_all add: thread_node.cases)

lemma fvA_thread_sl_empty : "fvA (thread_sl NULL xs) = {}"
  by (simp add: thread_sl_def, case_tac xs, simp_all add: thread_slseg.cases)

lemma fvA_thread_sl_nonempty : "r \<noteq> NULL \<Longrightarrow> fvA (thread_sl r xs) = {}"
  apply (simp add: thread_sl_def, induct xs  arbitrary: r, simp add: thread_slseg.cases)
  apply (case_tac r, simp_all add: thread_slseg.cases)
  apply (case_tac "thd_next a")
  using fvA_thread_sl_empty thread_sl_def apply auto[1]
  by simp

lemma fvA_thread_sl : "fvA (thread_sl p xs) = {}"
  apply (case_tac p, simp add: fvA_thread_sl_empty)
  by (simp add: fvA_thread_sl_nonempty)

lemma fvA_thread_ready_sl_empty : "fvA (thread_ready_sl NULL xs) = {}"
  by (simp add: thread_ready_sl_def, case_tac xs, simp_all add: thread_slseg.cases)

lemma fvA_thread_ready_sl_nonempty : "r \<noteq> NULL \<Longrightarrow> fvA (thread_ready_sl r xs) = {}"
  apply (simp add: thread_ready_sl_def, induct xs  arbitrary: r, simp add: thread_slseg.cases)
  apply (case_tac r, simp_all add: thread_slseg.cases inv_is_ready_def)
  apply (case_tac "thd_next a")
  using fvA_thread_ready_sl_empty thread_ready_sl_def apply auto[1]
  by simp

lemma fvA_thread_ready_sl : "fvA (thread_ready_sl p xs) = {}"
  apply (case_tac p, simp add: fvA_thread_ready_sl_empty)
  by (simp add: fvA_thread_ready_sl_nonempty)
  
lemma fvA_inv_thread_distinct : "fvA (inv_thread_distinct h tcbs) = {}"
  by (induct tcbs arbitrary: h, simp_all add: inv_thread_distinct_def)

lemma fvA_is_cur : "fvA (is_cur p t) = {}"
  by (simp add: is_cur_def fvA_thread_node inv_is_running_def)

lemma fvA_is_readyq : "fvA (is_readyq r  xs) = {}"  
  by (simp add: is_readyq_def fvA_thread_sl inv_all_ready_def inv_thread_distinct_def)

lemma fvA_buf : "fvA (buf h tn xs) = {}"
  by (induct xs arbitrary: h, simp_all)

lemma fvA_thread_wait_sl_empty : "fvA (thread_wait_sl NULL xs) = {}"
  by (simp add: thread_wait_sl_def, case_tac xs, simp_all add: thread_slseg.cases)

lemma fvA_thread_wait_sl_nonempty : "r \<noteq> NULL \<Longrightarrow> fvA (thread_wait_sl r xs) = {}"
  apply (simp add: thread_wait_sl_def, induct xs arbitrary: r, simp add: thread_slseg.cases)
  apply (case_tac r, simp_all add: thread_slseg.cases inv_is_blocked_def)
  apply (case_tac "thd_next a")
  using fvA_thread_wait_sl_empty thread_wait_sl_def apply auto[1]
  by simp

lemma fvA_is_waitq : "fvA (is_waitq r xs) = {}"
  by (simp add: is_waitq_def fvA_thread_sl inv_all_blocked_def inv_thread_distinct_def)

lemma fvA_thread_wait_sl : "fvA (thread_wait_sl p xs) = {}"
  apply (case_tac p, simp add: fvA_thread_wait_sl_empty)
  by (simp add: fvA_thread_wait_sl_nonempty)

lemma fvA_inv_cur : "fvA inv_cur = {A_Cur}"
  by (simp add: inv_cur_def inv_cur1_def fvA_is_cur  insert_commute)

lemma fvA_inv_readyq : "fvA inv_readyq = {A_Readyq}"
  by (simp add: inv_readyq_def inv_readyq1_def fvA_is_readyq  insert_commute)


lemma fvA_is_stack : "fvA (is_stack s st) = {}"
  by (simp add: is_stack_def stack_node_def fvA_is_waitq fvA_buf inv_stack_pt_def inv_stack_buf_waitq_def)

lemma fvA_inv_stack : "fvA inv_stack = {A_Stack}"
  by (simp add: inv_stack_def inv_stack1_def fvA_is_stack)

(* ======================== auxillary lemma for invariant  ================ *)




(* ================== auxillary lemma for tcb read and modify ===================*)
lemma thread_node_equiv : " thread_node p t \<equiv>\<^sub>S\<^sub>L thread_node_nonempty p t"
  apply (case_tac p, simp add: thread_node_nonempty_def assn_equiv_def)
  by (simp add: thread_node_nonempty_def assn_equiv_def)

(* ==================== read next ======================*)
definition thread_node_next :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_next p x = [p + 1]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n"

definition thread_node_next_frame :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_next_frame p x = (([p]\<^sub>n \<longmapsto> [thd_st x]\<^sub>n) ** ([p + 2]\<^sub>n \<longmapsto> [thd_data x]\<^sub>n) 
                                  \<and>\<^sub>S\<^sub>L \<langle>[p \<noteq> NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L)" 

lemma equiv_aux :  "(P ** Q ** R \<and>\<^sub>S\<^sub>L \<langle>S\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L (P ** (Q ** R \<and>\<^sub>S\<^sub>L \<langle>S\<rangle>\<^sub>S\<^sub>L))"
  using Astar_assoc_equiv assn_equiv_def by auto

lemma thread_node_nonempty_equiv1 : "thread_node_nonempty p x \<equiv>\<^sub>S\<^sub>L (thread_node_next p x 
                            ** thread_node_next_frame p x)"
  apply (simp add: thread_node_nonempty_def thread_node_next_def thread_node_next_frame_def)
  apply (rule_tac Q = "([Suc p]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n) ** ([p]\<^sub>n \<longmapsto> [thd_st x]\<^sub>n)
                  ** ([Suc (Suc p)]\<^sub>n \<longmapsto> [thd_data x]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[K_NO_WAIT < p]\<^sub>b\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_conj, simp add: Astar_commute_equiv assn_equiv_cong_star assn_equiv_reflex)
  by (simp add: equiv_aux)
  
lemma thread_node_equiv1 : "thread_node p x \<equiv>\<^sub>S\<^sub>L (thread_node_next p x 
                            ** thread_node_next_frame p x)"
  using assn_equiv_trans thread_node_equiv thread_node_nonempty_equiv1 by blast

lemma thread_node_readnext :  " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile> {thread_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
              v2 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>tnext\<rbrakk>
            {thread_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(thread_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_next_frame p x" 
         and Qa = "(thread_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [thd_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
         ** thread_node_next_frame p x" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv1 apply auto[1]
  using assn_equiv_def thread_node_equiv1 apply auto[1] 
  apply (simp add: thread_node_next_def tcb_p_next_def, rule rule_frame)
   apply (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 Un_iff fvE.simps(1) fvE.simps(2) 
   rule_read_var_offn singletonD sup_bot.right_neutral)
  by (simp add: thread_node_next_frame_def)

(* ==================== write state ======================*)
definition thread_node_st :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_st p x = [p]\<^sub>n \<longmapsto> [thd_st x]\<^sub>n"

definition thread_node_st_frame :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_st_frame p x = (([p + 1]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n) ** ([p + 2]\<^sub>n \<longmapsto> [thd_data x]\<^sub>n) 
                            \<and>\<^sub>S\<^sub>L \<langle>[p \<noteq> NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L)"

lemma thread_node_nonempty_equiv2 : "thread_node_nonempty p x \<equiv>\<^sub>S\<^sub>L 
                          thread_node_st p x ** thread_node_st_frame p x"
  apply (simp add: Astar_assoc_equiv thread_node_nonempty_def thread_node_st_def thread_node_st_frame_def)
  apply (rule_tac Q = "([p]\<^sub>n \<longmapsto> [thd_st x]\<^sub>n) **
    ([Suc p]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n) ** ([Suc (Suc p)]\<^sub>n \<longmapsto> [thd_data x]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[K_NO_WAIT < p]\<^sub>b\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (rule assn_equiv_conj, simp add: Astar_commute_equiv assn_equiv_cong_star assn_equiv_reflex)
  by (simp add: equiv_aux)

lemma thread_node_equiv2 : "thread_node p x \<equiv>\<^sub>S\<^sub>L 
                          thread_node_st p x ** thread_node_st_frame p x"
  using assn_equiv_trans thread_node_equiv thread_node_nonempty_equiv2 by blast

lemma uptcbst_equiv : "thread_node p (uptcb_state x state) \<equiv>\<^sub>S\<^sub>L [p]\<^sub>n \<longmapsto> [state]\<^sub>n
                           ** thread_node_st_frame p x"
  apply (rule_tac Q = "thread_node_nonempty p (uptcb_state x state)" in assn_equiv_trans)
  apply (simp add: thread_node_equiv)
  by (simp add: thread_node_nonempty_def thread_node_st_frame_def thd_st_def uptcb_state_def 
        thd_next_def thd_data_def equiv_aux) 

lemma thread_node_write_st : "
      \<Gamma> \<turnstile> {thread_node t x}
            \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [state]\<^sub>n
          {thread_node t (uptcb_state x state)}"
    apply (rule_tac Pa = "thread_node_st t x  ** thread_node_st_frame t x" and
  Qa = "[t]\<^sub>n \<longmapsto> [state]\<^sub>n  ** thread_node_st_frame t x" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv2 apply auto[1]
  using assn_equiv_def uptcbst_equiv apply auto[1]
  by (rule rule_frame, simp add: thread_node_st_def tcb_p_state_def, rule rule_write, simp)

lemma thread_node_write_st' : "
      \<Gamma> \<turnstile> {thread_node p x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
            \<lbrakk>[v]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [state]\<^sub>n
          {thread_node p (uptcb_state x state)  \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(thread_node_st p x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_st_frame p x" and
  Qa = "([p]\<^sub>n \<longmapsto> [state]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_st_frame p x" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv2 apply auto[1]
  using assn_equiv_def uptcbst_equiv apply auto[1]
  by (rule rule_frame, simp add: thread_node_st_def tcb_p_state_def, rule rule_write_var, simp)

(* ==================== write data ======================*)
definition thread_node_data :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_data p x = [p + 2]\<^sub>n \<longmapsto> [thd_data x]\<^sub>n"

definition thread_node_data_frame :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_data_frame p x = (([p]\<^sub>n \<longmapsto> [thd_st x]\<^sub>n) ** ([p + 1]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n)
                     \<and>\<^sub>S\<^sub>L \<langle>[p \<noteq> NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L)"

lemma thread_node_nonempty_equiv3 : "thread_node_nonempty p x \<equiv>\<^sub>S\<^sub>L thread_node_data p x 
                                            ** thread_node_data_frame p x"
  apply (simp add: thread_node_nonempty_def thread_node_data_def thread_node_data_frame_def)
  apply (rule_tac Q = "([Suc (Suc p)]\<^sub>n \<longmapsto> [thd_data x]\<^sub>n) **
    ([p]\<^sub>n \<longmapsto> [thd_st x]\<^sub>n) ** ([Suc p]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[K_NO_WAIT < p]\<^sub>b\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
   apply (meson Astar_assoc_equiv Astar_commute_equiv assn_equiv_conj assn_equiv_trans)
  by (simp add: equiv_aux)

lemma thread_node_equiv3 : "thread_node p x \<equiv>\<^sub>S\<^sub>L thread_node_data p x ** thread_node_data_frame p x"
  using assn_equiv_trans thread_node_equiv thread_node_nonempty_equiv3 by blast

lemma uptcbdata_equiv : "thread_node p (uptcb_data x data) \<equiv>\<^sub>S\<^sub>L [p + 2]\<^sub>n \<longmapsto> [data]\<^sub>n
                           ** thread_node_data_frame p x"
  apply (case_tac p, simp add: thread_node.cases thread_node_data_frame_def assn_equiv_def)
  apply (simp add: thread_node.cases thread_node_data_frame_def thd_st_def thd_data_def thd_next_def
        uptcb_data_def)
  by (meson Astar_assoc_equiv Astar_commute_equiv Conj_true_equiv assn_equiv_symmetry
      assn_equiv_trans equiv_aux)

lemma thread_node_write_data : "\<Gamma> \<turnstile> {thread_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                          \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>tdata\<rbrakk> :=\<^sub>C [data]\<^sub>n
          {thread_node p (uptcb_data x data) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(thread_node_data p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_data_frame p x"
  and Qa = "([p + 2]\<^sub>n \<longmapsto> [data]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_data_frame p x"
  in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv3 apply auto[1]
  using assn_equiv_def uptcbdata_equiv apply auto[1]
  apply (rule rule_frame, simp_all) 
  by (metis add_2_eq_Suc' rule_write_var_offn tcb_p_data_def thread_node_data_def)
(* ==================== read data ======================*)
lemma thread_node_read_data :  " \<lbrakk>v1 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile> {thread_node t x }
              v1 :=\<^sub>C \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tdata\<rbrakk>
            {thread_node t x  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [thd_data x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "thread_node_data t x  ** thread_node_data_frame t x" and Qa = "(thread_node_data 
  t x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [thd_data x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_data_frame t x" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv3 apply auto[1]
  using assn_equiv_def thread_node_equiv3 apply auto[1] 
  apply (simp add: thread_node_data_def tcb_p_data_def, rule rule_frame)
  apply (rule_tac Pa = "([t]\<^sub>n +\<^sub>e [2]\<^sub>n) \<longmapsto> [thd_data x]\<^sub>n" and Qa = "([t]\<^sub>n +\<^sub>e [2]\<^sub>n) \<longmapsto> [thd_data x]\<^sub>n
  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [thd_data x]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in safe_assn_equiv, simp_all add: assn_equiv_def)
  by (rule rule_read, simp, simp add: thread_node_data_frame_def)

(* ==================== update next ======================*)

lemma uptcbnext_equiv : "thread_node p (uptcb_next x next) \<equiv>\<^sub>S\<^sub>L [p + 1]\<^sub>n \<longmapsto> [next]\<^sub>n
                           ** thread_node_next_frame p x"
  apply (case_tac p, simp add: thread_node_next_frame_def assn_equiv_def)
  apply (simp add: thread_node.cases uptcb_next_def thd_st_def thd_next_def thd_data_def 
       thread_node_next_frame_def)
  by (meson Astar_assoc_equiv2 Astar_commute_equiv Conj_true_equiv assn_equiv_conj_Apure 
      assn_equiv_symmetry assn_equiv_trans)

lemma thread_node_write_next : " \<Gamma> \<turnstile> {thread_node t x}
                                \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [next]\<^sub>n
                          {thread_node t (uptcb_next x next) }"
  apply (rule_tac Pa = "thread_node_next t x  ** thread_node_next_frame t x" and Qa = 
  "([t + 1]\<^sub>n \<longmapsto> [next]\<^sub>n) ** thread_node_next_frame t x" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv1 apply auto[1]
  using assn_equiv_def uptcbnext_equiv apply auto[1]
  apply (rule rule_frame, simp add: thread_node_next_def tcb_p_next_def)
  by (metis One_nat_def Suc_eq_plus1 rule_write_offn, simp)

lemma thread_node_write_next_var : " \<Gamma> \<turnstile> {thread_node t x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [v]\<^sub>v
                          {thread_node t (uptcb_next x n) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(thread_node_next t x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_next_frame t x" 
  and Qa = "(([t + 1]\<^sub>n \<longmapsto> [v]\<^sub>v) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_next_frame t x" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv1 apply auto[1]
  using assn_equiv_def uptcbnext_equiv apply auto[1]
  apply (rule rule_frame, simp add: thread_node_next_def tcb_p_next_def)
  apply (rule_tac Pa = "[Suc t]\<^sub>n \<longmapsto> [thd_next x]\<^sub>n ** ( \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and Qa = "
  [Suc t]\<^sub>n \<longmapsto> [v]\<^sub>v ** ( \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv1 apply auto[1]
  using assn_equiv_def uptcbnext_equiv apply auto[1]
   apply (rule rule_frame) apply (metis Suc_eq_plus1 add.left_neutral rule_write_offn)
  by simp_all


lemma thread_node_write_next' : " \<Gamma> \<turnstile> {thread_node p x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                                      \<lbrakk>[v]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [next]\<^sub>n
                      {thread_node p (uptcb_next x next) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(thread_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_next_frame p x"
  and Qa = "([p + 1]\<^sub>n \<longmapsto> [next]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** thread_node_next_frame p x"
  in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv1 apply auto[1]
  using assn_equiv_def uptcbnext_equiv apply auto[1]
  apply (rule rule_frame, simp_all) 
  using Suc_eq_plus1 rule_write_var_offn tcb_p_next_def thread_node_next_def by presburger

corollary thread_node_write_next_fromvar : "
      \<Gamma> \<turnstile> {thread_node p x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Ea =\<^sub>b [next]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
            \<lbrakk>[v]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C Ea
          {thread_node p (uptcb_next x next) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Ea =\<^sub>b [next]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(thread_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_node_next_frame p x
  \<and>\<^sub>S\<^sub>L \<langle>Ea =\<^sub>b [next]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" and Qa = "(([p + 1]\<^sub>n \<longmapsto> Ea) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (thread_node_next_frame 
  p x \<and>\<^sub>S\<^sub>L \<langle>Ea =\<^sub>b [next]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in safe_assn_equiv)
  using assn_equiv_def thread_node_equiv1 apply auto[1]
  using assn_equiv_def uptcbnext_equiv apply auto[1]
  apply (rule rule_frame) 
  using rule_write_var_offn tcb_p_next_def thread_node_next_def apply presburger 
  by simp

(* ================== auxillary lemma for stack read and modify ========== *)

(* ==================== read base ======================*)
definition stack_node_base :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_base p x = [p]\<^sub>n \<longmapsto> [stack_base x]\<^sub>n"

definition stack_node_base_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_base_frame p x = ([p + 1]\<^sub>n \<longmapsto> [stack_next x]\<^sub>n) ** ([p + 2]\<^sub>n \<longmapsto> [stack_top x]\<^sub>n) 
                                   ** ([p + 3]\<^sub>n \<longmapsto> [stack_wait x]\<^sub>n)" 

lemma stack_node_equiv1_aux : "P ** Q ** R ** S \<equiv>\<^sub>S\<^sub>L P ** (Q ** R ** S)"
  by (meson Astar_assoc_equiv assn_equiv_cong_star assn_equiv_reflex assn_equiv_trans)

lemma stack_node_equiv1 : " stack_node p x \<equiv>\<^sub>S\<^sub>L stack_node_base p x ** stack_node_base_frame p x"
  by (simp add: stack_node_base_def stack_node_base_frame_def stack_node_def stack_node_equiv1_aux)

lemma stack_node_read_base : " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
               v2 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>sbase\<rbrakk>
            {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_base x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_base p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node_base_frame p x)"
         and Qa = "(stack_node_base p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_base x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
          ** (stack_node_base_frame p x)" in safe_assn_equiv)
  using assn_equiv_def stack_node_equiv1 apply auto[1]
  using assn_equiv_def stack_node_equiv1 apply auto[1]
  apply (rule rule_frame, simp add: stack_node_base_def stack_p_base_def)
  by (rule rule_read_var, simp, simp add: stack_node_base_frame_def)

lemma stack_node_read_base1 : " \<lbrakk>v1 \<noteq> v3; v2 \<noteq> v3; v1 \<notin> fvAs \<Gamma>; v3 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
               v3 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>sbase\<rbrakk>
            {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v3]\<^sub>v =\<^sub>b [stack_base x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node p x  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
         and Qa = "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v3]\<^sub>v =\<^sub>b [stack_base x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
          ** (\<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
    apply (rule_tac Q = "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
     apply (simp add: Apure_Astar_equiv assn_equiv_symmetry, simp add: assn_equiv_def)
  apply (rule_tac Q = "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v3]\<^sub>v =\<^sub>b [stack_base x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L
    \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
    apply (simp add: Apure_Astar_equiv assn_equiv_symmetry, simp add: assn_equiv_def) apply auto[1]
  apply (rule rule_frame, simp add: stack_node_read_base)
  by (simp add: disjoint_def)

(* ===================== read next ===================== *)
definition stack_node_next :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_next p x = [p + 1]\<^sub>n \<longmapsto> [stack_next x]\<^sub>n"

definition stack_node_next_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_next_frame p x = ([p]\<^sub>n \<longmapsto> [stack_base x]\<^sub>n) ** ([p + 2]\<^sub>n \<longmapsto> [stack_top x]\<^sub>n) 
                                   ** ([p + 3]\<^sub>n \<longmapsto> [stack_wait x]\<^sub>n)" 

lemma stack_node_equiv2_aux : "P ** Q ** R ** S \<equiv>\<^sub>S\<^sub>L Q ** (P ** R ** S)"
  by (meson Astar_assoc_equiv2 Astar_commute_equiv assn_equiv_cong_star 
      assn_equiv_reflex assn_equiv_trans)

lemma stack_node_equiv2 : " stack_node p x \<equiv>\<^sub>S\<^sub>L stack_node_next p x ** stack_node_next_frame p x"
  by (simp add: stack_node_next_def stack_node_next_frame_def stack_node_def stack_node_equiv2_aux)

lemma stack_node_read_next : " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
               v2 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>snext\<rbrakk>
            {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node_next_frame p x)"
         and Qa = "(stack_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_next x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
          ** (stack_node_next_frame p x)" in safe_assn_equiv)
  using assn_equiv_def stack_node_equiv2 apply auto[1]
  using assn_equiv_def stack_node_equiv2 apply auto[1]
  apply (rule rule_frame, simp add: stack_node_next_def stack_p_next_def)
  apply (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 Un_iff fvE.simps(1) fvE.simps(2) 
   rule_read_var_offn singletonD sup_bot.right_neutral)
  by (simp add: stack_node_next_frame_def)

(* ===================== write next ===================== *)
lemma stack_node_write_next_frame_equiv : "stack_node_next_frame p (x:=\<^sub>n\<^sub>e n) \<equiv>\<^sub>S\<^sub>L stack_node_next_frame p x"
  by (simp add: stack_node_next_frame_def, simp add: upstack_next_def stack_top_def stack_base_def
      stack_next_def stack_wait_def assn_equiv_reflex)

lemma stack_node_write_next_equiv : "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Q\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L 
       (stack_node_next p x \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Q\<rangle>\<^sub>S\<^sub>L) ** stack_node_next_frame p x"
  apply (rule_tac Q = "(stack_node_next p x ** stack_node_next_frame p x) \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Q\<rangle>\<^sub>S\<^sub>L" 
        in assn_equiv_trans, simp add: assn_equiv_conj stack_node_equiv2)
  apply (simp add: assn_equiv_def) by blast

lemma stack_node_write_next_minus1 : " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>snext\<rbrakk> :=\<^sub>C [v2]\<^sub>v -\<^sub>e [1]\<^sub>n
            {stack_node p (x :=\<^sub>n\<^sub>e n - 1) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node_next_frame
   p x" and Qa = "(([p + 1]\<^sub>n \<longmapsto> ([v2]\<^sub>v -\<^sub>e [1]\<^sub>n)) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node_next_frame
   p x" in safe_assn_equiv, simp add: assn_equiv_symmetry stack_node_write_next_equiv)
  apply (rule_tac Q = "(stack_node_next p (x :=\<^sub>n\<^sub>e n - 1) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L)
  ** stack_node_next_frame p (x :=\<^sub>n\<^sub>e n - 1)" in assn_equiv_trans)
    apply (rule assn_equiv_cong_star, simp add: upstack_next_def stack_node_next_def stack_next_def
    assn_equiv_def) apply auto[1]
    apply (simp add: assn_equiv_symmetry stack_node_write_next_frame_equiv)
  apply (simp add: assn_equiv_symmetry stack_node_write_next_equiv)
  apply (rule rule_frame, simp add: stack_node_next_def stack_p_next_def)
    apply (metis Suc_eq_plus1 add.left_neutral rule_write_var_offn_with_conj)
  by (simp add: stack_node_next_frame_def)
   
lemma stack_node_write_next_add1 : " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>snext\<rbrakk> :=\<^sub>C [v2]\<^sub>v +\<^sub>e [1]\<^sub>n
            {stack_node p (x :=\<^sub>n\<^sub>e n + 1) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_next p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node_next_frame
   p x" and Qa = "(([p + 1]\<^sub>n \<longmapsto> ([v2]\<^sub>v +\<^sub>e [1]\<^sub>n)) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node_next_frame
   p x" in safe_assn_equiv, simp add: assn_equiv_symmetry stack_node_write_next_equiv)
  apply (rule_tac Q = "(stack_node_next p (x :=\<^sub>n\<^sub>e n + 1) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L)
  ** stack_node_next_frame p (x :=\<^sub>n\<^sub>e n + 1)" in assn_equiv_trans)
    apply (rule assn_equiv_cong_star, simp add: upstack_next_def stack_node_next_def stack_next_def
    assn_equiv_def) apply auto[1]
    apply (simp add: assn_equiv_symmetry stack_node_write_next_frame_equiv)
  apply (simp add: assn_equiv_symmetry stack_node_write_next_equiv)
  apply (rule rule_frame, simp add: stack_node_next_def stack_p_next_def)
    apply (metis Suc_eq_plus1 add.left_neutral rule_write_var_offn_with_conj)
  by (simp add: stack_node_next_frame_def)

(* ===================== read top ======================= *)
definition stack_node_top :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_top p x = [p + 2]\<^sub>n \<longmapsto> [stack_top x]\<^sub>n"

definition stack_node_top_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_top_frame p x = ([p]\<^sub>n \<longmapsto> [stack_base x]\<^sub>n) ** ([p + 1]\<^sub>n \<longmapsto> [stack_next x]\<^sub>n) 
                                   ** ([p + 3]\<^sub>n \<longmapsto> [stack_wait x]\<^sub>n)" 

lemma stack_node_equiv3_aux : "P ** Q ** R ** S \<equiv>\<^sub>S\<^sub>L R ** (P ** Q ** S)"
  using Astar_assoc_equiv2 Astar_commute_equiv assn_equiv_trans by blast

lemma stack_node_equiv3: "stack_node p x \<equiv>\<^sub>S\<^sub>L stack_node_top p x ** stack_node_top_frame p x"
  by (simp add: stack_node_def stack_node_top_def stack_node_top_frame_def stack_node_equiv3_aux)

lemma stack_node_read_top : " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
               v2 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>stop\<rbrakk>
            {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_top x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_top p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node_top_frame p x)"
         and Qa = "(stack_node_top p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_top x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
          ** (stack_node_top_frame p x)" in safe_assn_equiv)
  using assn_equiv_def stack_node_equiv3 apply auto[1]
  using assn_equiv_def stack_node_equiv3 apply auto[1]
  apply (rule rule_frame, simp add: stack_node_top_def stack_p_top_def)  
  apply (metis (mono_tags, lifting) Num.add_2_eq_Suc' Un_iff fvE.simps(1) fvE.simps(2) 
   rule_read_var_offn singletonD sup_bot.right_neutral)
  by (simp add: stack_node_top_frame_def)

lemma stack_node_read_top1 : " \<lbrakk>v1 \<noteq> v3; v2 \<noteq> v3; v1 \<notin> fvAs \<Gamma>; v3 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
               v3 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>stop\<rbrakk>
            {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v3]\<^sub>v =\<^sub>b [stack_top x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node p x  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
         and Qa = "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v3]\<^sub>v =\<^sub>b [stack_top x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
          ** (\<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
    apply (rule_tac Q = "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
     apply (simp add: Apure_Astar_equiv assn_equiv_symmetry, simp add: assn_equiv_def)
  apply (rule_tac Q = "(stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v3]\<^sub>v =\<^sub>b [stack_top x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L
    \<langle>[v2]\<^sub>v =\<^sub>b [q]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
    apply (simp add: Apure_Astar_equiv assn_equiv_symmetry, simp add: assn_equiv_def) apply auto[1]
  apply (rule rule_frame, simp add: stack_node_read_top)
  by (simp add: disjoint_def)

(* ===================== read wait ======================= *)
definition stack_node_wait :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_wait p x = [p + 3]\<^sub>n \<longmapsto> [stack_wait x]\<^sub>n"

definition stack_node_wait_frame :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node_wait_frame p x = ([p]\<^sub>n \<longmapsto> [stack_base x]\<^sub>n) ** ([p + 1]\<^sub>n \<longmapsto> [stack_next x]\<^sub>n) 
                                   ** ([p + 2]\<^sub>n \<longmapsto> [stack_top x]\<^sub>n)" 

lemma stack_node_equiv4: "stack_node p x \<equiv>\<^sub>S\<^sub>L stack_node_wait p x ** stack_node_wait_frame p x"
  by (simp add: stack_node_def stack_node_wait_def stack_node_wait_frame_def Astar_commute_equiv)

lemma stack_node_read_wait : " \<lbrakk>v1 \<noteq> v2; v1 \<notin> fvAs \<Gamma>; v2 \<notin> fvAs \<Gamma>\<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
               v2 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>swait\<rbrakk>
            {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_wait x]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_wait p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node_wait_frame p x)"
         and Qa = "(stack_node_wait p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [stack_wait x]\<^sub>n\<rangle>\<^sub>S\<^sub>L) 
          ** (stack_node_wait_frame p x)" in safe_assn_equiv)
  using assn_equiv_def stack_node_equiv4 apply auto[1]
  using assn_equiv_def stack_node_equiv4 apply auto[1]
  apply (rule rule_frame, simp add: stack_node_wait_def stack_p_wait_def)  
  apply (metis (mono_tags, lifting)  Un_iff fvE.simps(1) fvE.simps(2) 
   rule_read_var_offn singletonD sup_bot.right_neutral)
  by (simp add: stack_node_wait_frame_def)

(* ===================== write wait ===========================*)
lemma stack_node_write_wait_frame_equiv : "stack_node_wait_frame p (x:=\<^sub>w\<^sub>a w) \<equiv>\<^sub>S\<^sub>L stack_node_wait_frame p x"
  by (simp add: stack_node_wait_frame_def, simp add: upstack_wait_def stack_top_def stack_base_def
      stack_next_def stack_wait_def assn_equiv_reflex)

lemma stack_node_write_wait : "  v1 \<notin> fvAs \<Gamma> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [w]\<^sub>n
            {stack_node p (x:=\<^sub>w\<^sub>a w) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_wait p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node_wait_frame p x)"
         and Qa = "(stack_node_wait p (x:=\<^sub>w\<^sub>a w) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L ) ** (stack_node_wait_frame p x)" in 
        safe_assn_equiv)
    apply (metis Astar_commute_equiv assn_equiv_conj_Apure assn_equiv_symmetry assn_equiv_trans 
    stack_node_def stack_node_wait_def stack_node_wait_frame_def)
  apply (rule_tac Q = "(stack_node_wait p (x :=\<^sub>w\<^sub>a w) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** stack_node_wait_frame p 
  (x :=\<^sub>w\<^sub>a w)" in assn_equiv_trans)
  apply (simp add: assn_equiv_cong_star assn_equiv_reflex assn_equiv_symmetry stack_node_write_wait_frame_equiv)
  apply (metis Astar_commute_equiv assn_equiv_conj_Apure assn_equiv_symmetry assn_equiv_trans 
    stack_node_def stack_node_wait_def stack_node_wait_frame_def)
  by (rule rule_frame, simp add: stack_p_wait_def stack_node_wait_def upstack_wait_def 
      stack_wait_def rule_write_var_offn, simp)

lemma stack_node_write_wait_with_var : "  v1 \<notin> fvAs \<Gamma> \<Longrightarrow>
             \<Gamma> \<turnstile> {stack_node p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [w]\<^sub>n\<rangle>\<^sub>S\<^sub>L }
                \<lbrakk>[v1]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [v2]\<^sub>v
            {stack_node p (x:=\<^sub>w\<^sub>a w) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [w]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(stack_node_wait p x \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [w]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** 
  (stack_node_wait_frame p x)" and Qa = "(stack_node_wait p (x:=\<^sub>w\<^sub>a w) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L 
  \<langle>[v2]\<^sub>v =\<^sub>b [w]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (stack_node_wait_frame p x)" in safe_assn_equiv)
    apply (simp add: assn_equiv_def) using assn_equiv_def stack_node_equiv4 apply auto[1]
  apply (rule_tac Q = "(stack_node_wait p (x :=\<^sub>w\<^sub>a w) ** stack_node_wait_frame p x) 
  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [w]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
    apply (simp add: assn_equiv_def) apply auto[1]
   apply (rule assn_equiv_cong_conj, rule_tac Q = "stack_node_wait p (x :=\<^sub>w\<^sub>a w) ** 
   stack_node_wait_frame p (x :=\<^sub>w\<^sub>a w)" in assn_equiv_trans)
     apply (rule assn_equiv_cong_star, simp add: assn_equiv_reflex)
     apply (simp add: assn_equiv_symmetry stack_node_write_wait_frame_equiv)
    apply (simp add: assn_equiv_symmetry stack_node_equiv4, simp add: assn_equiv_reflex)
  apply (rule rule_frame, simp add: stack_node_wait_def stack_p_wait_def)
   by (simp add: upstack_wait_def stack_wait_def rule_write_var_offn2, simp)

(* ===================== buf read & update ====================*)
lemma read_buf_with_var : "\<lbrakk>v2 \<noteq> v1 \<and> v2 \<notin> fvAs \<Gamma>; n \<ge> b \<and> n < t \<rbrakk> \<Longrightarrow>
                  \<Gamma> \<turnstile> {(buf b t xs)  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                      v2 :=\<^sub>C \<lbrakk>[v1]\<^sub>v\<rbrakk>
                      {(buf b t xs)  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [xs ! (n - b)]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (induct xs arbitrary: b, simp add: CSL_def)
  apply (case_tac "b = n", clarsimp)
  apply (rule_tac Pa = "([n]\<^sub>n \<longmapsto> [a]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** buf (Suc n) t xs" and Qa = "
  ([n]\<^sub>n \<longmapsto> [a]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [a]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** buf (Suc n) t xs" in safe_assn_equiv)
  using assn_equiv_def apply auto[1] using assn_equiv_def apply auto[1]
   apply (rule rule_frame, rule rule_read_var, simp, simp add: fvA_buf, clarsimp)
  apply (rule_tac Pa = "[b]\<^sub>n \<longmapsto> [a]\<^sub>n ** (buf (Suc b) t xs \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" and Qa = " [b]\<^sub>n \<longmapsto> 
  [a]\<^sub>n ** (buf (Suc b) t xs \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[v2]\<^sub>v =\<^sub>b [xs ! (n - Suc b)]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in safe_assn_equiv)
  using assn_equiv_def apply auto[1] using assn_equiv_def apply auto[1]
  apply (drule_tac a = "Suc b" in mall_impD) apply linarith
  by (rule rule_frame1, simp_all)

lemma update_buf_with_var : " n \<ge> b \<and> n < t \<Longrightarrow>
           \<Gamma> \<turnstile> { (buf b t xs)  \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L }
              \<lbrakk>[v1]\<^sub>v\<rbrakk> :=\<^sub>C [k]\<^sub>n
            {buf b t (xs[(n - b) := k]) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (induct xs arbitrary: b, simp add: CSL_def) 
  apply (case_tac "b = n", clarsimp)
  apply (rule_tac Pa = "([n]\<^sub>n \<longmapsto> [a]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** buf (Suc n) t xs" and Qa = "
  ([n]\<^sub>n \<longmapsto> [k]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** buf (Suc n) t xs" in safe_assn_equiv)
  using assn_equiv_def apply auto[1] using assn_equiv_def apply auto[1]
   apply (rule rule_frame, rule rule_write_var, simp)
  apply (rule_tac Pa = "[b]\<^sub>n \<longmapsto> [a]\<^sub>n ** (buf (Suc b) t xs \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" and Qa = " [b]\<^sub>n \<longmapsto> 
  [a]\<^sub>n ** (buf (Suc b) t (xs[(n - Suc b) := k]) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in safe_assn_equiv)
  using assn_equiv_def apply auto[1]  
   apply (rule_tac Q = "(buf b t (a # xs[n - Suc b := k]) \<and>\<^sub>S\<^sub>L \<langle>[v1]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L)" in assn_equiv_trans)
  using assn_equiv_def apply auto[1] 
   apply (metis Suc_diff_Suc assn_equiv_reflex le_neq_implies_less list_update_code(3))
  apply (drule_tac a = "Suc b" in mall_impD) apply linarith
  by (rule rule_frame1, simp_all)

(* ======================  rule for stm ======================== *)
definition stm_while_inv :: "assn \<Rightarrow> assn \<Rightarrow> nat \<Rightarrow> assn"
  where "stm_while_inv P Q t = ((P \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<or>\<^sub>S\<^sub>L (Q \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [t\<diamondop>FLAG]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L))"

definition stm1_post :: "assn \<Rightarrow> nat \<Rightarrow> assn"
  where "stm1_post P t = (P \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition stm2_pre1 :: " assn \<Rightarrow> nat \<Rightarrow> assn"
  where "stm2_pre1 P t = stm1_post P t ** ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n)"

definition stm2_pre2 :: "assn \<Rightarrow> nat \<Rightarrow> assn"
  where "stm2_pre2 P t = stm1_post P t ** (Aexcur inv_cur1)"

definition stm2_post1 :: " assn \<Rightarrow> nat \<Rightarrow> assn"
  where "stm2_post1 P t = stm1_post P t ** ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [NULL]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition stm2_post2 :: " assn \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "stm2_post2 P t p ta = stm1_post P t ** (([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L)
        ** is_cur p ta)"

definition stm3_pre :: " assn \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "stm3_pre P t p ta = P ** (inv_cur1 t ta)"

lemma stm3_pre_implies : "(stm2_post2 P t p ta \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [t]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<sqsubseteq> stm3_pre P t p ta"
  apply (rule_tac Q = "(P ** (([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** is_cur p ta))
  \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>CUR_RUNNING]\<^sub>v =\<^sub>b [t]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in implies_trans)
   apply (simp add: stm2_post2_def stm1_post_def implies_def) apply metis
  apply (case_tac "p = t", simp add: stm3_pre_def inv_cur1_def implies_def) apply auto[1]
  apply (simp add: implies_def) by auto

definition stm3_post :: " assn \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "stm3_post P t p ta = (P \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (inv_cur1 t ta)"

definition stm4_pre :: " assn \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "stm4_pre P t p ta = P ** (inv_cur1 t ta) ** (\<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"

definition stm4_post :: " assn \<Rightarrow> nat  \<Rightarrow> assn"
  where "stm4_post Q t  = Q ** inv_cur ** (\<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"

lemma stm3_post_equiv : "stm3_post P t p ta \<equiv>\<^sub>S\<^sub>L stm4_pre P t p ta"
  apply (simp add: stm3_post_def stm4_pre_def assn_equiv_def) by auto

lemma stm4_post_implies : "stm4_post Q t  \<sqsubseteq> stm_while_inv P Q t ** inv_cur"
  apply (rule_tac Q = "(Q \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [1]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** inv_cur" in implies_trans)
   apply (simp add: stm4_post_def implies_def)
  apply (rule implies_star, simp add: stm_while_inv_def implies_def)
  by (simp add: implies_def)

lemma rule_inv_cur: "\<forall>p t. \<Gamma> \<turnstile> {P ** inv_cur1 p t} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {P ** (Aexcur inv_cur1)} C {Q}"
  apply (simp add: CSL_def) by blast

lemma rule_stm : "\<lbrakk> disjoint ({t \<diamondop> FLAG}) (wrC C); t\<diamondop>FLAG \<notin> fvAs \<Gamma> \<union> fvA P; t \<noteq> NULL;
                    t\<diamondop>CUR_RUNNING \<notin> fvAs \<Gamma>;   t\<diamondop>CUR_RUNNING \<notin> fvA P; \<Gamma> Cur = inv_cur; 
                    \<forall>ta. \<Gamma> \<turnstile> { P ** inv_cur1 t ta} C { Q ** inv_cur}  \<rbrakk> \<Longrightarrow> 
                    \<Gamma> \<turnstile> {P} t \<^enum> C {Q}"
  apply (simp add: stm_def)
  apply (rule_tac Q = "P \<and>\<^sub>S\<^sub>L \<langle>[t\<diamondop>FLAG]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in rule_seq)
   apply (rule rule_assign_num1, simp)
  apply (rule_tac P = "stm_while_inv P Q t" and Q = "(stm_while_inv P Q t) \<and>\<^sub>S\<^sub>L \<langle>\<not>\<^sub>b [t\<diamondop>FLAG]\<^sub>v =\<^sub>b [0]\<^sub>n\<rangle>\<^sub>S\<^sub>L"
  in rule_conseq)
    apply (rule rule_while, rule rule_with_true, simp)
    defer
    apply (simp add: stm_while_inv_def implies_def)
   apply (simp add: stm_while_inv_def implies_def) apply auto[1]
  apply (rule_tac Pa = "(stm2_pre1 P t \<or>\<^sub>S\<^sub>L stm2_pre2 P t)" and Qa = "stm_while_inv P Q t ** inv_cur" 
   in safe_assn_equiv)
    apply (rule_tac Q = "stm1_post P t ** inv_cur" in assn_equiv_trans)
     apply (simp add: stm2_pre1_def stm2_pre2_def inv_cur_def)
  using Astar_disj_dist assn_equiv_symmetry apply blast
    apply (rule assn_equiv_cong_star, simp add: stm1_post_def stm_while_inv_def assn_equiv_def) apply auto[1]
    apply (simp add: assn_equiv_reflex, simp add: assn_equiv_reflex)
  apply (rule rule_disj')
   apply (rule_tac Q = "stm2_post1 P t" in rule_seq, simp add: stm2_pre1_def stm2_post1_def)
    apply (rule rule_frame1, rule rule_read, simp add: Thread_Local_def)
    apply (simp add: stm1_post_def disjoint_def, simp add: Thread_Local_def)
   apply (rule rule_if, simp add: stm2_post1_def CSL_def) apply linarith
  apply (rule_tac P = "stm1_post P t ** ([A_Cur]\<^sub>v \<longmapsto> [K_NO_WAIT]\<^sub>n)" and Q = "stm1_post P t ** 
  ([A_Cur]\<^sub>v \<longmapsto> [K_NO_WAIT]\<^sub>n)" in rule_conseq, simp add: rule_skip)
    apply (simp add: implies_def stm2_post1_def) apply auto[1]
   apply (rule implies_star, simp add: stm1_post_def stm_while_inv_def implies_def)
   apply (simp add: implies_def inv_cur_def)
  apply (simp add: stm2_pre2_def, rule rule_inv_cur, intro allI)
  apply (rule_tac Q = "stm2_post2 P t p ta" in rule_seq, simp add: inv_cur1_def stm2_post2_def)
   apply (rule rule_frame1, rule rule_frame, rule rule_read)
     apply (simp add: Thread_Local_def, simp add: fvA_is_cur, simp add: stm1_post_def)
   apply (simp add: disjoint_def, simp add: Thread_Local_def)
  apply (rule rule_if, rule_tac Q = "stm3_post P t p ta" in rule_seq)
    apply (rule_tac P = "stm3_pre P t p ta" and Q = "stm3_post P t p ta" in rule_conseq)
      apply (simp add: stm3_pre_def stm3_post_def, rule rule_frame)
       apply (rule rule_assign_num1, simp, simp add: inv_cur1_def fvA_is_cur disjoint_def)
      apply (simp add: Thread_Local_def, simp add: stm3_pre_implies, simp add: implies_def)
   apply (rule_tac P = "stm4_pre P t p ta" and Q = "stm4_post Q t" in rule_conseq)
     apply (simp add: stm4_pre_def stm4_post_def, rule rule_frame) apply auto[1]
     apply (simp) using equiv_implies stm3_post_equiv apply blast
  using stm4_post_implies apply blast
  apply (rule_tac P = "stm1_post P t ** (inv_cur1 p ta)" and Q = "stm1_post P t ** (inv_cur1 p ta)"
  in rule_conseq, simp add: rule_skip)
   apply (simp add: stm2_post2_def stm1_post_def inv_cur1_def implies_def) apply auto[1]
  apply (rule implies_star, simp add: stm1_post_def stm_while_inv_def implies_def)
  using inv_cur_implies2 by blast

lemma rule_stm' : "\<lbrakk> disjoint ({t \<diamondop> FLAG}) (wrC C); t\<diamondop>FLAG \<notin> fvAs \<Gamma> \<union> fvA P; t \<noteq> NULL;
                    t\<diamondop>CUR_RUNNING \<notin> fvAs \<Gamma>;   t\<diamondop>CUR_RUNNING \<notin> fvA P; \<Gamma> Cur = inv_cur; 
                     \<Gamma> \<turnstile> { P } C { Q}; A_Cur \<notin> wrC C  \<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> {P} t \<^enum> C {Q}"
  apply (rule rule_stm, simp_all, clarsimp)
  apply (rule_tac P = "P ** inv_cur1 t (a, aa, b)" and Q = "Q ** inv_cur1 t (a, aa, b)" in rule_conseq)
    apply (rule rule_frame, simp, simp add: inv_cur1_def disjoint_def fvA_is_cur)
   apply (simp add: implies_def)
  apply (rule implies_star, simp add: implies_def)
  using inv_cur_implies2 by blast


lemma rule_stm_stack : "\<lbrakk>fvAs \<Gamma> = {}; disjoint ({t \<diamondop> FLAG}) (wrC C); t\<diamondop>FLAG \<notin> fvA P; t \<noteq> NULL; 
    t\<diamondop>CUR_RUNNING \<notin> fvA P; \<forall>ta. \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) 
    \<turnstile> { P ** inv_cur1 t ta} C { Q ** inv_cur}\<rbrakk>  \<Longrightarrow> 
    \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile> {P} t \<^enum> C {Q}"
  apply (rule rule_stm, simp_all, simp_all add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
  by (simp_all add: Thread_Local_def)

lemma rule_stm_stack' : "\<lbrakk>fvAs \<Gamma> = {}; disjoint ({t \<diamondop> FLAG}) (wrC C); t\<diamondop>FLAG \<notin> fvA P; t \<noteq> NULL; 
    t\<diamondop>CUR_RUNNING \<notin> fvA P;  \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) 
    \<turnstile> { P} C { Q} ; A_Cur \<notin> wrC C\<rbrakk>  \<Longrightarrow> 
    \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile> {P} t \<^enum> C {Q}"
  apply (rule rule_stm', simp_all, simp_all add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq)
  by (simp_all add: Thread_Local_def)

end