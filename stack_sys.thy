theory stack_sys
  imports func_cor_pop func_cor_push func_cor_scheduler Event_Safe
begin

type_synonym Thread_Sys_Param = "(tid \<times> nat \<times> nat)"

definition Empty_Env :: "rname \<Rightarrow> assn" ("\<Gamma>\<^sub>e\<^sub>m\<^sub>p")
  where "Empty_Env = (\<lambda>x. Aemp)"


definition Scheduler_Sys :: "resys"
  where "Scheduler_Sys = ([], EvtSys {([], (BasicEvent ([True]\<^sub>b, scheduler)))})"

definition Thread_Sys :: "tid \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> resys"
  where "Thread_Sys t d time = ([], EvtSys {([], (BasicEvent ([t \<noteq> NULL]\<^sub>b, stack_push t d))), 
                     ([], (BasicEvent ([t \<noteq> NULL]\<^sub>b, stack_pop t time)))})"

definition mk_Thread_Sys :: " Thread_Sys_Param \<Rightarrow> resys"
  where "mk_Thread_Sys p = Thread_Sys (fst p) (fst (snd p)) (snd (snd p))"

definition Thread_Sys_List :: "Thread_Sys_Param list \<Rightarrow> paresys"
  where "Thread_Sys_List l = map mk_Thread_Sys l"

definition Stack_Pes :: "Thread_Sys_Param list \<Rightarrow> paresys"
  where "Stack_Pes l =  Scheduler_Sys # (Thread_Sys_List l)"


lemma safe_Scheduler_Sys : "fvAs \<Gamma> = {} \<Longrightarrow> \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) 
      \<turnstile>\<^sub>r\<^sub>e\<^sub>s {Aemp} Scheduler_Sys {Aemp}"
  apply (simp add: Scheduler_Sys_def, rule rule_res_empty)
  apply (rule rule_EvtSys', simp, rule rule_re_empty)
  by (rule rule_BasicEvt_true, drule safe_scheduler, simp)

lemma safe_Thread_Sys : "fvAs \<Gamma> = {} \<Longrightarrow> \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) 
      \<turnstile>\<^sub>r\<^sub>e\<^sub>s  {Aemp} Thread_Sys t d time {Aemp}"
  apply (simp add: Thread_Sys_def)
  apply (rule rule_res_empty, rule rule_EvtSys', simp, rule conjI)
   apply (rule rule_re_empty, rule rule_BasicEvt, drule_tac t = t and d = d in safe_push, simp)
  apply (rule rule_re_empty, rule rule_BasicEvt, drule_tac t = t and timeout = time in safe_pop, simp)
  done

lemma safe_stack_rpes_aux : 
  "\<lbrakk> \<Gamma>(Cur := inv_cur, Readyq := inv_readyq, Stack := inv_stack) \<turnstile>\<^sub>p\<^sub>e\<^sub>s {Aemp} pes {Aemp} ; 
         {A_Cur, A_Readyq, A_Stack} \<inter> wrPEsv pes = {}\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s 
  {inv_cur ** inv_readyq ** inv_stack} ([Cur, Readyq, Stack], pes) {inv_cur ** inv_readyq ** inv_stack}"
  apply (rule_tac upd = "[(Cur, inv_cur), (Readyq, inv_readyq), (Stack, inv_stack)]" in rule_rpes', simp_all)
   apply (simp add: fvA_inv_cur fvA_inv_readyq fvA_inv_stack disjoint_def)
  by (meson Aemp_equiv Astar_assoc_equiv Astar_commute_equiv assn_equiv_symmetry assn_equiv_trans)

lemma disjoint_Scheduler_Env : " disjoint {A_Cur, A_Readyq, A_Stack} (wrREsv Scheduler_Sys)"
  apply (simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq disjoint_def)
  by (simp add: Scheduler_Sys_def stm_def wrREsv_def wrREv_def sched_local_def)

lemma disjoint_Scheduler_Env1 : "A_Cur \<notin> wrREsv Scheduler_Sys \<and> A_Readyq \<notin> wrREsv Scheduler_Sys \<and> 
                                 A_Stack \<notin> wrREsv Scheduler_Sys"
  by (meson disjoint_Scheduler_Env disjoint_def disjoint_insert(1) disjoint_search(1))
lemma disjoint_Thread_Env : "disjoint {A_Cur, A_Readyq, A_Stack} (wrREsv (Thread_Sys t d time))"
  apply (simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_cur fvA_inv_readyq disjoint_def)
  apply (simp add: Thread_Sys_def stack_pop_def stack_push_def stm_def)
  sorry

lemma disjoint_Thread_Scheduler : "disjoint (fvREsv Scheduler_Sys) (wrREsv (Thread_Sys t d time))"
  apply (simp add: Scheduler_Sys_def stm_def fvREsv_def fvREv_def tcb_p_next_def tcb_p_state_def)
  apply (simp add: Thread_Sys_def stack_pop_def stack_push_def stm_def)
  apply (simp add:  wrREsv_def wrREv_def disjoint_def)
  sorry


lemma disjoint_Scheduler_Thread : "disjoint (fvREsv (Thread_Sys t d time)) (wrREsv Scheduler_Sys)"
  sorry

lemma disjoint_Thread_Thread : "t1 \<noteq> t2 \<Longrightarrow> disjoint (fvREsv (Thread_Sys t1 d1 time1)) 
                                                      (wrREsv (Thread_Sys t2 d2 time2))"
  sorry


lemma distinct_pes_aux : "\<forall>x \<in> set pes. {A_Cur, A_Readyq, A_Stack} \<inter> wrREsv x = {} \<Longrightarrow> 
                        {A_Cur, A_Readyq, A_Stack} \<inter> wrPEsv pes = {}"
  by (induct pes, simp, simp add: wrPEsv.cases)

lemma "\<lbrakk>distinct (map fst l); fvAs \<Gamma> = {}; pes = Stack_Pes l \<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^sub>r\<^sub>p\<^sub>e\<^sub>s {inv_cur ** inv_readyq ** inv_stack} ([Cur, Readyq, Stack], pes) 
               {inv_cur ** inv_readyq ** inv_stack}"
  apply (rule safe_stack_rpes_aux, rule rule_pes', clarsimp)
    apply (case_tac k, simp add: Stack_Pes_def, simp add: safe_Scheduler_Sys)
    apply (simp add: Stack_Pes_def Thread_Sys_List_def mk_Thread_Sys_def safe_Thread_Sys)
   apply (clarsimp, rule conjI)
    apply (case_tac k1, case_tac k2, simp, simp add: Stack_Pes_def)
     apply (simp add: Thread_Sys_List_def mk_Thread_Sys_def disjoint_Thread_Scheduler)
    apply (case_tac k2, simp add: Stack_Pes_def)
     apply (simp add: Thread_Sys_List_def mk_Thread_Sys_def disjoint_Scheduler_Thread)
    apply (simp add: Stack_Pes_def  Thread_Sys_List_def mk_Thread_Sys_def)
  apply (rule disjoint_Thread_Thread)
  using nth_eq_iff_index_eq apply fastforce
   apply (case_tac k2, simp add: Stack_Pes_def fvA_Gamma2 fvA_inv_stack fvA_inv_readyq)
    apply (simp add: fvA_inv_cur)  using disjoint_Scheduler_Env apply auto[1]
   apply (simp add: Stack_Pes_def Thread_Sys_List_def mk_Thread_Sys_def)
   apply (simp add: fvA_Gamma2 fvA_inv_stack fvA_inv_readyq fvA_inv_cur)
  using disjoint_Thread_Env apply fastforce
  sorry
