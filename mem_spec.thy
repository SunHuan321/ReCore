theory mem_spec
  imports CSLsound test 
begin

(* constant definition *)
abbreviation "NULL \<equiv> 0"

abbreviation "BLOCKED \<equiv>  0 :: nat"
abbreviation "READY \<equiv>  1 :: nat"
abbreviation "RUNNING \<equiv>  2 :: nat"

abbreviation "K_NO_WAIT \<equiv> 0 :: nat"

abbreviation "EBUSY \<equiv> 1 :: nat"
abbreviation "EAGAIN \<equiv> 2 :: nat"
abbreviation "ENOMEM \<equiv> 3 :: nat"

(* definition of data structure *)
type_synonym tcb = "nat \<times> nat \<times> nat \<times> nat"
type_synonym tcbs = "tcb list"
type_synonym buf = "nat list"
type_synonym stack = "nat \<times> nat \<times> nat \<times> nat \<times> buf \<times> tcbs"
type_synonym tid = "nat"

(* pointer for data structure *)
definition stack_p_base :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>sbase)")
  where "stack_p_base p = p"

definition stack_p_next :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>snext)")
  where "stack_p_next p = (p +\<^sub>e ([1]\<^sub>n))"

definition stack_p_top :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>stop)")
  where "stack_p_top p = (p +\<^sub>e ([2]\<^sub>n))"

definition stack_p_wait :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>swaitq)")
  where "stack_p_wait p = (p +\<^sub>e ([3]\<^sub>n))"

definition tcb_p_state :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tstate)")
  where "tcb_p_state p = p"

definition tcb_p_pri :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tpriority)")
  where "tcb_p_pri p = (p +\<^sub>e ([1]\<^sub>n))"

definition tcb_p_next :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tnext)")
  where "tcb_p_next p = (p +\<^sub>e ([2]\<^sub>n))"

definition tcb_p_data :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tdata)")
  where "tcb_p_data p = (p +\<^sub>e ([3]\<^sub>n))"

(* resource name *)
type_synonym StackId = "string"
type_synonym Stack_Pool = "StackId list"
abbreviation "CUR \<equiv> ''cur''"
abbreviation "READYQ \<equiv> ''ready_q''"

(* varname spec *)
type_synonym Thread = var
                                            
definition p_stack :: "StackId \<Rightarrow> var"  ("(_\<^sup>s)")
  where "p_stack sId \<equiv> ''p_'' @ sId "

(* local variable definition *)

definition Thread_Local :: "Thread \<Rightarrow> var \<Rightarrow> var" ("(_\<diamondop>_)")
  where "Thread_Local t v = t @ v"

abbreviation "BASE \<equiv> ''base''"
abbreviation "NEXT \<equiv> ''next''"
abbreviation "TOP \<equiv> ''top''"
abbreviation "DATA \<equiv> ''data''"
abbreviation "RET \<equiv> ''ret''" 
abbreviation "FIRST_PENDING_THREAD \<equiv> ''first_pending_thread''"
abbreviation "WAITQ \<equiv> ''waitq''"
abbreviation "END \<equiv> ''END''"
abbreviation "AUX \<equiv> ''AUX''"

(* expression name *)
abbreviation "CUR_THREAD \<equiv> ''cur_thread''"
abbreviation "P_READYQ \<equiv> ''p_readyq'' "


definition stm :: "Thread \<Rightarrow> cmd \<Rightarrow> cmd"  ("_ \<^enum> _" [0,0] 61)
  where "stm t c = WITH CUR WHEN ([t]\<^sub>v) =\<^sub>b ([CUR_THREAD]\<^sub>v) DO c OD"

definition z_pend_curr :: "cmd"
  where "z_pend_curr \<equiv> Cskip"

definition z_unpend_first_thread :: "cmd"
  where "z_unpend_first_thread \<equiv> Cskip"

definition z_ready_thread :: "cmd"
  where "z_ready_thread \<equiv> Cskip"

definition z_thread_return_value_set_with_data :: "cmd"
  where "z_thread_return_value_set_with_data \<equiv> Cskip"

definition z_reschedule :: "cmd"
  where "z_reschedule \<equiv> Cskip"

definition stack_push :: "Thread \<Rightarrow> StackId \<Rightarrow> nat \<Rightarrow> cmd"
  where
    "stack_push t sId data \<equiv> 
    (t \<^enum> (t \<diamondop> END) := ([0]\<^sub>n)) ;;
    WITH sId WHEN [True]\<^sub>b DO 
      (t \<^enum> (t \<diamondop> NEXT) := \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>snext)\<rbrakk>) ;;
      (t \<^enum> (t \<diamondop> TOP) := \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>stop)\<rbrakk>);;
      IF ([(t \<diamondop> NEXT)]\<^sub>v) =\<^sub>b ([(t \<diamondop> TOP)]\<^sub>v) THEN
        (t \<^enum> (t \<diamondop> RET) := ([ENOMEM]\<^sub>n)) ;;
        (t \<^enum> (t \<diamondop> END) := ([1]\<^sub>n))
      ELSE
        z_unpend_first_thread ;;
        IF ([t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v) =\<^sub>b ([NULL]\<^sub>n) THEN
          (t \<^enum> \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>snext)\<rbrakk> := ([data]\<^sub>n)) ;;
          (t \<^enum>  \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>snext)\<rbrakk> := ([(t \<diamondop> NEXT)]\<^sub>v) +\<^sub>e ([1]\<^sub>n))
        ELSE
          (t \<^enum> z_ready_thread) ;;
          (t \<^enum> z_thread_return_value_set_with_data) ;;
          (t \<^enum> z_reschedule)
        FI
       FI
    OD ;;
    IF ([t \<diamondop> END]\<^sub>v) =\<^sub>b ([0]\<^sub>n) THEN
      (t \<^enum> (t \<diamondop> RET) := ([0]\<^sub>n))
    ELSE
      Cskip
    FI"

definition stack_pop :: "Thread \<Rightarrow> StackId \<Rightarrow> nat \<Rightarrow> cmd"
  where
    "stack_pop t sId timeout \<equiv> 
    (t \<^enum> (t \<diamondop> END) := ([0]\<^sub>n)) ;;
    WITH sId WHEN [True]\<^sub>b DO 
       (t \<^enum> (t \<diamondop> NEXT) := \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>snext)\<rbrakk>)  ;;
       (t \<^enum> (t \<diamondop> BASE) := \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>sbase)\<rbrakk>) ;;
       IF ([(t \<diamondop> NEXT)]\<^sub>v) >\<^sub>b ([(t \<diamondop> BASE)]\<^sub>v) THEN
          (t \<^enum>  \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>snext)\<rbrakk> := ([(t \<diamondop> NEXT)]\<^sub>v) -\<^sub>e ([1]\<^sub>n));;
          (t \<^enum> (t \<diamondop> NEXT) := \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>snext)\<rbrakk>) ;;
          (t \<^enum>  (t \<diamondop> DATA) := \<lbrakk>([t \<diamondop> NEXT]\<^sub>v)\<rbrakk>) ;;
          (t \<^enum>  (t \<diamondop> RET) := ([0]\<^sub>n)) ;;
          (t \<^enum> (t \<diamondop> END) := ([1]\<^sub>n)) 
      ELSE
         IF [ timeout = K_NO_WAIT ]\<^sub>b THEN
           (t \<^enum>  (t \<diamondop> RET) := ([0]\<^sub>n)) ;;
           (t \<^enum> (t \<diamondop> END) := ([1]\<^sub>n)) 
         ELSE
           (t \<^enum> z_pend_curr) 
         FI
      FI     
    OD;;
    IF ([t \<diamondop> END]\<^sub>v) =\<^sub>b ([0]\<^sub>n)  THEN
      IF ([(t \<diamondop> RET)]\<^sub>v) =\<^sub>b ([EAGAIN]\<^sub>n) THEN
        Cskip
       ELSE
          (t \<^enum> (t \<diamondop> DATA) := \<lbrakk>([t]\<^sub>v\<Down>\<^sub>tdata)\<rbrakk>) ;;
          (t \<^enum> (t \<diamondop> RET) := ([0]\<^sub>n))
       FI
    ELSE  
      Cskip
    FI
"

definition z_pend_curr1 :: "Thread \<Rightarrow> StackId \<Rightarrow> cmd"
  where "z_pend_curr1 t sId \<equiv> 
      \<lbrakk>[t]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> := ([BLOCKED]\<^sub>n) ;;
      (t \<diamondop> WAITQ) := \<lbrakk>[sId\<^sup>s]\<^sub>v\<Down>\<^sub>swaitq\<rbrakk> ;;
      \<lbrakk>[t]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> := ([(t \<diamondop> WAITQ)]\<^sub>v) ;;
      \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>swaitq)\<rbrakk> := ([t]\<^sub>v)"

definition z_unpend_first_thread1 :: "Thread \<Rightarrow> StackId \<Rightarrow> cmd"
  where "z_unpend_first_thread1 t sId \<equiv>
      (t \<diamondop> FIRST_PENDING_THREAD) := \<lbrakk>[sId\<^sup>s]\<^sub>v\<Down>\<^sub>swaitq\<rbrakk> ;; 
      IF ([(t \<diamondop> FIRST_PENDING_THREAD)]\<^sub>v) =\<^sub>b ([NULL]\<^sub>n) THEN
        Cskip
      ELSE
        (t \<diamondop> AUX) := \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk>;;
        \<lbrakk>([sId\<^sup>s]\<^sub>v\<Down>\<^sub>swaitq)\<rbrakk> := ([t \<diamondop> AUX]\<^sub>v)
      FI
"


end