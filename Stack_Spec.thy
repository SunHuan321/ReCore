theory Stack_Spec
  imports Aux_for_CSL 
begin

type_synonym Thread_Sys_Param = "(tid \<times> nat \<times> nat)"

definition Empty_Env :: "rname \<Rightarrow> assn" ("\<Gamma>\<^sub>e\<^sub>m\<^sub>p")
  where "Empty_Env = (\<lambda>x. Aemp)"

lemma "fvAs \<Gamma>\<^sub>e\<^sub>m\<^sub>p = {}"
  by (simp add: fvAs_def Empty_Env_def)

fun string_of_digit :: "nat \<Rightarrow> string"
where
  "string_of_digit n =
    (if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')"

fun string_of_nat :: "nat \<Rightarrow> string"
  where
    "string_of_nat n = 
      (if n < 10 then (string_of_digit n) else
      string_of_nat (n div 10) @ (string_of_digit (n mod 10)))"

lemma "n1 \<noteq> n2 \<Longrightarrow> string_of_nat n1 \<noteq> string_of_nat n2"
  sorry

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
type_synonym tid = "nat"

(* address of data in each structure *)
definition stack_p_base :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>sbase)")
  where "stack_p_base p = p"

definition stack_p_next :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>snext)")
  where "stack_p_next p = p +\<^sub>e [1]\<^sub>n"

definition stack_p_top :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>stop)")
  where "stack_p_top p = p +\<^sub>e [2]\<^sub>n"

definition stack_p_wait :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>swait)")
  where "stack_p_wait p = p +\<^sub>e [3]\<^sub>n"

definition tcb_p_state :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tstate)")
  where "tcb_p_state p = p"

definition tcb_p_next :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tnext)")
  where "tcb_p_next p = p +\<^sub>e [1]\<^sub>n"

definition tcb_p_data :: "exp \<Rightarrow> exp" ("(_\<Down>\<^sub>tdata)")
  where "tcb_p_data p = p +\<^sub>e [2]\<^sub>n"

(* resource name *) 
abbreviation "Cur \<equiv> ''cur''"
abbreviation "Readyq \<equiv> ''ready_q''"
abbreviation "Stack \<equiv> '' stack ''"

(* resource invariant expression*)
abbreviation "A_Cur \<equiv> ''a_cur''"
abbreviation "A_Readyq \<equiv> ''a_readyq'' "
abbreviation "A_Stack \<equiv> ''a_stack''"


(* auxillary variable *)
abbreviation "CUR_THREAD \<equiv> ''cur_thread''"
abbreviation "READY_LIST \<equiv> ''ready_list''"
(* local variable definition *)

definition Thread_Local :: "tid \<Rightarrow> var \<Rightarrow> var" ("(_\<diamondop>_)")
  where "Thread_Local t v = ((string_of_nat) t @ v)"

abbreviation "ADDR \<equiv> ''addr''"
abbreviation "BASE \<equiv> ''base''"
abbreviation "NEXT \<equiv> ''next''"
abbreviation "TOP \<equiv> ''top''"
abbreviation "DATA \<equiv> ''data''"
abbreviation "RET \<equiv> ''ret''" 
abbreviation "FIRST_PENDING_THREAD \<equiv> ''first_pending_thread''"
abbreviation "WAITQ \<equiv> ''waitq''"
abbreviation "END \<equiv> ''end''"
abbreviation "AUX \<equiv> ''aux''"
abbreviation "FIRST_READY \<equiv> ''first_ready''"
abbreviation "SECOND_READY \<equiv> ''second_ready''"
abbreviation "CUR_RUNNING \<equiv> ''cur_running''"
abbreviation "FLAG \<equiv> ''flag''"

definition sched_local :: "var \<Rightarrow> var" ("sched \<diamondop>_")
  where "sched_local v = ''sched'' @ v"

(* expression name *)
definition stm :: "tid \<Rightarrow> cmd \<Rightarrow> cmd"  ("_ \<^enum> _" [0,0] 61)
  where "stm t c = 
        (t \<diamondop> FLAG) :=\<^sub>C [0]\<^sub>n ;;
        WHILE [t \<diamondop> FLAG]\<^sub>v =\<^sub>b [0]\<^sub>n DO
          WITH Cur WHEN [True]\<^sub>b DO
            (t \<diamondop> CUR_RUNNING) :=\<^sub>C \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> ;;
            IF [t \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [t]\<^sub>n THEN
              (t \<diamondop> FLAG) :=\<^sub>C [1]\<^sub>n ;;
              c
            ELSE
              Cskip
            FI
          OD
        OD"


definition stack_push :: "tid  \<Rightarrow> nat \<Rightarrow> cmd"
  where
    "stack_push t  data \<equiv> 
    (t \<^enum> (t \<diamondop> END) :=\<^sub>C [0]\<^sub>n) ;;                  
    WITH Stack WHEN [True]\<^sub>b DO 
      (t \<^enum> (t \<diamondop> ADDR) :=\<^sub>C \<lbrakk>[A_Stack]\<^sub>v\<rbrakk>) ;;
      (t \<^enum> (t \<diamondop> NEXT) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
      (t \<^enum> (t \<diamondop> TOP) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>stop\<rbrakk>) ;;
      IF [t \<diamondop> NEXT]\<^sub>v =\<^sub>b [t \<diamondop> TOP]\<^sub>v THEN
        (t \<^enum> (t \<diamondop> RET) :=\<^sub>C [ENOMEM]\<^sub>n) ;;
        (t \<^enum> (t \<diamondop> END) :=\<^sub>C [1]\<^sub>n)
      ELSE
        (t \<^enum>  
           (
              (t \<diamondop> FIRST_PENDING_THREAD) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> ;;
              IF [t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [NULL]\<^sub>n THEN
                Cskip
              ELSE
                (t \<diamondop> WAITQ) :=\<^sub>C \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> ;;
                \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [t \<diamondop> WAITQ]\<^sub>v
              FI
            )
        ) ;;
        
        IF [t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v =\<^sub>b [NULL]\<^sub>n THEN
          (t \<^enum> \<lbrakk>[t \<diamondop> NEXT]\<^sub>v\<rbrakk> :=\<^sub>C [data]\<^sub>n) ;;
          (t \<^enum>  \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk> :=\<^sub>C [t \<diamondop> NEXT]\<^sub>v +\<^sub>e [1]\<^sub>n)
        ELSE
       
          (t \<^enum> 
            ( 
              \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [READY]\<^sub>n ;;
              \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tdata\<rbrakk> :=\<^sub>C [data]\<^sub>n ;;
              WITH Readyq WHEN [True]\<^sub>b DO
                 (t \<diamondop> FIRST_READY) :=\<^sub>C \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> ;; 
                 \<lbrakk>[t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [t \<diamondop> FIRST_READY]\<^sub>v ;; 
                 \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> :=\<^sub>C [t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v 
              OD
            )
          ) 
        
        FI
       FI
    OD ;;
    IF [t \<diamondop> END]\<^sub>v =\<^sub>b [0]\<^sub>n THEN
      (t \<^enum> (t \<diamondop> RET) :=\<^sub>C [0]\<^sub>n)
    ELSE
      Cskip
    FI"

definition stack_pop :: "tid  \<Rightarrow> nat \<Rightarrow> cmd"
  where
    "stack_pop t timeout \<equiv> 
      (t \<^enum> (t \<diamondop> END) :=\<^sub>C [0]\<^sub>n) ;;
      WITH Stack WHEN [True]\<^sub>b DO 
         (t \<^enum> (t \<diamondop> ADDR) :=\<^sub>C \<lbrakk>[A_Stack]\<^sub>v\<rbrakk>) ;;
         (t \<^enum> (t \<diamondop> NEXT) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
         (t \<^enum> (t \<diamondop> BASE) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>sbase\<rbrakk>) ;;
         IF [(t \<diamondop> NEXT)]\<^sub>v >\<^sub>b ([t \<diamondop> BASE]\<^sub>v) THEN
            (t \<^enum> \<lbrakk>([t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext)\<rbrakk> :=\<^sub>C [t \<diamondop> NEXT]\<^sub>v -\<^sub>e [1]\<^sub>n);;
            (t \<^enum> (t \<diamondop> NEXT) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>snext\<rbrakk>) ;;
            (t \<^enum> (t \<diamondop> DATA) :=\<^sub>C \<lbrakk>[t \<diamondop> NEXT]\<^sub>v\<rbrakk>) ;;
            (t \<^enum> (t \<diamondop> RET) :=\<^sub>C [0]\<^sub>n) ;;
            (t \<^enum> (t \<diamondop> END) :=\<^sub>C [1]\<^sub>n) 
        ELSE
           IF [timeout = K_NO_WAIT ]\<^sub>b THEN
             (t \<^enum> (t \<diamondop> RET) :=\<^sub>C ([EBUSY]\<^sub>n)) ;;
             (t \<^enum> (t \<diamondop> END) :=\<^sub>C ([1]\<^sub>n)) 
           ELSE
            
             (t \<^enum> 
                (
                  (t \<diamondop> FIRST_PENDING_THREAD) :=\<^sub>C \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> ;;                  
                  \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [t \<diamondop> FIRST_PENDING_THREAD]\<^sub>v ;;
                  \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [BLOCKED]\<^sub>n ;;
                  \<lbrakk>[t \<diamondop> ADDR]\<^sub>v\<Down>\<^sub>swait\<rbrakk> :=\<^sub>C [t]\<^sub>n ;;
                  \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> :=\<^sub>C [NULL]\<^sub>n 
                )
              )
            
           FI
        FI     
      OD;;
      IF [t \<diamondop> END]\<^sub>v =\<^sub>b [0]\<^sub>n  THEN
        IF [t \<diamondop> RET]\<^sub>v =\<^sub>b [EAGAIN]\<^sub>n THEN
          Cskip
         ELSE
            (t \<^enum> (t \<diamondop> DATA) :=\<^sub>C \<lbrakk>[t]\<^sub>n\<Down>\<^sub>tdata\<rbrakk>) ;;
            (t \<^enum> (t \<diamondop> RET) :=\<^sub>C [0]\<^sub>n)
         FI
      ELSE  
        Cskip
      FI
"

abbreviation "scheduler \<equiv>
    WITH Readyq  WHEN [True]\<^sub>b DO 
        sched \<diamondop> FIRST_READY :=\<^sub>C \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> ;; 
        IF [sched \<diamondop> FIRST_READY]\<^sub>v =\<^sub>b [NULL]\<^sub>n  THEN
          Cskip
        ELSE
          sched \<diamondop> SECOND_READY :=\<^sub>C \<lbrakk>[sched \<diamondop> FIRST_READY]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> ;;
          WITH Cur WHEN [True]\<^sub>b DO
            sched \<diamondop> CUR_RUNNING :=\<^sub>C \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> ;;
            IF [sched \<diamondop> CUR_RUNNING]\<^sub>v =\<^sub>b [NULL]\<^sub>n THEN
               \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> :=\<^sub>C [sched \<diamondop> SECOND_READY]\<^sub>v          
            ELSE
               \<lbrakk>[sched \<diamondop> CUR_RUNNING]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [READY]\<^sub>n ;;
               \<lbrakk>[sched \<diamondop> CUR_RUNNING]\<^sub>v\<Down>\<^sub>tnext\<rbrakk> :=\<^sub>C [sched \<diamondop> SECOND_READY]\<^sub>v;;
               \<lbrakk>[A_Readyq]\<^sub>v\<rbrakk> :=\<^sub>C [sched \<diamondop> CUR_RUNNING]\<^sub>v 
            FI ;;
            \<lbrakk>[sched \<diamondop> FIRST_READY]\<^sub>v\<Down>\<^sub>tstate\<rbrakk> :=\<^sub>C [RUNNING]\<^sub>n ;;
            \<lbrakk>[A_Cur]\<^sub>v\<rbrakk> :=\<^sub>C [sched \<diamondop> FIRST_READY]\<^sub>v 
          OD
        FI
    OD"

lemma fvA_Gamma : "\<lbrakk>fvAs \<Gamma> = {}; \<Gamma>' = (\<Gamma>(Cur := inv1,  Stack := inv3, Readyq := inv2))\<rbrakk> \<Longrightarrow>
      fvAs \<Gamma>' = fvA inv1 \<union> fvA inv2 \<union> fvA inv3"
  apply (rule_tac s = "fvA (\<Gamma>' Cur) \<union> fvA (\<Gamma>' Readyq) \<union> fvA (\<Gamma>' Stack) \<union> 
        (\<Union>x \<in> UNIV - {Cur, Readyq, Stack}. fvA (\<Gamma>' x))" in HOL.trans)
   apply (simp only: fvAs_def) apply blast
  by (simp add: fvAs_def)

lemma fvA_Gamma1 : "\<lbrakk>fvAs \<Gamma> = {}; \<Gamma>' = (\<Gamma>(Stack := inv1, Readyq := inv3, Cur := inv2))\<rbrakk> \<Longrightarrow>
      fvAs \<Gamma>' = fvA inv1 \<union> fvA inv2 \<union> fvA inv3"
  by (smt fun_upd_twist fvA_Gamma sup_assoc sup_commute)

lemma fvA_Gamma2 : "\<lbrakk>fvAs \<Gamma> = {}; \<Gamma>' = (\<Gamma>(Cur := inv2, Readyq := inv3, Stack := inv1))\<rbrakk> \<Longrightarrow>
      fvAs \<Gamma>' = fvA inv1 \<union> fvA inv2 \<union> fvA inv3"
  by (smt fun_upd_twist fvA_Gamma sup_assoc sup_commute)



end