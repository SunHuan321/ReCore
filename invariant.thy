theory invariant
  imports Stack_Spec
begin

definition thd_st :: "tcb \<Rightarrow> nat"
  where "thd_st t = fst t"

definition thd_next :: "tcb \<Rightarrow> nat"
  where "thd_next t = fst (snd t)"

definition thd_data :: "tcb \<Rightarrow> nat"
  where "thd_data t =  snd (snd t)"

definition uptcb_state :: "tcb \<Rightarrow> nat \<Rightarrow> tcb"  ("(_ :=\<^sub>s\<^sub>t _)" 200)
  where "uptcb_state t s = (s, thd_next t, thd_data t)"

definition uptcb_next :: "tcb \<Rightarrow> nat \<Rightarrow> tcb"   ("(_ :=\<^sub>n\<^sub>x _)" 200)
  where "uptcb_next t n = (thd_st t, n, thd_data t)"

definition uptcb_data :: "tcb \<Rightarrow> nat \<Rightarrow> tcb"   ("(_ :=\<^sub>d\<^sub>t _)" 200)
  where "uptcb_data t d = (thd_st t, thd_next t, d)"


definition is_running :: "tcb \<Rightarrow> bool"
  where "is_running t =  (thd_st t = RUNNING)"

definition is_ready :: "tcb \<Rightarrow> bool"
  where "is_ready t =  (thd_st t = READY)"

definition is_blocked :: "tcb \<Rightarrow> bool"
  where "is_blocked t =  (thd_st t = BLOCKED)"

definition tcbs_next :: "tcbs \<Rightarrow> nat list"
  where "tcbs_next ts = map thd_next ts"

definition tcbs_st :: "tcbs \<Rightarrow> nat list"
  where "tcbs_st ts = map thd_st ts"

primrec all_ready :: "tcbs \<Rightarrow> bool"
  where 
    "all_ready [] = True"
  | "all_ready (x # xs) = (is_ready x \<and> all_ready xs)"

primrec all_blocked :: "tcbs \<Rightarrow> bool"
  where 
    "all_blocked [] = True"
  | "all_blocked (x # xs) = (is_blocked x \<and> all_blocked xs)"

definition tcbs_distinct :: "nat \<Rightarrow> tcbs \<Rightarrow> bool"
  where 
    "tcbs_distinct p l = distinct (p # (tcbs_next l))"

definition stack_base :: "stack_mem \<Rightarrow> nat"
  where "stack_base s = fst s"

definition stack_next :: "stack_mem \<Rightarrow> nat"
  where "stack_next s = fst (snd s)"

definition stack_top :: "stack_mem \<Rightarrow> nat"
  where "stack_top s = fst (snd (snd s))"

definition stack_wait :: "stack_mem \<Rightarrow> nat"
  where "stack_wait s = fst (snd (snd (snd s)))"

definition stack_buf :: "stack_mem \<Rightarrow> nat list"
  where "stack_buf s = fst (snd (snd (snd (snd s))))"

definition stack_tcbs :: "stack_mem \<Rightarrow> tcbs"
  where "stack_tcbs s = snd (snd (snd (snd (snd s))))"

definition upstack_next :: "stack_mem \<Rightarrow> nat \<Rightarrow> stack_mem"   ("(_ :=\<^sub>n\<^sub>e _)" 200)
  where "upstack_next s n = (stack_base s, n, stack_top s, stack_wait s, stack_buf s, stack_tcbs s)"

definition upstack_wait :: "stack_mem \<Rightarrow> nat \<Rightarrow> stack_mem"   ("(_ :=\<^sub>w\<^sub>a _)" 200)
  where "upstack_wait s w = (stack_base s, stack_next s, stack_top s, w, stack_buf s, stack_tcbs s)"

definition upstack_buf :: "stack_mem \<Rightarrow> nat list \<Rightarrow> stack_mem"   ("(_ :=\<^sub>b\<^sub>f _)" 200)
  where "upstack_buf s buf = (stack_base s, stack_next s, stack_top s, stack_wait s, buf, stack_tcbs s)"

definition upstack_tcbs :: "stack_mem \<Rightarrow> tcbs \<Rightarrow> stack_mem"   ("(_ :=\<^sub>t\<^sub>c _)" 200)
  where "upstack_tcbs s xs = (stack_base s, stack_next s, stack_top s, stack_wait s, stack_buf s, xs)"

(* memory assertion *)

primrec buf :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> assn"
  where "buf h tn [] = \<langle>[h = tn]\<^sub>b\<rangle>\<^sub>S\<^sub>L"
  | "buf h tn (x # xs) = ([h]\<^sub>n \<longmapsto> [x]\<^sub>n) ** buf (h+1) tn xs"
 
definition thread_node_nonempty :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node_nonempty p t = (([p]\<^sub>n \<longmapsto> [thd_st t]\<^sub>n) ** ([p + 1]\<^sub>n \<longmapsto> [thd_next t]\<^sub>n)
                           ** ([p + 2]\<^sub>n \<longmapsto> [thd_data t]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[p \<noteq> NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L)"

fun  thread_node :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where 
   "thread_node NULL t = (\<langle>[False]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  |"thread_node p t = (([p]\<^sub>n \<longmapsto> [thd_st t]\<^sub>n) ** ([p + 1]\<^sub>n \<longmapsto> [thd_next t]\<^sub>n)
                           ** ([p + 2]\<^sub>n \<longmapsto> [thd_data t]\<^sub>n))"

fun thread_slseg :: "nat \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where 
    "thread_slseg h tn [] = ( \<langle>[h = tn]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp )"
  | "thread_slseg NULL tn (x # xs) = (\<langle>[False]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  | "thread_slseg h tn (x # xs) = (thread_node h x) ** (thread_slseg ((thd_next x)) tn xs)"

definition thread_sl :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "thread_sl h ts = thread_slseg h NULL ts"

lemma thread_sl_equiv : "thread_sl t (x # xs) \<equiv>\<^sub>S\<^sub>L (thread_node t x) ** thread_sl (thd_next x) xs"
  apply (case_tac t, simp add: thread_sl_def assn_equiv_def)
  by (simp add: thread_sl_def assn_equiv_reflex)

definition stack_node :: "nat  \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "stack_node p s = (([p]\<^sub>n \<longmapsto> [stack_base s]\<^sub>n) ** ([p + 1]\<^sub>n \<longmapsto> [stack_next s]\<^sub>n) ** 
                          ([p + 2]\<^sub>n \<longmapsto> [stack_top s]\<^sub>n) ** ([p + 3]\<^sub>n \<longmapsto> [stack_wait s]\<^sub>n))"


definition stack_buf_waitq :: "stack_mem \<Rightarrow> bool"
  where "stack_buf_waitq s =  ((stack_wait s) \<noteq> NULL \<longrightarrow> (stack_base s) = (stack_next s))"

definition  stack_pt :: " stack_mem \<Rightarrow> bool"
  where "stack_pt s = ((stack_base s) \<le> (stack_next s) \<and> (stack_next s) \<le> (stack_top s)
                        \<and> (stack_base s) < (stack_top s))"

(* invariant *)

definition inv_is_running :: "tcb \<Rightarrow> assn"
  where "inv_is_running t = \<langle>[is_running t]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_is_ready :: "tcb \<Rightarrow> assn"
  where "inv_is_ready t = \<langle>[is_ready t]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_is_blocked :: "tcb \<Rightarrow> assn"
  where "inv_is_blocked t = \<langle>[is_blocked t]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_all_ready :: "tcbs \<Rightarrow> assn"
  where "inv_all_ready ts = \<langle>[all_ready ts]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_all_blocked :: "tcbs \<Rightarrow> assn"
  where "inv_all_blocked ts = \<langle>[all_blocked ts]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_thread_distinct :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where 
    "inv_thread_distinct p ts = \<langle>[tcbs_distinct p ts]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_waitq :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "inv_waitq w ts = ((inv_all_blocked ts) \<and>\<^sub>S\<^sub>L (inv_thread_distinct w ts))"

definition inv_stack_buf_waitq :: "stack_mem \<Rightarrow> assn"
  where "inv_stack_buf_waitq s = \<langle>[stack_buf_waitq s]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_stack_pt :: " stack_mem \<Rightarrow> assn"
  where "inv_stack_pt s =  \<langle>[stack_pt s]\<^sub>b\<rangle>\<^sub>S\<^sub>L"

definition inv_stack_waitq :: "stack_mem \<Rightarrow> assn"
  where "inv_stack_waitq s = inv_waitq (stack_wait s) (stack_tcbs s)"

definition inv_cur_aux :: "nat \<Rightarrow> assn"
  where "inv_cur_aux p =  \<langle> [CUR_THREAD]\<^sub>v =\<^sub>b [p]\<^sub>n \<rangle>\<^sub>S\<^sub>L" 

definition inv_ready_aux :: "nat \<Rightarrow> assn"
  where "inv_ready_aux p = \<langle>[READY_LIST]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L"

(* resource invariant *)

definition cur_node :: "nat \<Rightarrow> assn"
  where "cur_node p =  ([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[CUR_THREAD]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition is_cur :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "is_cur p t = ((thread_node p t) \<and>\<^sub>S\<^sub>L (inv_is_running t))"

definition inv_cur1 :: "nat \<Rightarrow> tcb \<Rightarrow> assn"
  where "inv_cur1 p t = ([A_Cur]\<^sub>v \<longmapsto> [p]\<^sub>n) ** (is_cur p t)"

definition inv_cur :: "assn"
    where "inv_cur \<equiv> ([A_Cur]\<^sub>v \<longmapsto> [NULL]\<^sub>n) \<or>\<^sub>S\<^sub>L (Aexcur inv_cur1)"
(* inv_cur \<equiv> cur_node NULL \<or> \<exists>p t. cur_node p ** is_cur p t*)

lemma "(is_cur p t \<and>\<^sub>S\<^sub>L \<langle>[p = NULL]\<^sub>b\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L \<langle>[False]\<^sub>b\<rangle>\<^sub>S\<^sub>L "
  apply (case_tac p, simp add: is_cur_def assn_equiv_def)
  by (simp add: assn_equiv_def)

definition ready_node :: "nat \<Rightarrow> assn"
  where "ready_node r =  ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[READY_LIST]\<^sub>v =\<^sub>b [r]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"

definition is_readyq :: "nat  \<Rightarrow> tcbs \<Rightarrow> assn"
  where "is_readyq r xs = ((thread_sl r xs) \<and>\<^sub>S\<^sub>L (inv_all_ready xs))"

definition inv_readyq1 :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "inv_readyq1 r xs = ([A_Readyq]\<^sub>v \<longmapsto> [r]\<^sub>n) ** (is_readyq r xs)"

definition inv_readyq :: "assn"
  where "inv_readyq = Aexreadyq inv_readyq1"
(* inv_readyq \<equiv> \<exists>r xs. ready_node r ** is_readyq r xs*)

definition is_waitq :: "nat  \<Rightarrow> tcbs \<Rightarrow> assn"
  where "is_waitq r xs = ((thread_sl r xs) \<and>\<^sub>S\<^sub>L (inv_all_blocked xs))"

definition is_stack ::  " nat \<Rightarrow> stack_mem  \<Rightarrow> assn"
  where "is_stack p s  = (((stack_node p s) ** (is_waitq (stack_wait s) (stack_tcbs s)) **
         (buf (stack_base s) (stack_top s) (stack_buf s))) \<and>\<^sub>S\<^sub>L (inv_stack_buf_waitq s) 
         \<and>\<^sub>S\<^sub>L (inv_stack_pt s))"

definition inv_stack1 :: "nat \<Rightarrow> stack_mem \<Rightarrow> assn"
  where "inv_stack1 s st = ( [A_Stack]\<^sub>v \<longmapsto> [s]\<^sub>n) ** is_stack s st"

definition inv_stack :: "assn"
  where "inv_stack \<equiv> Aexstack inv_stack1"

(* inv_stack \<equiv> \<exists>s st. ([A_Stack \<longmapsto> s] **  is_stack s st*)

(* ========================== simplify the assertion ========================================= *)
fun thread_ready_slseg :: "nat \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where 
    "thread_ready_slseg h tn [] = (\<langle>[h = tn]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  | "thread_ready_slseg NULL tn (x # xs) = (\<langle>[False]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  | "thread_ready_slseg h tn (x # xs) = ((thread_node h x) \<and>\<^sub>S\<^sub>L (inv_is_ready x)) 
                                        ** (thread_ready_slseg ((thd_next x)) tn xs)"

definition thread_ready_sl :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "thread_ready_sl h ts = thread_ready_slseg h NULL ts"


lemma ready_sl_equiv : "thread_ready_sl h (x # xs) \<equiv>\<^sub>S\<^sub>L (((thread_node h x) 
                \<and>\<^sub>S\<^sub>L (inv_is_ready x)) ** (thread_ready_sl (thd_next x) xs))"
  apply (case_tac h, simp add: thread_ready_sl_def assn_equiv_def)
  apply (simp add: thread_ready_sl_def inv_is_ready_def)
  by (simp add: assn_equiv_reflex)

lemma ready_sl_implies : "thread_ready_sl h (x # xs) \<sqsubseteq> (thread_node h x) ** (thread_ready_sl  
      (thd_next x) xs)"
  apply (rule_tac Q = "(((thread_node h x) \<and>\<^sub>S\<^sub>L (inv_is_ready x)) ** (thread_ready_sl 
  (thd_next x) xs))" in implies_trans)
   apply (rule equiv_implies, simp add: ready_sl_equiv)
  apply (simp add: implies_def) by auto[1]

lemma readyq_equiv : "is_readyq r xs \<equiv>\<^sub>S\<^sub>L thread_ready_sl r xs"
  apply (simp add: is_readyq_def thread_ready_sl_def, induct xs arbitrary: r)
   apply (case_tac r, simp add: thread_sl_def inv_all_ready_def assn_equiv_def)
   apply (simp add: thread_sl_def assn_equiv_def)
  apply (case_tac r, simp add: thread_sl_def assn_equiv_def)
  apply (drule_tac a = "thd_next a" in mallD)
  apply (rule_tac Q = "thread_node r a ** thread_sl (thd_next a) xs \<and>\<^sub>S\<^sub>L inv_all_ready (a # xs)"
  in assn_equiv_trans, rule assn_equiv_cong_conj)
  using thread_sl_equiv apply blast
   apply (simp add: assn_equiv_reflex)
  apply (rule_tac Q = "(thread_node r a \<and>\<^sub>S\<^sub>L inv_is_ready a) ** (thread_sl (thd_next a) xs \<and>\<^sub>S\<^sub>L 
  inv_all_ready xs)" in assn_equiv_trans)
   apply (simp add: inv_all_ready_def inv_is_ready_def assn_equiv_def) apply auto[1]
  by (simp add: assn_equiv_cong_star assn_equiv_reflex)

lemma thread_ready_sl_insert : "\<lbrakk>thd_st x = READY; thd_next x = r\<rbrakk> \<Longrightarrow>
      (thread_node t x) ** (thread_ready_sl r xs) \<equiv>\<^sub>S\<^sub>L (thread_ready_sl t (x # xs))"
  apply (case_tac t, simp add: thread_ready_sl_def assn_equiv_def)
  by (simp add: thread_ready_sl_def inv_is_ready_def is_ready_def assn_equiv_def)

lemma thread_ready_sl_insert' : "\<lbrakk>thd_st x = READY; thd_next x = r\<rbrakk> \<Longrightarrow>
      (thread_node t x) ** (is_readyq r xs) \<equiv>\<^sub>S\<^sub>L (is_readyq t (x # xs))"
  apply (rule_tac Q = "(thread_node t x) ** (thread_ready_sl r xs)" in assn_equiv_trans)
   apply (simp add: assn_equiv_cong_star assn_equiv_reflex readyq_equiv)
  apply (rule_tac Q = "thread_ready_sl t (x # xs)" in assn_equiv_trans, simp add: thread_ready_sl_insert)
  by (simp add: assn_equiv_symmetry readyq_equiv)

fun thread_wait_slseg :: "nat \<Rightarrow> nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where 
    "thread_wait_slseg h tn [] = (\<langle>[h = tn]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  | "thread_wait_slseg NULL tn (x # xs) = (\<langle>[False]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  | "thread_wait_slseg h tn (x # xs) = ((thread_node h x) \<and>\<^sub>S\<^sub>L (inv_is_blocked x)) 
                                        ** (thread_wait_slseg ((thd_next x)) tn xs)"

definition thread_wait_sl :: "nat \<Rightarrow> tcbs \<Rightarrow> assn"
  where "thread_wait_sl h ts = thread_wait_slseg h NULL ts"

lemma waitq_equiv : "is_waitq r xs \<equiv>\<^sub>S\<^sub>L thread_wait_sl r xs"
    apply (simp add: is_waitq_def thread_wait_sl_def, induct xs arbitrary: r)
   apply (case_tac r, simp add: thread_sl_def inv_all_blocked_def assn_equiv_def)
   apply (simp add: thread_sl_def assn_equiv_def)
  apply (case_tac r, simp add: thread_sl_def assn_equiv_def)
  apply (drule_tac a = "thd_next a" in mallD)
  apply (rule_tac Q = "thread_node r a ** thread_sl (thd_next a) xs \<and>\<^sub>S\<^sub>L inv_all_blocked (a # xs)"
  in assn_equiv_trans, rule assn_equiv_cong_conj)
  using thread_sl_equiv apply blast
   apply (simp add: assn_equiv_reflex)
  apply (rule_tac Q = "(thread_node r a \<and>\<^sub>S\<^sub>L inv_is_blocked a) ** (thread_sl (thd_next a) xs \<and>\<^sub>S\<^sub>L 
  inv_all_blocked xs)" in assn_equiv_trans)
   apply (simp add: inv_all_blocked_def inv_is_blocked_def assn_equiv_def) apply auto[1]
  by (simp add: assn_equiv_cong_star assn_equiv_reflex)

lemma thread_wait_sl_insert : "\<lbrakk>thd_st x = BLOCKED; thd_next x = w\<rbrakk> \<Longrightarrow>
      (thread_node t x) ** (thread_wait_sl w xs) \<equiv>\<^sub>S\<^sub>L (thread_wait_sl t (x # xs))"
  apply (case_tac t, simp add: thread_wait_sl_def assn_equiv_def)
  by (simp add: thread_wait_sl_def inv_is_blocked_def is_blocked_def assn_equiv_def)

end