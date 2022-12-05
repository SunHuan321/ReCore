theory mem_spec
  imports CSLsound
begin

abbreviation "NULL \<equiv> 0"

abbreviation "BLOCKED \<equiv>  0 :: nat"
abbreviation "READY \<equiv>  1 :: nat"
abbreviation "RUNNING \<equiv>  2 :: nat"

type_synonym tcb = "nat \<times> nat \<times> nat \<times> nat"
type_synonym tcbs = "tcb list"
type_synonym buf = "nat list"
type_synonym stack = "nat \<times> nat \<times> nat \<times> nat \<times> buf \<times> tcbs"

primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "le a [] = True"
  | "le a (x # xs) = (a \<le> x \<and> le a xs)"

primrec sorted :: "nat list \<Rightarrow> bool"
  where 
    "sorted [] = True"
  | "sorted (x # xs) = (le x xs & sorted xs)"

definition thd_st :: "tcb \<Rightarrow> nat"
  where "thd_st t = fst t"

definition thd_pri :: "tcb \<Rightarrow> nat"
  where "thd_pri t = fst (snd t)"

definition thd_next :: "tcb \<Rightarrow> nat"
  where "thd_next t = fst (snd (snd t))"

definition thd_data :: "tcb \<Rightarrow> nat"
  where "thd_data t = snd (snd (snd t))"

definition is_running :: "tcb \<Rightarrow> bool"
  where "is_running t =  (thd_st t = RUNNING)"

definition is_blocked :: "tcb \<Rightarrow> bool"
  where "is_blocked t =  (thd_st t = BLOCKED)"

definition tcb2list :: "tcb \<Rightarrow> nat list"
  where "tcb2list t = [thd_st t, thd_pri t, thd_next t, thd_data t]"

definition tcbs_next :: "tcbs \<Rightarrow> nat list"
  where "tcbs_next ts = map thd_next ts"

definition tcbs_pri :: "tcbs \<Rightarrow> nat list"
  where "tcbs_pri ts = map thd_pri ts"

definition tcbs_st :: "tcbs \<Rightarrow> nat list"
  where "tcbs_st ts = map thd_st ts"

primrec all_running :: "tcbs \<Rightarrow> bool"
  where 
    "all_running [] = True"
  | "all_running (x # xs) = (is_running x \<and> all_running xs)"

primrec all_blocked :: "tcbs \<Rightarrow> bool"
  where 
    "all_blocked [] = True"
  | "all_blocked (x # xs) = (is_blocked x \<and> all_blocked xs)"

definition stack_base :: "stack \<Rightarrow> nat"
  where "stack_base s = fst s"

definition stack_next :: "stack \<Rightarrow> nat"
  where "stack_next s = fst (snd s)"

definition stack_top :: "stack \<Rightarrow> nat"
  where "stack_top s = fst (snd (snd s))"

definition stack_wait :: "stack \<Rightarrow> nat"
  where "stack_wait s = fst (snd (snd (snd s)))"

definition stack_buf :: "stack \<Rightarrow> nat list"
  where "stack_buf s = fst (snd (snd (snd (snd s))))"

definition stack_tcbs :: "stack \<Rightarrow> tcbs"
  where "stack_tcbs s = snd (snd (snd (snd (snd s))))"

definition stack2list :: "stack \<Rightarrow> nat list"
  where "stack2list s = [stack_base s, stack_next s, stack_top s, stack_wait s]"

(* auxillary assertion *)
primrec array :: "exp \<Rightarrow> nat list \<Rightarrow> assn"
  where 
    "array p [] = Aemp"
  | "array p (x # xs) = (p \<longmapsto> Enum x) ** (array (Eplus p (Enum 1)) xs)"

primrec buf :: "exp \<Rightarrow> exp \<Rightarrow> nat list \<Rightarrow> assn"
  where
    "buf b t [] = Apure (Beq b t)"
  | "buf b t (x # xs) = (b \<longmapsto> (Enum x)) ** (buf (Eplus b (Enum 1)) t xs)"

definition thread_node :: "exp \<Rightarrow> tcb \<Rightarrow> assn"
  where "thread_node p t = array p (tcb2list t)"

primrec thread_slseg :: "exp \<Rightarrow> exp \<Rightarrow> tcbs \<Rightarrow> assn"
  where 
    "thread_slseg h tn [] = Apure (Beq h tn)"
  | "thread_slseg h tn (x # xs) = (thread_node h x) ** (thread_slseg (Enum (thd_next x)) tn xs)"

definition thread_sl :: "exp \<Rightarrow> tcbs \<Rightarrow> assn"
  where "thread_sl h ts = thread_slseg h (Enum NULL) ts"

definition stack_node :: "exp \<Rightarrow> stack \<Rightarrow> assn"
  where "stack_node p s = array p (stack2list s) ** 
                          (buf (Enum (stack_base s + 1)) (Enum (stack_top s - 1)) (stack_buf s)) 
                          ** (thread_sl (Enum (stack_wait s)) (stack_tcbs s))"

(* invariant *)
definition inv_pri :: "tcbs \<Rightarrow> assn"
  where "inv_pri ts = Apure (Bbool (sorted (tcbs_pri ts)))"

definition inv_is_running :: "tcb \<Rightarrow> assn"
  where "inv_is_running t = Apure (Bbool (is_running t))"

definition inv_all_running :: "tcbs \<Rightarrow> assn"
  where "inv_all_running ts = Apure (Bbool (all_running ts))"

definition inv_all_blocked :: "tcbs \<Rightarrow> assn"
  where "inv_all_blocked ts = Apure (Bbool (all_blocked ts))"

primrec inv_thread_distinct :: "exp \<Rightarrow> tcbs \<Rightarrow> assn"
  where 
    "inv_thread_distinct p [] = Apure (Bbool True)"
  | "inv_thread_distinct p (x # xs) = Aconj (Apure (Bnot (Beq p (Enum (thd_next x)))))
                                        (Apure (Bbool (distinct (tcbs_next (x # xs)))))"


definition inv_waitq :: "exp \<Rightarrow> tcbs \<Rightarrow> assn"
  where "inv_waitq w ts = thread_sl w ts ** inv_all_blocked ts **
                                            inv_thread_distinct w ts"

definition inv_buf_waitq :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> assn"
  where "inv_buf_waitq b n w = Apure (Bbool (w = NULL \<longrightarrow> b = n))"


definition inv_stack_pt :: " stack \<Rightarrow> assn"
  where "inv_stack_pt s = Apure (Bbool ((stack_base s) \<le> (stack_next s) 
                                        \<and> (stack_next s) \<le> (stack_top s)))"

definition inv_stack_waitq :: "stack \<Rightarrow> assn"
  where "inv_stack_waitq s = inv_waitq (Enum (stack_wait s)) (stack_tcbs s)"

definition inv_stack_buf_waitq :: "stack \<Rightarrow> assn"
  where "inv_stack_buf_waitq s = inv_buf_waitq (stack_base s) (stack_next s) (stack_wait s)"

(* resource invariant *)
definition inv_cur :: "exp \<Rightarrow> tcb \<Rightarrow> assn"
  where "inv_cur p t = (thread_node p t) ** inv_is_running t"

definition inv_readyq :: "exp \<Rightarrow> tcbs \<Rightarrow> assn"
  where "inv_readyq r ts = thread_sl r ts ** inv_all_running ts **
                                             inv_thread_distinct r ts"

definition inv_stack ::  "exp \<Rightarrow> stack \<Rightarrow> assn"
  where "inv_stack p s = stack_node p s ** (inv_stack_waitq s) 
                      ** (inv_stack_buf_waitq s) ** (inv_stack_pt s)"

                                                         
end
