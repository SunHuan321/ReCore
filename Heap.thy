theory Heap
  imports CSLsound
begin

abbreviation "NULL \<equiv> Enum 0"

abbreviation "BLOCKED \<equiv> Enum 0"
abbreviation "READY \<equiv> Enum 1"
abbreviation "RUNNING \<equiv> Enum 2"

definition assn_equiv :: "assn \<Rightarrow> assn \<Rightarrow> bool"   (infixl "\<equiv>\<^sub>S\<^sub>L"  60)
  where " P \<equiv>\<^sub>S\<^sub>L  Q \<equiv> \<forall>\<sigma>. \<sigma> \<Turnstile> P \<longleftrightarrow> \<sigma> \<Turnstile> Q"

lemma assn_emp_equiv : " P ** Aemp \<equiv>\<^sub>S\<^sub>L P"
  using assn_equiv_def by auto

lemma assn_commute_equiv : " P ** Q \<equiv>\<^sub>S\<^sub>L Q ** P"
  apply (simp add: assn_equiv_def)
  using map_add_commute by fastforce

primrec array :: "exp \<Rightarrow> exp list \<Rightarrow> assn"
  where
      "array p [] = Aemp"
    | "array p (x # xs) = (p \<longmapsto> x) ** (array (Eplus p (Enum 1)) xs)"

primrec buffer :: "exp \<Rightarrow> exp \<Rightarrow> exp list \<Rightarrow> assn"
  where
    "buffer p q [] = Apure (Beq p q)"
  | "buffer p q (x # xs) = (p \<longmapsto> x) ** (buffer (Eplus p (Enum 1)) q xs)"

definition
  thread_node :: " exp \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> assn"
  where
      "thread_node t state pri next data \<equiv> array t [state, pri, next, data]"

definition 
  thread_node' :: "exp \<Rightarrow> (exp \<times> exp \<times> exp \<times> exp) \<Rightarrow> assn"
  where
    "thread_node' t x = thread_node t (fst x) (fst (snd x)) (fst (snd (snd x)))
                                      (snd (snd (snd x)))"


primrec
  thread_slseg :: "exp \<Rightarrow> exp \<Rightarrow> (exp \<times> exp \<times> exp \<times> exp) list \<Rightarrow> assn"
  where
    "thread_slseg h tn [] = Apure (Beq h tn)"
  | "thread_slseg h tn (x # xs) = thread_node' h x ** thread_slseg (fst (snd (snd x))) tn xs" 

definition thread_sl :: "exp \<Rightarrow> (exp \<times> exp \<times> exp \<times> exp) list \<Rightarrow> assn"
  where
    "thread_sl t l \<equiv> thread_slseg t NULL l"

primrec conj_list :: "('a \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> assn"
  where
    "conj_list \<Gamma> [] = Aemp"
  | "conj_list \<Gamma> (x # xs) = Aconj (\<Gamma> x) (conj_list \<Gamma> xs)"

definition ready_thread :: "(exp \<times> exp \<times> exp \<times> exp) \<Rightarrow> assn"
  where
    "ready_thread x \<equiv> Apure (Beq (fst x) READY)"

definition ready_thread_list :: "(exp \<times> exp \<times> exp \<times> exp) list \<Rightarrow> assn"
  where "ready_thread_list l \<equiv> conj_list ready_thread l"

definition blocked_thread :: "(exp \<times> exp \<times> exp \<times> exp) \<Rightarrow> assn"
  where
    "blocked_thread x \<equiv> Apure (Beq (fst x) BLOCKED)"

definition blocked_thread_list :: "(exp \<times> exp \<times> exp \<times> exp) list \<Rightarrow> assn"
  where "blocked_thread_list l \<equiv> conj_list blocked_thread l"

definition wait_queue :: "exp \<Rightarrow> (exp \<times> exp \<times> exp \<times> exp) list \<Rightarrow> assn"
  where "wait_queue wait ts \<equiv> Aconj (thread_sl wait ts) (blocked_thread_list ts)"

definition
  stack :: " exp \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp list \<Rightarrow> (exp \<times> exp \<times> exp \<times> exp) list \<Rightarrow> assn"
  where
    "stack s b n t wait buf ts \<equiv> (s \<longmapsto> b) ** ((Eplus s (Enum 1)) \<longmapsto> n) ** ((Eplus s (Enum 2)) \<longmapsto> t) 
                    ** ((Eplus s (Enum 3)) \<longmapsto> wait) ** (buffer b t buf) ** (wait_queue wait ts)"

end