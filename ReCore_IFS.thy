theory ReCore_IFS
  imports SecurityModel Event_Computation
begin

record 'd action = 
        actk :: actk
        eventof :: event
        domain ::  "'d"

locale InfoFlow = 
  fixes \<Gamma> :: "'Env"
    and C0 ::  "rpesconf"
    and step :: "'d action \<Rightarrow> (rpesconf \<times> rpesconf) set"
    and interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
    and vpeq ::  "heap \<Rightarrow> 'd \<Rightarrow> heap \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
    and obs ::  "heap \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
    and dome :: "state \<Rightarrow> event \<Rightarrow> 'd"
  assumes info_vpeq_trans : "\<forall> a b c u. (a \<sim> u \<sim> b) \<and> (b \<sim> u \<sim> c) \<longrightarrow> (a \<sim> u \<sim> c)"
    and   info_vpeq_sym : "\<forall> a b u. (a \<sim> u \<sim> b) \<longrightarrow> (b \<sim> u \<sim> a)"
    and   info_vpeq_refl : "\<forall> a u. (a \<sim> u \<sim> a)"
    and   info_step_def : "step a \<equiv> {(P, Q). ( P -rpes-(actk a)\<rightarrow> Q) \<and> 
                                ((\<exists>e k. actk a = ((EvtEnt e)\<sharp>k) \<and> eventof a = e 
                                  \<and> dome (gets P)  e = domain a) \<or>
                                  (\<exists>c k. actk a = ((Cmd c)\<sharp>k) \<and> eventof a = (getx P) k 
                                  \<and> dome (gets P) (eventof a) = domain a))}"
begin

definition vpeqC :: "rpesconf \<Rightarrow> 'd \<Rightarrow> rpesconf \<Rightarrow> bool" ("(_ \<sim>._.\<sim> _)" [70,71] 60)
   where "vpeqC C1 u C2 \<equiv> snd (gets C1) \<sim>u\<sim> snd (gets C2)"

lemma vpeqC_transitive: "\<forall> a b c u. (a \<sim>.u.\<sim> b) \<and> (b \<sim>.u.\<sim> c) \<longrightarrow> (a \<sim>.u.\<sim> c)"
  using info_vpeq_trans vpeqC_def by blast

lemma vpeqC_symmetric: "\<forall> a b u. (a \<sim>.u.\<sim> b) \<longrightarrow> (b \<sim>.u.\<sim> a)"
  using info_vpeq_sym vpeqC_def by blast

lemma vpeqC_reflexive: "\<forall> a u. (a \<sim>.u.\<sim> a)"
  by (simp add: info_vpeq_refl vpeqC_def)

definition obsC :: " rpesconf \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>."  55)
  where "C \<guillemotright>. d= snd (gets C) \<guillemotright> d"

definition nextC :: "rpesconf \<Rightarrow> 'd action \<Rightarrow>  rpesconf set" where
  "nextC P a \<equiv> {Q. (P,Q)\<in>step a}"
      
primrec runC :: "'d action list \<Rightarrow> (rpesconf \<times> rpesconf) set" where
  run_Nil:  "runC [] = Id " |
  run_Cons: "runC (a#as) = {(P,Q). (\<exists>R. (P,R) \<in> step a \<and> (R,Q) \<in> runC as)}"

definition reachableC :: "rpesconf \<Rightarrow> rpesconf \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
  "reachableC C1 C2 \<equiv>  (\<exists>as. (C1,C2) \<in> runC as)"

definition reachableC0 :: "rpesconf \<Rightarrow> bool"  where
  "reachableC0 C \<equiv> reachableC C0 C"

subsection \<open>Unwinding Conditions\<close>

definition observed_consistentC :: "bool" where
 "observed_consistentC \<equiv> (\<forall>s t u. ((s \<sim> u \<sim> t) \<longrightarrow> s \<guillemotright> u  = t \<guillemotright> u))"

definition local_respectC :: "bool" where
  "local_respectC \<equiv> \<forall>a u C. (reachableC0 C) \<longrightarrow> (\<not> (domain a) \<leadsto> u) \<longrightarrow> 
                              (\<forall> C'. (C'\<in>nextC C a) \<longrightarrow> (C \<sim>.u.\<sim> C'))"


definition weak_step_consistentC :: "bool" where
  "weak_step_consistentC \<equiv> \<forall>a u C1 C2. (reachableC0 C1) \<and> (reachableC0 C2) \<longrightarrow>  (C1 \<sim>.u.\<sim> C2) 
                         \<and> ( ((domain a) \<leadsto> u) \<longrightarrow> (C1 \<sim>.(domain a).\<sim> C2) ) \<longrightarrow> 
                         (\<forall> C1' C2'. (C1'\<in>nextC C1 a) \<and> (C2'\<in>nextC C2 a) \<longrightarrow> (C1' \<sim>.u.\<sim> C2'))"

interpretation SM_IFS C0 step domain obsC vpeqC interference
  using SM_IFS_def vpeqC_reflexive vpeqC_symmetric vpeqC_transitive by blast

lemma run_equiv : "runC as = run as"
  apply (induct as, simp)
  by (simp add: relcomp_unfold)

lemma reachableC_equiv : "reachableC C1 C2 = reachable C1 C2"
  by (simp add: reachable_def reachableC_def run_equiv)

lemma reachable0_equiv : "reachableC0 C = reachable0  C"
  by (simp add: reachable0_def reachableC0_def reachableC_equiv)

lemma ReCore_obs_consistent : "observed_consistentC \<Longrightarrow> observed_consistent"
  by (metis obsC_def observed_consistentC_def observed_consistent_def vpeqC_def)

lemma local_respectC_equiv : "local_respectC \<longleftrightarrow> local_respect"
  using local_respectC_def local_respect_def nextC_def reachable0_equiv by fastforce

lemma weak_step_consistentC_equiv : "weak_step_consistentC \<longleftrightarrow> weak_step_consistent"
proof
  assume "weak_step_consistentC"
  then show "weak_step_consistent"
    by (smt (verit, best) mem_Collect_eq nextC_def reachable0_equiv weak_step_consistentC_def weak_step_consistent_def)
next
  assume "weak_step_consistent "
  then show "weak_step_consistentC"
    by (smt (verit, ccfv_threshold) mem_Collect_eq nextC_def reachable0_equiv weak_step_consistentC_def weak_step_consistent_def)
qed

subsection \<open>Unwinding Theorem\<close>

theorem ReCore_nonleakage:
    assumes p1: observed_consistentC
    and     p2: weak_step_consistentC 
  shows "nonleakage"
  using ReCore_obs_consistent UnwindingTheorem_nonleakage p1 p2 weak_step_consistentC_equiv by blast

theorem ReCore_noninfluence0:
    assumes p1: observed_consistentC
    and     p2: local_respectC
    and     p3: weak_step_consistentC
  shows "noninfluence0"
  using ReCore_obs_consistent UnwindingTheorem_noninfluence0 local_respectC_equiv p1 p2 p3 weak_step_consistentC_equiv by fastforce

end
end

    