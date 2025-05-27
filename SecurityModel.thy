theory SecurityModel
  imports Main
begin

subsection \<open> Security State Machine \<close>

locale SM_IFS = 
  fixes s0  :: "'s"
  and step :: "'a \<Rightarrow> ('s \<times> 's) set"
  and domain :: "'a \<Rightarrow> 'd"
  and obs :: "'s \<Rightarrow> 'd \<Rightarrow> 'o" (infixl "\<guillemotright>"  55)
  and vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<sim>_\<sim> _)" [70,69,70] 60)
  and interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)" [70,71] 60)
assumes vpeq_transitive : "\<forall> a b c u. (a \<sim> u \<sim> b) \<and> (b \<sim> u \<sim> c) \<longrightarrow> (a \<sim> u \<sim> c)"
    and vpeq_symmetric : "\<forall> a b u. (a \<sim> u \<sim> b) \<longrightarrow> (b \<sim> u \<sim> a)"
    and vpeq_reflexive : "\<forall> a u. (a \<sim> u \<sim> a)"
begin

definition ivpeq :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<approx> _ \<approx> _)" [70,71] 60)
  where "ivpeq s D t \<equiv> \<forall> d \<in> D. (s \<sim> d \<sim> t)"

primrec run :: " 'a list \<Rightarrow> ('s \<times> 's) set" 
  where run_Nil: "run  [] = Id" |
  run_Cons: "run (a#as) = step a O run as"

definition execute  :: " 'a list \<Rightarrow> 's \<Rightarrow> 's set" 
  where "execute as s = Image (run as) {s}"

lemma run_trans : "\<forall>s t v as bs. (C,T)\<in>run as \<and> (T,V)\<in>run bs \<longrightarrow> (C,V)\<in>run (as@bs)"
proof-
  {
    fix T V as bs
    have "\<forall>C. (C,T)\<in>run as \<and> (T,V)\<in>run bs \<longrightarrow> (C,V)\<in>run (as@bs)"
    proof(induct as)
      case Nil show ?case by simp
    next
      case (Cons c cs)
      assume a0: "\<forall>C. (C, T) \<in> run cs \<and> (T, V) \<in> run bs \<longrightarrow> (C, V) \<in> run (cs @ bs)"
      show ?case
      proof-
        {
          fix C
          have "(C, T) \<in> run (c # cs) \<and> (T, V) \<in> run bs \<longrightarrow> (C, V) \<in> run ((c # cs) @ bs) "
          proof
            assume b0: "(C, T) \<in> run (c # cs) \<and> (T, V) \<in> run bs"
                (*assume b1: "(T, V) \<in> run bs"*)
            from b0 obtain C' where b2: "(C,C')\<in>step c \<and> (C',T)\<in>run cs" by auto
            with a0 b0 have "(C',V)\<in>run (cs@bs)" by blast
            with b2 show "(C, V) \<in> run ((c # cs) @ bs)"
              by auto
          qed
        }
        then show ?thesis by auto
      qed
    qed
  }
  then show ?thesis by auto
qed

definition reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
  "reachable s t \<equiv>  (\<exists>as. (s, t) \<in> run as)"

definition reachable0 :: "'s \<Rightarrow> bool"  where
  "reachable0 s \<equiv> reachable s0 s"

lemma reachableC0 : "reachable0 s0"
  by (metis IdI reachable0_def reachable_def run_Nil)

lemma reachable_self : "reachable s s"
  by (metis IdI reachable_def run_Nil)
  
lemma reachable_step : "(s, s')\<in>step a \<Longrightarrow> reachable s s'"
proof-
  assume a0: "(s, s')\<in>step a"
  then have "(s , s')\<in>run [a]"
    by simp
  then show ?thesis
    using reachable_def by blast
qed

lemma reachable_trans : "\<lbrakk>reachable C T; reachable T V\<rbrakk> \<Longrightarrow> reachable C V"
proof-
  assume a0: "reachable C T"
  assume a1: "reachable T V"
  from a0 have "C = T \<or> (\<exists>as. (C,T)\<in>run as)" using reachable_def 
    by metis
  then show ?thesis
  proof
    assume b0: "C = T"
    show ?thesis 
    proof -
      from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run  as)" using reachable_def by metis
      then show ?thesis
      proof
        assume c0: "T=V"
        with a0 show ?thesis by simp
      next
        assume c0: "(\<exists>as. (T,V)\<in>run  as)"
        then show ?thesis by (simp add: a1 b0) 
      qed
    qed
  next
    assume b0: "\<exists>as. (C,T)\<in>run as"
    show ?thesis
    proof -
      from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run  as)" using reachable_def by metis
      then show ?thesis
      proof
        assume c0: "T=V"
        then show ?thesis using a0 by auto 
      next
        assume c0: "(\<exists>as. (T,V)\<in>run  as)"
        from b0 obtain as where d0: "(C,T)\<in>run as" by auto
        from c0 obtain bs where d1: "(T,V)\<in>run bs" by auto
        then show ?thesis using d0 reachable_def run_trans by metis 
      qed
    qed
  qed
qed

lemma reachableStep : "\<lbrakk>reachable0 C; (C,C')\<in>step a\<rbrakk> \<Longrightarrow> reachable0 C'"
  proof -
    assume a0: "reachable0 C"
    assume a1: "(C,C')\<in>step a"
    from a0 have "(C = s0) \<or> (\<exists>as. (s0,C) \<in> run as)" unfolding reachable0_def reachable_def by auto
    then show "reachable0 C'"
      proof
        assume b0: "C = s0"
        show "reachable0 C'"
          using a1 b0 reachable0_def reachable_step by auto 
      next
        assume b0: "\<exists>as. (s0,C) \<in> run as"
        show "reachable0 C'"
          using a0 a1 reachable0_def reachable_step reachable_trans by blast 
      qed
  qed

lemma reachable0_reach : "\<lbrakk>reachable0 C; reachable C C'\<rbrakk> \<Longrightarrow> reachable0 C'"
  using reachable0_def reachable_trans by blast
  
primrec sources :: "'a list \<Rightarrow> 'd \<Rightarrow> 'd set" where
  sources_Nil:  "sources [] u = {u}" |
  sources_Cons: "sources (a#as) u = (sources as u) \<union> {w. w = domain a \<and> (\<exists>v. (w \<leadsto> v) \<and> v \<in> sources as u)}"
declare sources_Nil [simp del]    
declare sources_Cons [simp del]

primrec ipurge :: "'a list \<Rightarrow> 'd \<Rightarrow> 'a list" where
  ipurge_Nil:   "ipurge [] u = []" |
  ipurge_Cons:  "ipurge (a#as) u = (if  domain a \<in> sources (a#as) u then
                                          a # ipurge as u
                                       else
                                          ipurge as u
                                      )"

lemma sources_ipurge: "sources (ipurge as u) u = sources as u"
  proof -
    have "\<forall>as u. sources (ipurge as u) u = sources as u"
    proof -
      {
        fix as
        have "\<forall>u. sources (ipurge as u) u = sources as u"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons b bs)
            assume a0: "\<forall>u. sources (ipurge bs u) u = sources bs u"
            show ?case
            proof -
            {
              fix u
              have "sources (ipurge (b # bs) u) u = sources (b # bs) u"
                proof(cases "domain b\<in>sources (b#bs) u")
                  assume b0: "domain b\<in>sources (b#bs) u"
                  then have b1: "ipurge (b # bs) u = b # ipurge bs u"
                    by (simp add: sources_Cons) 
                  from a0 have b2: "sources (ipurge bs u) u = sources bs u" by simp
                  from b1 have b3: "sources (ipurge (b # bs) u) u = sources (b # ipurge bs u) u" by simp
                  with b0 b2 have b4: "sources (ipurge (b # bs) u) u = {domain b} \<union> sources (ipurge bs u) u"
                    using sources_Cons by auto
                  from b0 have b5: "sources (b # bs) u = {domain b} \<union> sources bs u" using sources_Cons by auto 
                  then show ?thesis using a0 b4 by auto 
                next
                  assume b0: "\<not> domain b\<in>sources (b#bs) u"
                  then have b1: "sources (ipurge (b # bs) u) u = sources (ipurge bs u) u" using sources_Cons by auto 
                  from b0 have b2: "sources (b # bs) u = sources bs u" using sources_Cons by auto 
                  with a0 b1 show ?thesis by auto
                qed
            }
            then show ?thesis by auto
            qed
        qed
      }
      then show ?thesis by auto
      qed
    then show ?thesis by auto
    qed

lemma ipurge_eq: "ipurge as u = ipurge (ipurge as u) u"
  proof -
    have "\<forall>as u. ipurge as u = ipurge (ipurge as u) u"
      proof -
      {
        fix as
        have "\<forall>u. ipurge as u = ipurge (ipurge as u) u"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons b bs)
            assume a0: "\<forall>u. ipurge bs u = ipurge (ipurge bs u) u"
            show ?case
            proof -
            {
              fix u
              have "ipurge (b # bs) u = ipurge (ipurge (b # bs) u) u "
                proof(cases "domain b\<in>sources (b#bs) u")
                  assume b0: "domain b\<in>sources (b#bs) u"
                  then have b1: "ipurge (b # bs) u = b # ipurge bs u" by simp
                  then have b2: "ipurge (ipurge (b # bs) u) u = ipurge (b # ipurge bs u) u" by simp
                  have b3: "sources (b#bs) u = sources (b#ipurge bs u) u" using sources_ipurge by (metis b1) 
                  with b1 b2 show ?thesis using a0 by auto 
                next
                  assume b0: "\<not> domain b\<in>sources (b#bs) u"
                  then have b1: "ipurge (b # bs) u = ipurge bs u" by simp
                  then have b2: "ipurge (ipurge (b # bs) u) u = ipurge (ipurge bs u) u" by simp
                  with b1 show ?thesis  using a0 by auto 
                qed
            }
            then show ?thesis by auto
            qed
          qed
      }
      then show ?thesis by auto
      qed
    then show ?thesis by auto
  qed

definition exec_equiv :: "'s \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> 's  \<Rightarrow> 'a list \<Rightarrow> bool" ("(_ \<lhd> _ \<simeq> _ \<simeq> _ \<lhd> _)" [80,80,80,80,80] 75)
    where "exec_equiv S as u T bs \<equiv> \<forall>S' T'. ((S,S')\<in> run as \<and> (T,T')\<in> run bs) \<longrightarrow>  (S' \<guillemotright> u = T' \<guillemotright> u)"

lemma exec_equiv_sym : "(S \<lhd> as \<simeq> u \<simeq> T \<lhd> bs) \<Longrightarrow> (T \<lhd> bs \<simeq> u \<simeq> S \<lhd> as)"
  by (metis exec_equiv_def)

lemma exec_equiv_both:
   "\<lbrakk>reachable0 s; reachable0 t; \<forall>s' t'. (s, s') \<in> step a \<and> (t, t') \<in> step b
    \<longrightarrow>  s' \<lhd> as \<simeq> u \<simeq> t' \<lhd> bs\<rbrakk> \<Longrightarrow> s \<lhd> (a # as) \<simeq> u \<simeq> t \<lhd> (b # bs) "
proof -
  assume a0: "reachable0  s"
  assume a1: "reachable0  t"
  assume a2: " \<forall>s' t'. (s, s') \<in> step a \<and> (t, t') \<in> step b\<longrightarrow>  s' \<lhd> as \<simeq> u \<simeq> t' \<lhd> bs"
  have "\<forall>s'' t''. (s, s'') \<in> run (a # as) \<and> (t, t'') \<in> run (b # bs) \<longrightarrow> s'' \<guillemotright> u = t'' \<guillemotright> u"
  proof -
    {
      fix s'' t''
      assume b0: "(s, s'') \<in> run (a # as) \<and> (t, t'') \<in> run (b # bs)"
      then obtain s' where b1: " (s, s') \<in> step a \<and> (s',s'') \<in> run as"
        by auto
      from b0 obtain t' where b2: "(t, t') \<in> step b \<and> (t', t'') \<in> run bs"
        by auto
      with a2 b1 have b3: "s' \<lhd> as \<simeq> u \<simeq> t' \<lhd> bs" by blast
      with b0 b1 b2 have "s'' \<guillemotright> u = t'' \<guillemotright> u" using exec_equiv_def 
        by fastforce
    }
    then show ?thesis by auto
  qed
  then show ?thesis using exec_equiv_def
    by metis
qed

(* Rushby's noninterference*)
definition noninterference0 :: "bool"
  where "noninterference0 \<equiv> \<forall>u as. (s0 \<lhd> as \<simeq> u \<simeq> s0 \<lhd> (ipurge as u))"

(* reachable state version of Rushby's noninterference*)
definition noninterference0_r :: "bool"
  where "noninterference0_r \<equiv> \<forall>u as s. reachable0 s \<longrightarrow> (s \<lhd> as \<simeq> u \<simeq> s \<lhd> (ipurge as u))"

(* Oheimb's nondeterministic version of noninterference *)
(* It is the same as Oheimb's strong noninterference*)
definition noninterference1 :: "bool" where
  "noninterference1 \<equiv> \<forall>u as bs. (ipurge as u = ipurge bs u)  \<longrightarrow> (s0 \<lhd> as \<simeq> u \<simeq> s0 \<lhd> bs)"

(* reachable state version of Oheimb's strong noninterference *)
definition noninterference1_r :: "bool"
      where "noninterference1_r \<equiv> \<forall>u as bs s. reachable0 s \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> (s \<lhd> as \<simeq> u \<simeq> s \<lhd> bs)"

(* Oheimb's nonleakage. The Murray's nonleakage is the same *)
definition nonleakage :: "bool" where
  "nonleakage \<equiv> \<forall>as s t u. (reachable0 s) \<and> (reachable0 t) \<longrightarrow> (s \<approx>(sources as u)\<approx> t) 
                                 \<longrightarrow> (s \<lhd> as \<simeq> u \<simeq> t \<lhd> as)"

(* Oheimb's noninfluence *)
definition noninfluence0 ::"bool" where
  "noninfluence0 \<equiv> \<forall> u as s t . (reachable0 s) \<and> (reachable0 t) \<longrightarrow> (s \<approx>(sources as u)\<approx> t) 
                                \<longrightarrow> (s \<lhd> as \<simeq> u \<simeq> t \<lhd> (ipurge as u))"

(* Murray's noninfluence (without the scheduler) *)
(* replacing ``ipurge bs {C1} u'' by ``ipurge bs {C2} u'' yields and equivalent property as stated in Murray's paper*)
definition noninfluence1 :: "bool" where
  "noninfluence1 \<equiv> \<forall>as bs s t u. (reachable0 s) \<and> (reachable0 t) \<longrightarrow> (s \<approx>(sources as u)\<approx> t)
                                 \<longrightarrow> ipurge as u = ipurge bs u \<longrightarrow> (s \<lhd> as \<simeq> u \<simeq> t \<lhd> bs)"


subsection \<open>A Infererence Framework of Information Flow Security Properties\<close>
(*
   \<Midarrow>\<Midarrow>\<Midarrow> unwinding conditions
   \<parallel>             \<parallel>
   \<parallel>             \<parallel>(UnwindingTheorem_noninfluence0)
   \<parallel>             \<parallel>
   \<parallel>             \<Down>
   \<parallel>      noninfluence0  \<Midarrow>\<Midarrow>(lm7)\<Longrightarrow>  noninterference0_r  \<Midarrow>\<Midarrow>(lm1)\<Longrightarrow>  noninterference0
   \<parallel>             \<Up>                           \<Up>                              \<Up>
   \<parallel>(UT_nonlk)   \<parallel>(lm8)                      \<parallel>(lm9)                         \<parallel>(lm10)
   \<parallel>             \<parallel>                           \<parallel>                              \<parallel>
   \<parallel>             \<parallel>                           \<parallel>                              \<parallel>
   \<parallel>      noninfluence1  \<Midarrow>\<Midarrow>(lm6)\<Longrightarrow>  noninterference1_r  \<Midarrow>\<Midarrow>(lm2)\<Longrightarrow>  noninterference1
   \<parallel>             \<parallel>
   \<parallel>             \<parallel>(lm5)
   \<parallel>             \<parallel>
   \<parallel>             \<Down>
   \<parallel>\<Midarrow>\<Midarrow>\<Midarrow>\<Longrightarrow>  nonleakage

*)

lemma lm1: "noninterference0_r \<Longrightarrow> noninterference0"
  using noninterference0_def noninterference0_r_def reachableC0 by blast

lemma lm2: "noninterference1_r \<Longrightarrow> noninterference1"
  using noninterference1_def noninterference1_r_def reachableC0 by blast

(*
lemma lm3: "noninterference0 \<Longrightarrow> noninterference1" sorry (*exec_equiv is not transitive, so this is not satisfied*)


lemma lm4: "noninterference0_r \<Longrightarrow> noninterference1_r" sorry (*exec_equiv is not transitive, so this is not satisfied*)
*)

lemma lm5: "noninfluence1 \<Longrightarrow> nonleakage" 
  using noninfluence1_def nonleakage_def by blast

(*lemma lm11: "noninfluence0 \<Longrightarrow> nonleakage" *)

lemma lm6: "noninfluence1 \<Longrightarrow> noninterference1_r" 
  using ivpeq_def noninfluence1_def noninterference1_r_def vpeq_reflexive by blast

lemma lm7: "noninfluence0 \<Longrightarrow> noninterference0_r"
  by (simp add: ivpeq_def noninfluence0_def noninterference0_r_def vpeq_reflexive)

lemma lm8: "noninfluence1 \<Longrightarrow> noninfluence0"
  using ipurge_eq noninfluence0_def noninfluence1_def by blast 
  
lemma lm9: "noninterference1_r \<Longrightarrow> noninterference0_r"
  using ipurge_eq noninterference0_r_def noninterference1_r_def by blast

lemma lm10: "noninterference1 \<Longrightarrow> noninterference0"
  using ipurge_eq noninterference0_def noninterference1_def by blast

subsection \<open> Unwinding conditions and unwinding theorem \<close>

definition observed_consistent :: " bool" where
 "observed_consistent \<equiv> \<forall>s t u. s \<sim>u\<sim> t \<longrightarrow> s \<guillemotright> u = t \<guillemotright> u"

definition weak_step_consistent :: " bool" 
  where "weak_step_consistent \<equiv> \<forall>a d s t. reachable0 s \<and> reachable0 t \<longrightarrow> s \<sim>d\<sim> t 
                                \<and> (domain a \<leadsto> d \<longrightarrow> s \<sim>domain a\<sim> t) \<longrightarrow> (\<forall>s' t'. (s, s') \<in> step a 
                                \<and> (t, t') \<in> step a \<longrightarrow> s' \<sim>d\<sim> t')"

definition local_respect :: "bool" 
  where "local_respect \<equiv> \<forall>a d s s'. reachable0 s \<longrightarrow> \<not> domain a \<leadsto> d \<and> (s, s') \<in> step a \<longrightarrow> s \<sim>d\<sim> s'"

lemma sources_unwinding_step:
    "\<lbrakk>s \<approx> sources (a # as) d \<approx> t; weak_step_consistent; (s, s') \<in> step a; (t, t') \<in> step a;
      reachable0  s; reachable0 t\<rbrakk>  \<Longrightarrow> s' \<approx> sources as d \<approx> t'"
proof -
  assume a0: "s \<approx> sources (a # as) d \<approx> t"
  assume a1: "weak_step_consistent "
  assume a2: "(s, s') \<in> step  a"
  assume a3: "(t, t') \<in> step  a"
  assume a4: "reachable0  s"
  assume a5: "reachable0  t"
  have a7: "sources  as d \<subseteq> sources  (a#as) d" by (simp add: sources_Cons) 
  have "\<forall>u. u \<in> sources as d \<longrightarrow> s' \<sim>u\<sim> t'"
  proof -
    {
      fix u
      assume b0: "u \<in> sources as d"
      from a7 b0 have b1: "u \<in> sources (a#as) d" by auto
      then have "s' \<sim>u\<sim> t'"
      proof(cases "domain a \<leadsto> u")
        assume c0: "domain a \<leadsto> u"
        show ?thesis
        proof -
          have d0: "s \<sim>domain a\<sim> t"
            by (metis (mono_tags, lifting) CollectI UnI2 a0 b0 c0 ivpeq_def sources_Cons)
          then have "s' \<sim>u\<sim> t'" 
            by (smt (verit, ccfv_SIG) a0 a1 a2 a3 a4 a5 b1 ivpeq_def weak_step_consistent_def)
          then show ?thesis by auto
        qed
      next
        assume c0: "\<not> domain a \<leadsto> u"
        show ?thesis 
          by (smt (verit, best) a0 a1 a2 a3 a4 a5 b1 c0 ivpeq_def weak_step_consistent_def)
      qed
    }
    then show ?thesis by auto
  qed
  then show ?thesis 
    by (simp add: ivpeq_def)
qed

lemma sources_preserved_left:
  "\<lbrakk>local_respect; reachable0 s; reachable0 t; (s, s') \<in> step a; domain a \<notin> sources (a#as) u; 
   s \<approx> sources (a # as) u \<approx> t\<rbrakk> \<Longrightarrow> s' \<approx> sources as u \<approx> t"
proof -
  assume a1: "local_respect"
  assume a2: "reachable0 s"
  assume a3: "reachable0 t"
  assume a4: "(s, s') \<in> step a"
  assume a5: "domain a \<notin> sources (a#as) u"
  assume a6: "s \<approx> sources (a # as) u \<approx> t" 
  have " \<forall>d\<in>sources as u. s' \<sim>d\<sim> t"
  proof-
    {
      fix d
      assume b0: "d \<in> sources as u"
      then have b1: "\<not> domain a \<leadsto> d" 
        using a5 sources_Cons by fastforce
      from a6 b0 have b2: "s \<sim>d\<sim> t" 
        by (simp add: ivpeq_def sources_Cons)
      with b1 have "s' \<sim>d\<sim> t"
        using a1 a2 a4 local_respect_def vpeq_symmetric vpeq_transitive by blast
    }
    then show ?thesis by simp
  qed
  then show ?thesis by (simp add: ivpeq_def)
qed

theorem UnwindingTheorem_nonleakage:
    assumes p1: observed_consistent
    and     p2: weak_step_consistent
  shows nonleakage
proof(subst nonleakage_def)
  show "\<forall>as s t u. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx>sources as u\<approx> t) \<longrightarrow> s \<lhd> as \<simeq> u \<simeq> t \<lhd> as"
  proof -
    {
      fix as
      have "\<forall>s t u. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx>sources as u\<approx> t) \<longrightarrow> s \<lhd> as \<simeq> u \<simeq> t \<lhd> as"
      proof(induct as)
        case Nil
        show ?case 
        proof -
          {
            fix s t u
            assume a0: "s \<approx>sources [] u\<approx> t"
            then have a1: "s \<sim>u\<sim> t"
              by (simp add: ivpeq_def sources_Nil)
            then have "s \<lhd> [] \<simeq> u \<simeq> t \<lhd> []"  unfolding exec_equiv_def
              using observed_consistent_def p1 by auto
          }
          then show ?thesis by auto
        qed
      next
        case (Cons b bs)
        assume a0: "\<forall>s t u. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx>sources bs u\<approx> t) \<longrightarrow> s \<lhd> bs \<simeq> u \<simeq> t \<lhd> bs"
        show ?case
        proof -
          {
            fix s t u
            assume b0: "(reachable0 s) \<and> (reachable0 t)"
            assume b1: "s \<approx> sources (b # bs) u \<approx> t"
            have "\<forall>s' t'. (s, s') \<in> step  b \<and> (t, t') \<in> step b \<longrightarrow> exec_equiv  s' bs u t' bs "
              by (metis a0 b0 b1 p2 reachableStep sources_unwinding_step)
            then have "s \<lhd> (b # bs) \<simeq> u \<simeq> t \<lhd> (b # bs) " 
              using exec_equiv_def by auto
          }
          then show ?thesis
            by blast
        qed
      qed
    }
    then show ?thesis by auto
  qed
qed


theorem UnwindingTheorem_noninfluence0:
    assumes p1: observed_consistent 
    and     p2: local_respect
    and     p3: weak_step_consistent
  shows noninfluence0
proof(subst noninfluence0_def)
  show "\<forall>u as s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx>sources as u\<approx> t) \<longrightarrow> s \<lhd> as \<simeq> u \<simeq> t \<lhd> ipurge as u"
  proof-
    {
      fix as
      have "\<forall>u s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx>sources as u\<approx> t) \<longrightarrow> s \<lhd> as \<simeq> u \<simeq> t \<lhd> ipurge as u"
      proof(induct as)
        case Nil show ?case 
        proof -
          {
            fix u s t
            assume a0:"reachable0 s \<and> reachable0 t"
            assume a1:" s \<approx> sources [] u \<approx> t"
            have a2:" s \<sim>u\<sim> t" by (metis a1 insertI1 ivpeq_def sources_Nil)
            have a3:"ipurge [] u = []" by simp
            from a2 have "s \<lhd> [] \<simeq> u \<simeq> t \<lhd> []" unfolding exec_equiv_def
              using observed_consistent_def p1 by auto
            with a3 have " s \<lhd> [] \<simeq> u \<simeq> t \<lhd> ipurge [] u " by auto
          }
          then show ?thesis 
            using UnwindingTheorem_nonleakage nonleakage_def p1 p3 by fastforce
        qed
      next
        case (Cons b bs)
        assume a0:"\<forall>u s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx>sources bs u\<approx> t) \<longrightarrow> s \<lhd> bs \<simeq> u \<simeq> t \<lhd> ipurge bs u"
        show ?case 
        proof-
          {
            fix u s t
            assume b0:"reachable0 s"
            assume b1:"reachable0 t"
            assume b2:"s \<approx> sources (b # bs) u \<approx> t"
            have " s \<lhd> (b # bs) \<simeq> u \<simeq> t \<lhd> ipurge (b # bs) u"
            proof(cases "domain b \<in> sources (b # bs) u")
              assume d0: "domain b \<in> sources (b # bs) u"
              then have d1: "ipurge (b # bs) u = b # ipurge  bs u" by simp
              then have " \<forall>s' t'. (s, s') \<in> step b \<and> (t, t') \<in> step b \<longrightarrow> s' \<lhd> bs \<simeq> u \<simeq> t' \<lhd> ipurge bs u"
                by (meson a0 b0 b1 b2 p3 reachableStep sources_unwinding_step)
              then show ?thesis using b0 b1 d1 exec_equiv_both by auto
            next
              assume d0: "\<not> domain b \<in> sources (b # bs) u"
              then have d1: "ipurge (b # bs) u = ipurge bs u" by simp
              have "\<forall>s'. (s, s') \<in> step  b \<longrightarrow> s' \<lhd> bs \<simeq> u \<simeq> t \<lhd> ipurge bs u"
                by (meson a0 b0 b1 b2 d0 p2 reachableStep sources_preserved_left)
              then show ?thesis
                by (smt (verit) d1 exec_equiv_def relcomp.cases run_Cons) 
            qed
          }
          then show ?thesis
            by blast
        qed
      qed
    }
    then show ?thesis by auto
  qed
qed

end

end
