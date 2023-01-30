theory Aux_for_RGSep
  imports RGSepSound Aux_for_CSL
begin

definition RGassn_equiv :: "rgsep_assn \<Rightarrow> rgsep_assn \<Rightarrow> bool"   (infixl " \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p"  50)
  where " P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Q \<equiv> \<forall>\<sigma>. \<sigma> \<^sup>\<Turnstile>rgsep P \<longleftrightarrow> \<sigma> \<^sup>\<Turnstile>rgsep Q"


lemma RGequiv_implies : "P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Q \<Longrightarrow> P \<^sup>\<sqsubseteq>rgsep Q"
  by (simp add: RGassn_equiv_def rgsep_implies_def)

lemma RGassn_equiv_reflex: " P = Q \<Longrightarrow> P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Q"
  by (simp add: RGassn_equiv_def)

lemma RGassn_equiv_symmetry : "P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Q \<Longrightarrow> Q \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p P"
  by (simp add: RGassn_equiv_def)

lemma RGassn_equiv_trans : "\<lbrakk>P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Q; Q \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p R"
  by (simp add: RGassn_equiv_def)

lemma RGAstar_commute_equiv: "RGstar P Q \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p RGstar Q P"
  apply (simp add: RGassn_equiv_def)
  using map_add_commute by fastforce

lemma RGassn_equiv_local : "P \<equiv>\<^sub>S\<^sub>L Q \<Longrightarrow> RGlocal P \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p RGlocal Q"
  by (simp add: RGassn_equiv_def assn_equiv_def)

lemma RGAstar_assoc_equiv_aux : "\<sigma> \<^sup>\<Turnstile>rgsep RGstar (RGstar P Q) R \<longleftrightarrow> \<sigma> \<^sup>\<Turnstile>rgsep RGstar P (RGstar Q R)"
proof
  assume " \<sigma> \<^sup>\<Turnstile>rgsep RGstar (RGstar P Q) R"
  then show "\<sigma> \<^sup>\<Turnstile>rgsep RGstar P (RGstar Q R)"
    apply (clarsimp, rule_tac x = h1a in exI)
    apply (rule conjI, simp)
    apply (rule_tac x = "h2a ++ h2" in exI)
    using hsimps(4) by auto
next
  assume "\<sigma> \<^sup>\<Turnstile>rgsep RGstar P (RGstar Q R)"
  then show "\<sigma> \<^sup>\<Turnstile>rgsep RGstar (RGstar P Q) R"
    apply (clarsimp, rule_tac x = "h1 ++ h1a" in exI)
    using map_add_assoc by auto
qed

(* cong rule x = y \<Longrightarrow> f x = f y *)

lemma RGassn_equiv_cong_star : " \<lbrakk>Pa \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Pb ; Qa \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Qb\<rbrakk> \<Longrightarrow> RGstar Pa Qa \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p RGstar Pb Qb"
  by (simp add: RGassn_equiv_def)

lemma RGAstar_assoc_equiv: "RGstar (RGstar P Q) R \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p RGstar P (RGstar Q R)"
  by (meson RGAstar_assoc_equiv_aux RGassn_equiv_def)

lemma RGAstar_assoc_equiv2: "RGstar (RGstar P Q) R \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p RGstar P (RGstar R Q)"
  apply (rule_tac Q = "RGstar P (RGstar Q R)" in RGassn_equiv_trans)
   apply (simp add: RGAstar_assoc_equiv)
  apply (rule RGassn_equiv_cong_star)
   apply (simp add: RGassn_equiv_reflex, simp add: RGAstar_commute_equiv)
  done

(* auxillary proof rule *)

theorem RGequiv_safe : "\<lbrakk>R ,G \<^sup>\<turnstile>rgsep {P} C {Q}; P' \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p P; Q \<equiv>\<^sub>r\<^sub>g\<^sub>s\<^sub>e\<^sub>p Q'\<rbrakk> \<Longrightarrow>
                       R ,G \<^sup>\<turnstile>rgsep {P'} C {Q'}"
  apply (rule_tac RGrule_conseq, simp_all)
     apply (simp add: RGequiv_implies, simp add: RGequiv_implies)
   apply (simp_all add: RGsubset_def)
  done

theorem RGrule_frame1:
 "\<lbrakk> Rely ,Guar \<^sup>\<turnstile>rgsep {P} C {Q} ; disjoint (fvAA R) (wrC C);
  stable R [] (RGUnion Rely Guar)\<rbrakk>
  \<Longrightarrow> Rely ,Guar \<^sup>\<turnstile>rgsep {RGstar R P} C {RGstar R Q}"
  apply (rule_tac R = "Rely" and G = "Guar" and P = "RGstar P R" and Q = "RGstar Q R" in RGrule_conseq)
      apply (simp add: RGrule_frame)
     apply (simp add: RGAstar_commute_equiv RGequiv_implies)
  apply (simp add: RGAstar_commute_equiv RGequiv_implies)
   apply (simp_all add: RGsubset_def)
  done

theorem RGrule_with_true:  "\<lbrakk> R, G  \<^sup>\<turnstile>rgsep {RGstar P (RGlocal p)} C {RGstar Q (RGlocal q)};
     \<not> frgnA Q r; R r = {}; \<forall>s h h'. (s, h) \<Turnstile> p \<longrightarrow> (s, h') \<Turnstile> q \<longrightarrow> (h, h') \<in> G r;
     disjoint (fvA p) (wrC C); stable P [] R ; stable Q [] R\<rbrakk> 
    \<Longrightarrow> R, G  \<^sup>\<turnstile>rgsep {RGstar P (RGshared r p)} (Cwith r ([True]\<^sub>b) C) {RGstar Q (RGshared r q)}"
  apply (rule RGrule_with, simp_all)
  apply (erule RGequiv_safe)
   apply (rule RGassn_equiv_cong_star, simp add: RGassn_equiv_reflex)
   apply (rule RGassn_equiv_local, simp add: Conj_true_equiv)
  apply (rule RGassn_equiv_cong_star, simp_all add: RGassn_equiv_reflex)
  done

end