theory Aux_for_CSL
  imports CSL_syntax
begin

lemma implies_trans : "P \<sqsubseteq> Q \<Longrightarrow> Q \<sqsubseteq> R \<Longrightarrow> P \<sqsubseteq> R"
  by (simp add: implies_def)

lemma implies_star : "P \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> P ** Q \<sqsubseteq> P' ** Q'"
  apply (simp add: implies_def) by blast

lemma rule_Aex_Pre: "\<forall>n. \<Gamma> \<turnstile> {P n} C {Q} \<Longrightarrow> \<Gamma> \<turnstile> {Aex P} C {Q}"
  using CSL_def sat.simps(8) by blast

lemma rule_Aex_Post: "\<exists>n. \<Gamma> \<turnstile> {P} C {Q n} \<Longrightarrow> \<Gamma> \<turnstile> {P} C {Aex Q}"
  using implies_def rule_conseq sat.simps(8) by blast

definition assn_equiv :: "assn \<Rightarrow> assn \<Rightarrow> bool"   (infixl " \<equiv>\<^sub>S\<^sub>L"  50)
  where " P \<equiv>\<^sub>S\<^sub>L  Q \<equiv> \<forall>\<sigma>. \<sigma> \<Turnstile> P \<longleftrightarrow> \<sigma> \<Turnstile> Q"

lemma assn_equiv_reflex: " P = Q \<Longrightarrow> P \<equiv>\<^sub>S\<^sub>L Q"
  using assn_equiv_def by blast

lemma assn_equiv_symmetry : "P \<equiv>\<^sub>S\<^sub>L Q \<Longrightarrow> Q \<equiv>\<^sub>S\<^sub>L P"
  by (simp add: assn_equiv_def)

lemma assn_equiv_trans: "\<lbrakk> P \<equiv>\<^sub>S\<^sub>L Q; Q \<equiv>\<^sub>S\<^sub>L R \<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>S\<^sub>L R "
  by (simp add: assn_equiv_def)
 
lemma Astar_commute_equiv: "P ** Q \<equiv>\<^sub>S\<^sub>L Q ** P"
  apply (simp add: assn_equiv_def)
  using map_add_commute by fastforce

lemma Astar_assoc_equiv_aux : "(s, h) \<Turnstile> P ** Q ** R \<longleftrightarrow> (s, h) \<Turnstile> P ** (Q ** R)"
proof
  assume " (s, h) \<Turnstile> P ** Q ** R"
  then show "(s, h) \<Turnstile> P ** (Q ** R)"
    apply (clarsimp, rule_tac x = h1a in exI)
    apply (rule conjI, simp)
    apply (rule_tac x = "h2a ++ h2" in exI)
    using hsimps(4) by auto
next
  assume "(s, h) \<Turnstile> P ** (Q ** R)"
  then show "(s, h) \<Turnstile> P ** Q ** R"
    apply (clarsimp, rule_tac x = "h1 ++ h1a" in exI)
    using map_add_assoc by auto
qed

lemma Astar_assoc_equiv: "P ** Q ** R \<equiv>\<^sub>S\<^sub>L P ** (Q ** R)"
  using Astar_assoc_equiv_aux assn_equiv_def by auto

lemma Astar_assoc_equiv2: "P ** Q ** R \<equiv>\<^sub>S\<^sub>L P ** R ** Q"
  using Astar_assoc_equiv Astar_comassoc assn_equiv_def by auto

lemma Astar_disj_dist: " (P ** (Q1 \<or>\<^sub>S\<^sub>L Q2)) \<equiv>\<^sub>S\<^sub>L ((P ** Q1) \<or>\<^sub>S\<^sub>L (P ** Q2))"
  apply (simp add: assn_equiv_def) by blast

lemma Aemp_equiv : "Aemp ** P \<equiv>\<^sub>S\<^sub>L P"
  using assn_equiv_def by auto

lemma Apure_conj_equiv : " (\<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Q\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L ( \<langle> (P \<and>\<^sub>b Q) \<rangle>\<^sub>S\<^sub>L )"   
  by (simp add: assn_equiv_def)

lemma Apure_Astar_equiv : "(P \<and>\<^sub>S\<^sub>L \<langle>Q\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L P ** (\<langle>Q\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  by (simp add: assn_equiv_def)

lemma Apure_subE_equiv : "  (E \<longmapsto> E' \<and>\<^sub>S\<^sub>L \<langle>[x]\<^sub>v =\<^sub>b E''\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L 
                            (E \<longmapsto> subE x E'' E' \<and>\<^sub>S\<^sub>L \<langle>[x]\<^sub>v =\<^sub>b E''\<rangle>\<^sub>S\<^sub>L)"
  apply (simp add: assn_equiv_def)
  by (metis fun_upd_triv subE_assign)

lemma Conj_true_equiv : "(P \<and>\<^sub>S\<^sub>L \<langle>[True]\<^sub>b\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L P"
  by (simp add: assn_equiv_def)

lemma Apointo_equiv : " x \<longmapsto> ([n]\<^sub>n +\<^sub>e [m]\<^sub>n) \<equiv>\<^sub>S\<^sub>L x \<longmapsto> [n + m]\<^sub>n"
  by (simp add: assn_equiv_def)

lemma safe_assn_equiv: "\<lbrakk> Pa \<equiv>\<^sub>S\<^sub>L Pb; Qa \<equiv>\<^sub>S\<^sub>L Qb ; \<Gamma> \<turnstile> {Pa} C {Qa} \<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> {Pb} C {Qb}"
  by (simp add: assn_equiv_def implies_def rule_conseq)

lemma equiv_implies : "P \<equiv>\<^sub>S\<^sub>L Q \<Longrightarrow> P \<sqsubseteq> Q"
  by (simp add: assn_equiv_def implies_def)

lemma equiv_Bbool : "(\<langle>[P]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>[Q]\<^sub>b\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L (\<langle>[(P \<and> Q)]\<^sub>b\<rangle>\<^sub>S\<^sub>L)"
  by (simp add: assn_equiv_def)

lemma assn_equiv_conj : "P \<equiv>\<^sub>S\<^sub>L Q \<Longrightarrow> (P \<and>\<^sub>S\<^sub>L R) \<equiv>\<^sub>S\<^sub>L (Q \<and>\<^sub>S\<^sub>L R)"
  by (simp add: assn_equiv_def)

lemma assn_equiv_conj_Apure : "(P ** Q \<and>\<^sub>S\<^sub>L \<langle>R\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L (P ** (Q \<and>\<^sub>S\<^sub>L \<langle>R\<rangle>\<^sub>S\<^sub>L))"
  apply (simp add: assn_equiv_def) by blast

lemma "(P ** Q ** R \<and>\<^sub>S\<^sub>L \<langle>S\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L (P ** (Q ** R \<and>\<^sub>S\<^sub>L \<langle>S\<rangle>\<^sub>S\<^sub>L))"
  using Astar_assoc_equiv assn_equiv_def by auto

lemma Aistar_equiv : " P ** Aistar (map \<G> rs) ** \<G> a  \<equiv>\<^sub>S\<^sub>L P ** Aistar (map \<G> (a # rs))"
  using Astar_assoc_equiv Astar_assoc_equiv2 assn_equiv_trans by fastforce
(* cong rule x = y \<Longrightarrow> f x = f y *)
lemma assn_equiv_cong_conj : " \<lbrakk>Pa \<equiv>\<^sub>S\<^sub>L Pb ; Qa \<equiv>\<^sub>S\<^sub>L Qb\<rbrakk> \<Longrightarrow>  (Pa \<and>\<^sub>S\<^sub>L Qa) \<equiv>\<^sub>S\<^sub>L (Pb \<and>\<^sub>S\<^sub>L Qb)"
  by (simp add: assn_equiv_def)

lemma assn_equiv_cong_disj : " \<lbrakk>Pa \<equiv>\<^sub>S\<^sub>L Pb ; Qa \<equiv>\<^sub>S\<^sub>L Qb\<rbrakk> \<Longrightarrow>  (Pa \<or>\<^sub>S\<^sub>L Qa) \<equiv>\<^sub>S\<^sub>L (Pb \<or>\<^sub>S\<^sub>L Qb)"
  by (simp add: assn_equiv_def)

lemma assn_equiv_cong_star : " \<lbrakk>Pa \<equiv>\<^sub>S\<^sub>L Pb ; Qa \<equiv>\<^sub>S\<^sub>L Qb\<rbrakk> \<Longrightarrow>  (Pa ** Qa) \<equiv>\<^sub>S\<^sub>L (Pb ** Qb)"
  by (simp add: assn_equiv_def)

(* assign rule *)
lemma assn_equiv_varread : " (([p + off]\<^sub>n \<longmapsto> [q]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<equiv>\<^sub>S\<^sub>L 
        ((([v]\<^sub>v +\<^sub>e [off]\<^sub>n) \<longmapsto> [q]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [p]\<^sub>n\<rangle>\<^sub>S\<^sub>L)"
  apply (simp add: assn_equiv_def) 
  by auto

(* auxillary proof rule *)
theorem rule_frame1:
 "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ; disjoint (fvA R) (wrC C) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {R ** P} C {R ** Q}"
  apply (drule rule_frame, simp)
  apply (rule rule_conseq, simp_all)
  by (simp_all add: Astar_commute_equiv equiv_implies)

theorem rule_frame2: 
 "\<lbrakk> \<Gamma> \<turnstile> {P} C {Q} ; disjoint (fvA Rl) (wrC C); disjoint (fvA Rr) (wrC C) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> {Rl ** P ** Rr} C {Rl ** Q ** Rr}"
  by (simp add: rule_frame rule_frame1)

theorem rule_with_true:  "\<lbrakk> \<Gamma> \<turnstile> {P ** \<Gamma> r } C {Q ** \<Gamma> r} \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile> {P} Cwith r ([True]\<^sub>b) C {Q}"
  using CSL_def rule_with sat.simps(6) by blast

theorem rule_with_true' : "\<lbrakk> \<Gamma>(r := Aemp) \<turnstile> {P ** \<Gamma> r } C {Q ** \<Gamma> r} \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile> {P} Cwith r ([True]\<^sub>b) C {Q}"
  using CSL_def rule_with' sat.simps(6) by blast

theorem rule_read_var_off : " \<lbrakk> x \<notin> fvE Ea \<union> fvE Eb \<union> fvE Ec \<union> fvAs \<Gamma> \<rbrakk> \<Longrightarrow> 
                        \<Gamma> \<turnstile> {( (Ea +\<^sub>e [off]\<^sub>n) \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L}  
                              x :=\<^sub>C \<lbrakk>Ec +\<^sub>e [off]\<^sub>n\<rbrakk> 
                     {((Ea +\<^sub>e [off]\<^sub>n) \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle> [x]\<^sub>v =\<^sub>b Eb\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "((Ec +\<^sub>e [off]\<^sub>n) \<longmapsto> Eb) ** (\<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and     
       Qa = "(((Ec +\<^sub>e [off]\<^sub>n) \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle> [x]\<^sub>v =\<^sub>b Eb\<rangle>\<^sub>S\<^sub>L) ** (\<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  using assn_equiv_def bdenot.simps(1) apply auto[1]
  using assn_equiv_def bdenot.simps(1) apply auto[1]
  by (rule rule_frame, rule rule_read, simp_all add: disjoint_def)

theorem rule_read_var : " \<lbrakk> x \<notin> fvE Ea \<union> fvE Eb \<union> fvE Ec \<union> fvAs \<Gamma> \<rbrakk> \<Longrightarrow> 
                        \<Gamma> \<turnstile> {(Ea \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L}  
                              x :=\<^sub>C \<lbrakk>Ec\<rbrakk> 
                     {(Ea \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle> [x]\<^sub>v =\<^sub>b Eb\<rangle>\<^sub>S\<^sub>L}"
    apply (rule_tac Pa = "(Ec \<longmapsto> Eb) ** (\<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
        Qa = "((Ec \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle> [x]\<^sub>v =\<^sub>b Eb\<rangle>\<^sub>S\<^sub>L) ** (\<langle>Ec =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  using assn_equiv_def  apply auto[1]
  using assn_equiv_def apply auto[1]
  by (rule rule_frame, rule rule_read, simp_all add: disjoint_def)

corollary rule_read_var_offn : " \<lbrakk> x \<notin> fvE Ea \<union> fvE Eb \<union> fvE Ec \<union> fvAs \<Gamma> \<rbrakk> \<Longrightarrow> 
                        \<Gamma> \<turnstile> {([n + off]\<^sub>n \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}  
                              x :=\<^sub>C \<lbrakk>Ec +\<^sub>e [off]\<^sub>n\<rbrakk> 
                     {([n + off]\<^sub>n \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle> [x]\<^sub>v =\<^sub>b Eb\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(([n]\<^sub>n +\<^sub>e [off]\<^sub>n) \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L" and 
  Qa = "(([n]\<^sub>n +\<^sub>e [off]\<^sub>n) \<longmapsto> Eb) \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle> [x]\<^sub>v =\<^sub>b Eb\<rangle>\<^sub>S\<^sub>L" in safe_assn_equiv)
  using assn_equiv_def  apply auto[1]
  using assn_equiv_def apply auto[1]
  by (simp add: rule_read_var_off)

theorem rule_write_var_off : "\<Gamma> \<turnstile> {((Ea +\<^sub>e [off]\<^sub>n) \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>(Eb +\<^sub>e [off]\<^sub>n)\<rbrakk> :=\<^sub>C Ec
                              {((Ea +\<^sub>e [off]\<^sub>n) \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L}"
    apply (rule_tac Pa = "((Eb +\<^sub>e [off]\<^sub>n) \<longmapsto> E) ** (\<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
        Qa = "((Eb +\<^sub>e [off]\<^sub>n) \<longmapsto> Ec)  ** (\<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  using assn_equiv_def apply auto[1]
  using assn_equiv_def apply auto[1]
  by (rule rule_frame, rule rule_write, simp add: disjoint_def)     

theorem rule_write_var : "\<Gamma> \<turnstile> {(Ea \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>Eb\<rbrakk> :=\<^sub>C Ec
                              {(Ea \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L}"
    apply (rule_tac Pa = "(Eb \<longmapsto> E) ** (\<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
        Qa = "(Eb \<longmapsto> Ec)  ** (\<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  using assn_equiv_def apply auto[1]
  using assn_equiv_def apply auto[1]
  by (rule rule_frame, rule rule_write, simp add: disjoint_def)

theorem rule_write_var_with_conj : "\<Gamma> \<turnstile> {(Ea \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>Eb\<rbrakk> :=\<^sub>C Ec
                              {(Ea \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L}"
    apply (rule_tac Pa = "((Ea \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L) ** (\<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
        Qa = "((Ea \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ea\<rangle>\<^sub>S\<^sub>L) ** (\<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  by (simp_all add: assn_equiv_def, rule rule_frame, simp add: rule_write_var, simp add: disjoint_def)

theorem rule_write_var2 : " 
                        \<Gamma> \<turnstile> {(Ea \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ec\<rangle>\<^sub>S\<^sub>L}  
                              \<lbrakk>Ea\<rbrakk> :=\<^sub>C Eb 
                     {(Ea \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b Ec\<rangle>\<^sub>S\<^sub>L}"
      apply (rule_tac Pa = "(Ea \<longmapsto> E) ** (\<langle>Eb =\<^sub>b Ec\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
        Qa = "(Ea \<longmapsto> Eb) ** (\<langle>Eb =\<^sub>b Ec\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
  using assn_equiv_def apply auto[1]
  using assn_equiv_def apply auto[1]
  by (rule rule_frame, rule rule_write, simp add: disjoint_def)

theorem rule_False : "user_cmd C \<Longrightarrow> \<Gamma> \<turnstile> {\<langle>[False]\<^sub>b\<rangle>\<^sub>S\<^sub>L} C {Q}"
  by (simp add: CSL_def)

theorem rule_write_offn : "\<Gamma> \<turnstile> {([n + off]\<^sub>n \<longmapsto> E) }
                                \<lbrakk>([n]\<^sub>n +\<^sub>e [off]\<^sub>n)\<rbrakk> :=\<^sub>C Ec
                              {(([n + off]\<^sub>n) \<longmapsto> Ec)}"
  apply (rule_tac Pa = "(([n]\<^sub>n +\<^sub>e [off]\<^sub>n) \<longmapsto> E)" and Qa = "(([n]\<^sub>n +\<^sub>e [off]\<^sub>n) \<longmapsto> Ec)" in safe_assn_equiv)
  using assn_equiv_def apply auto[1] using assn_equiv_def apply auto[1]
  by (simp add: rule_write)

corollary rule_write_var_offn : "\<Gamma> \<turnstile> {([n + off]\<^sub>n \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>(Eb +\<^sub>e [off]\<^sub>n)\<rbrakk> :=\<^sub>C Ec
                              {(([n + off]\<^sub>n) \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(([n]\<^sub>n +\<^sub>e [off]\<^sub>n) \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L" and 
      Qa = "(([n]\<^sub>n +\<^sub>e [off]\<^sub>n) \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L" in safe_assn_equiv)
  using assn_equiv_def apply auto[1]
  using assn_equiv_def apply auto[1]
  by (simp add: rule_write_var_off)

corollary rule_write_var_offn_with_conj : "\<Gamma> \<turnstile> {([n + off]\<^sub>n \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>(Eb +\<^sub>e [off]\<^sub>n)\<rbrakk> :=\<^sub>C Ec
                              {(([n + off]\<^sub>n) \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(([n + off]\<^sub>n \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and
  Qa = "((([n + off]\<^sub>n) \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) ** (\<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
    apply (simp_all add: assn_equiv_def, rule rule_frame, simp add: rule_write_var_offn)
  by (simp add: disjoint_def)

lemma rule_write_var_offn2 : "\<Gamma> \<turnstile> {([n + off]\<^sub>n \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ed\<rangle>\<^sub>S\<^sub>L}
                                \<lbrakk>(Eb +\<^sub>e [off]\<^sub>n)\<rbrakk> :=\<^sub>C Ec
                              {(([n + off]\<^sub>n) \<longmapsto> Ed) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ed\<rangle>\<^sub>S\<^sub>L}"
    apply (rule_tac Pa = "(([n + off]\<^sub>n) \<longmapsto> E) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ed\<rangle>\<^sub>S\<^sub>L" and 
      Qa = "(([n + off]\<^sub>n) \<longmapsto> Ec) \<and>\<^sub>S\<^sub>L \<langle>Eb =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L \<langle>Ec =\<^sub>b Ed\<rangle>\<^sub>S\<^sub>L" in safe_assn_equiv)
  using assn_equiv_def apply auto[1] using assn_equiv_def apply auto[1]
  by (simp add: rule_write_var_offn_with_conj)

theorem rule_read_with_conj : "x \<notin> fvE E \<union> fvE E' \<union> fvAs \<Gamma> \<union> fvB P \<Longrightarrow> 
            \<Gamma> \<turnstile> {(E \<longmapsto> E') \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L}
              x :=\<^sub>C \<lbrakk>E\<rbrakk>
            {((E \<longmapsto> E') \<and>\<^sub>S\<^sub>L \<langle>P\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L \<langle>[x]\<^sub>v =\<^sub>b E'\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "(E \<longmapsto> E') ** ( \<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
         Qa = "((E \<longmapsto> E') \<and>\<^sub>S\<^sub>L \<langle>[x]\<^sub>v =\<^sub>b E'\<rangle>\<^sub>S\<^sub>L) ** ( \<langle>P\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
    apply (simp_all add: assn_equiv_def) apply auto
  by (rule rule_frame, rule rule_read, simp_all add: disjoint_def)

theorem rule_assign1 : "x \<notin> fvAs \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> { subA x E Q \<and>\<^sub>S\<^sub>L Aemp } Cassign x E {Q \<and>\<^sub>S\<^sub>L Aemp}"
  apply (clarsimp simp add: CSL_def)
  apply (case_tac n, simp, clarsimp)
  apply (rule conjI, clarsimp, erule aborts.cases, simp_all)
  apply (clarsimp, erule red.cases, simp_all)
  by (rule_tac x= Map.empty in exI, rule_tac x=hJ in exI, clarsimp simp add: subA_assign)

theorem rule_assign_num : "v \<notin> fvAs \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> {\<langle>[True]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp} v :=\<^sub>C [n]\<^sub>n {\<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp}"
  apply (rule_tac Pa = "subA v ([n]\<^sub>n) (\<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L Aemp" and Qa = "\<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp" 
  in safe_assn_equiv, simp add: assn_equiv_def, simp add: assn_equiv_def)
  by (rule rule_assign1, simp)

theorem rule_assign_num1 : "v \<notin> fvAs \<Gamma> \<union> fvA P \<Longrightarrow> \<Gamma> \<turnstile> {P} v :=\<^sub>C [n]\<^sub>n { P \<and>\<^sub>S\<^sub>L \<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L}"
  apply (rule_tac Pa = "P ** (\<langle>[True]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and Qa = "P ** (\<langle>[v]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in 
  safe_assn_equiv, simp add: assn_equiv_def, simp add: assn_equiv_def)
  by (rule rule_frame1, rule rule_assign_num, simp_all add: disjoint_def)

theorem rule_disj':
 "\<lbrakk> \<Gamma> \<turnstile> {P1} C {Q}; \<Gamma> \<turnstile> {P2} C {Q} \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> {Adisj P1 P2} C {Q}"
  apply (rule_tac Pa = "P1 \<or>\<^sub>S\<^sub>L P2" and Qa = "Q \<or>\<^sub>S\<^sub>L Q" in safe_assn_equiv)
  by (simp_all add: assn_equiv_def, simp add: rule_disj)


end