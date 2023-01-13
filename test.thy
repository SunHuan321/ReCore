theory test
  imports Aux_for_CSL
begin

lemma Example1 : " var \<notin> fvAs \<Gamma> \<Longrightarrow> var \<noteq> ''x'' \<Longrightarrow>
            \<Gamma> \<turnstile> { [''x'']\<^sub>v \<longmapsto> ([n]\<^sub>n) }
              var :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
              \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [var]\<^sub>v +\<^sub>e [2]\<^sub>n  
            {[''x'']\<^sub>v \<longmapsto> ([n]\<^sub>n +\<^sub>e [2]\<^sub>n)}"
  apply (rule_tac Q = "(\<langle>[var]\<^sub>v =\<^sub>b [n]\<^sub>n \<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp) **  ([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n)" in rule_seq)
   apply (rule_tac Pa = "[''x'']\<^sub>v \<longmapsto> [n]\<^sub>n" and 
          Qa = "[''x'']\<^sub>v \<longmapsto> [n]\<^sub>n \<and>\<^sub>S\<^sub>L \<langle>[var]\<^sub>v =\<^sub>b [n]\<^sub>n \<rangle>\<^sub>S\<^sub>L" in safe_assn_equiv)
     apply (simp add: assn_equiv_reflex)
  using Apure_Astar_equiv Astar_commute_equiv assn_equiv_trans apply blast
   apply (rule rule_read, simp)
  apply (rule_tac P = "(\<langle>[var]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp) ** ([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n)" and
                  Q = "(\<langle>[var]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L) \<and>\<^sub>S\<^sub>L ([''x'']\<^sub>v) \<longmapsto> (([n]\<^sub>n) +\<^sub>e ([2]\<^sub>n))" 
                  in rule_conseq)
    apply (rule_tac Pa = "([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n) ** (\<langle>([var]\<^sub>v) =\<^sub>b ([n]\<^sub>n)\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and 
                    Qa = "([''x'']\<^sub>v \<longmapsto> ([var]\<^sub>v +\<^sub>e [2]\<^sub>n)) ** (\<langle>[var]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
                    in safe_assn_equiv)
      apply (simp add: Astar_commute_equiv)
  using assn_equiv_def apply auto[1]
    apply (rule_tac R = "(\<langle>[var]\<^sub>v =\<^sub>b [n]\<^sub>n\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in rule_frame)
     apply (rule rule_write, simp)
  using implies_def apply blast
  using implies_def by auto

lemma even_equiv1 :"nat_even n \<equiv>\<^sub>S\<^sub>L (\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp) ** ([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n)"
  apply (simp add: nat_even_def)
  apply (rule_tac Q = "([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n) ** (\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in assn_equiv_trans)
   apply (rule_tac Q  = "([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n) \<and>\<^sub>S\<^sub>L \<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L" in assn_equiv_trans)
  using assn_equiv_def apply auto[1]
   apply (simp add: Apure_Astar_equiv)
  by (simp add: Astar_commute_equiv)

lemma even_equiv2 : "nat_even n \<equiv>\<^sub>S\<^sub>L ([''x'']\<^sub>v \<longmapsto> [n]\<^sub>n) ** (\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)"
  using Astar_commute_equiv even_equiv1 assn_equiv_trans by blast

lemma Example2 : " var \<notin> fvAs \<Gamma> \<Longrightarrow> var \<noteq> ''x'' \<Longrightarrow>
           \<Gamma> \<turnstile> {nat_even n}
           var :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
           \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [var]\<^sub>v +\<^sub>e [2]\<^sub>n
           {nat_even (n + 2)}"
  apply (rule_tac P = "nat_even n" and 
         Q = "\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L ([''x'']\<^sub>v) \<longmapsto> (([n]\<^sub>n) +\<^sub>e ([2]\<^sub>n))" in rule_conseq)
  apply (rule_tac Pa = "([''x'']\<^sub>v) \<longmapsto> ([n]\<^sub>n) ** (\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" and
         Qa = "([''x'']\<^sub>v) \<longmapsto> (([n]\<^sub>n) +\<^sub>e ([2]\<^sub>n)) ** (\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in safe_assn_equiv)
      apply (simp add: even_equiv2 assn_equiv_symmetry)
  using assn_equiv_def apply auto[1]
    apply (rule_tac R = "(\<langle>[even n]\<^sub>b\<rangle>\<^sub>S\<^sub>L \<and>\<^sub>S\<^sub>L Aemp)" in rule_frame, simp_all)
    apply (simp add: Example1)
   apply (simp add: implies_def)
  apply (simp add: nat_even_def)
  apply (rule equiv_implies, simp add: assn_equiv_def)
  done

lemma Example3_lemma1 : " var \<notin> fvAs \<Gamma> \<Longrightarrow> var \<noteq> ''x'' \<Longrightarrow> \<forall>m. \<exists>n. 
           \<Gamma> \<turnstile> {nat_even m}
           var :=\<^sub>C \<lbrakk>([''x'']\<^sub>v)\<rbrakk> ;;
           \<lbrakk>([''x'']\<^sub>v)\<rbrakk> :=\<^sub>C  ([var]\<^sub>v) +\<^sub>e ([2]\<^sub>n)
           {nat_even n}"
  apply (clarify, rule_tac x = "m + 2" in exI)
  using Example2 by auto

lemma Example3_lemma2:  " var \<notin> fvAs \<Gamma> \<Longrightarrow> var \<noteq> ''x'' \<Longrightarrow> 
           \<Gamma> \<turnstile> {Aex nat_even}
           var :=\<^sub>C \<lbrakk>([''x'']\<^sub>v)\<rbrakk> ;;
           \<lbrakk>([''x'']\<^sub>v)\<rbrakk> :=\<^sub>C  ([var]\<^sub>v) +\<^sub>e ([2]\<^sub>n)
           {Aex nat_even}"
  by (simp add: Example3_lemma1 rule_Aex_Pre rule_Aex_Post)

lemma Example3_lemma3: " var \<notin> fvAs \<Gamma> \<Longrightarrow> \<Gamma> ''r'' = Aex nat_even \<Longrightarrow> var \<noteq> ''x'' \<Longrightarrow>
            \<Gamma> \<turnstile> {Aemp}
           WITH ''r'' WHEN [True]\<^sub>b DO
           var :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
           \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [var]\<^sub>v +\<^sub>e [2]\<^sub>n
           OD
           {Aemp}"
  apply (rule rule_with_true)
  apply (rule_tac Pa = "\<Gamma> ''r''" and Qa = "\<Gamma> ''r''" in safe_assn_equiv)
    apply (simp_all add: Aemp_equiv assn_equiv_symmetry)
  by (simp add: Example3_lemma2)

lemma Example3 : "\<lbrakk> v1 \<notin> fvAs (\<Gamma>(''r'' := Aex nat_even)) ; 
                   v2 \<notin> fvAs (\<Gamma>(''r'' := Aex nat_even)); 
                   v1 \<noteq> ''x''; v2 \<noteq> ''x''; v1 \<noteq> v2\<rbrakk> \<Longrightarrow> 
      \<Gamma> \<turnstile> {Aex nat_even}
           RESOURCE ''r'' IN
           (
           WITH ''r'' WHEN [True]\<^sub>b DO
            v1 :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
            \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [v1]\<^sub>v +\<^sub>e [2]\<^sub>n
           OD
           \<parallel>
           WITH ''r'' WHEN [True]\<^sub>b DO
            v2 :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
            \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [v2]\<^sub>v +\<^sub>e [2]\<^sub>n
           OD  
           )                    
          {Aex nat_even}"
  apply (rule_tac Pa = "Aemp ** (Aex nat_even)" and Qa = "Aemp ** (Aex nat_even)" in safe_assn_equiv)
    apply (simp_all add: Aemp_equiv)
  apply (rule rule_resource)
   apply (rule_tac Pa = "Aemp ** Aemp" and Qa = "Aemp ** Aemp" in safe_assn_equiv)
  apply (simp_all add: Aemp_equiv)
   apply (rule rule_par, simp_all add: Example3_lemma3)
    apply (simp_all add: disjoint_def)
  by (simp add: nat_even_def)

lemma "fvC (WITH ''r'' WHEN [True]\<^sub>b DO
            v2 :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
            \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [v2]\<^sub>v +\<^sub>e [2]\<^sub>n
           OD) = {v2 , ''x''}"
  by (simp add: insert_commute)

lemma "wrC (WITH ''r'' WHEN [True]\<^sub>b DO
            v1 :=\<^sub>C \<lbrakk>[''x'']\<^sub>v\<rbrakk> ;;
            \<lbrakk>[''x'']\<^sub>v\<rbrakk> :=\<^sub>C  [v1]\<^sub>v +\<^sub>e [2]\<^sub>n
           OD) = {v1}"
  apply (simp)
lemma Example4: "''x'' \<notin> fvAs \<Gamma> \<Longrightarrow> \<Gamma> ''r'' =  [''x'']\<^sub>v \<longmapsto> [''y'']\<^sub>v \<Longrightarrow>
                     \<Gamma> \<turnstile> 
                      { Aemp}
                       ''x'' :=\<^sub>C [''x'']\<^sub>v  +\<^sub>e [2]\<^sub>n
                     { Aemp}"
  by (drule_tac E = "[''x'']\<^sub>v +\<^sub>e [2]\<^sub>n" and Q = "Aemp" in rule_assign, simp)


end