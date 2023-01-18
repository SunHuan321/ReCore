theory LRGSound
  imports Lang
begin       

subsection \<open>state definition \<close>

subsection \<open> LRG assertions \<close>
datatype lrg_assn = 
      Apure bexp
    | emp\<^sub>h
    | pointsto exp exp        (infixl "\<longmapsto>" 200)
    | star lrg_assn lrg_assn  (infixl "**" 200)
    | wand lrg_assn lrg_assn  (infixl "-\<oplus>" 200)
    | conj lrg_assn lrg_assn  (infixl "\<and>\<^sub>l\<^sub>r\<^sub>g" 200)
    | disj lrg_assn lrg_assn  (infixl "\<or>\<^sub>l\<^sub>r\<^sub>g" 200)

primrec
  sat :: "state \<Rightarrow> lrg_assn \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>S\<^sub>L" 60)
where
  "(\<sigma> \<Turnstile>\<^sub>S\<^sub>L emp\<^sub>s)      = (snd \<sigma> = Map.empty)" 
| "(\<sigma> \<Turnstile> E \<longmapsto> E')  = (dom (snd \<sigma>) = { edenot E (fst \<sigma>) } \<and> (snd \<sigma>) (edenot E (fst \<sigma>)) = Some (edenot E' (fst \<sigma>)))" 
| "(\<sigma> \<Turnstile> P ** Q)    = (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> P \<and> (fst \<sigma>, h2) \<Turnstile> Q \<and> snd \<sigma> = (h1 ++ h2) \<and> disjoint (dom h1) (dom h2))" 
| "(\<sigma> \<Turnstile> Awand P Q) = (\<forall>h. disjoint (dom (snd \<sigma>)) (dom h) \<and> (fst \<sigma>, h) \<Turnstile> P \<longrightarrow> (fst \<sigma>, snd \<sigma> ++ h) \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Apure B)   = bdenot B (fst \<sigma>)" 
| "(\<sigma> \<Turnstile> Aconj P Q) = (\<sigma> \<Turnstile> P \<and> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Adisj P Q) = (\<sigma> \<Turnstile> P \<or> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Aex PP)    = (\<exists>v. \<sigma> \<Turnstile> PP v)" 