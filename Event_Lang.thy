theory Event_Lang 
imports Lang
begin

section \<open>Abstract Syntax of Event Language\<close>

datatype event = 
    AnonyEvent "cmd"
    | BasicEvent "bexp \<times> cmd"   

datatype esys = 
   EvtSeq event esys
   | EvtSys "event set"

type_synonym paresys = "esys list"
type_synonym rparesys = "rname list \<times> esys list"

section \<open>Some Lemmas of Abstract Syntax\<close>

primrec is_basicevt :: "event \<Rightarrow> bool"
  where "is_basicevt (AnonyEvent _) = False" |
        "is_basicevt (BasicEvent _) = True"

primrec is_anonyevt :: "event \<Rightarrow> bool"
  where "is_anonyevt (AnonyEvent _) = True" |
        "is_anonyevt (BasicEvent _) = False"

lemma basicevt_isnot_anony: "is_basicevt e \<Longrightarrow> \<not> is_anonyevt e"
  by (metis event.exhaust is_anonyevt.simps(2) is_basicevt.simps(1)) 

lemma anonyevt_isnot_basic: "is_anonyevt e \<Longrightarrow> \<not> is_basicevt e"
  using basicevt_isnot_anony by auto

lemma evtseq_ne_es: "EvtSeq e es \<noteq> es"
  apply(induct es)
  apply auto[1]
  by simp

end


  

