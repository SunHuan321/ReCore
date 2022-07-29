theory Event_Lang 
imports CSLsound
begin

section \<open>Abstract Syntax of Event Language\<close>

datatype event = 
    AnonyEvent "cmd"
    | BasicEvent "bexp \<times> cmd"                  
type_synonym revent = "rname list \<times> event"

datatype esys = 
   EvtSeq revent esys
   | EvtSys "revent set"

type_synonym resys = "rname list \<times> esys"
type_synonym paresys = "resys list"
type_synonym rparesys = "rname list \<times> paresys"

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

definition is_basicrevt :: "revent \<Rightarrow> bool"
  where "is_basicrevt re = is_basicevt (snd re)"

definition is_anonyrevt :: "revent \<Rightarrow> bool"
  where "is_anonyrevt re = is_anonyevt (snd re)"

lemma basicrevt_isnot_anony: "is_basicrevt re \<Longrightarrow> \<not> is_anonyrevt re"
  using anonyevt_isnot_basic is_anonyrevt_def is_basicrevt_def by auto

end


  

