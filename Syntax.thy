theory Syntax
  imports CSLsound
begin

notation Cseq ("(_;;/ _)" [60,61] 60)


syntax
  "_Assign" :: "var \<Rightarrow> exp \<Rightarrow> cmd"                     ("(_ :=/ _)" [70, 65] 61)
  "_Read"   :: "var \<Rightarrow> exp \<Rightarrow> cmd"                     ("(_ :=/ *_)" [70, 65] 61)
  "_Write"  :: "exp \<Rightarrow> exp \<Rightarrow> cmd"                     ("(*_ :=/ *_)" [70, 65] 61)
  "_Cond"   :: "bexp \<Rightarrow> cmd \<Rightarrow> cmd \<Rightarrow> cmd "            ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cond2"  :: "bexp \<Rightarrow> cmd \<Rightarrow> cmd"                    ("(0IF _ THEN _ FI)" [0,0] 56)
  "_While"  :: "bexp \<Rightarrow> cmd \<Rightarrow> cmd"                    ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)

translations
  "x := a"  \<rightharpoonup> "CONST Cassign x a"
  "x := *p"  \<rightharpoonup> "CONST Cread x p"
  "*p := *q"  \<rightharpoonup> "CONST Cwrite p q"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cif b c1 c2"         
  "WHILE b DO c OD" \<rightharpoonup> "CONST Cwhile b c"
  

end