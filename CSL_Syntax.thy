theory CSL_Syntax
  imports CSLsound
begin

notation Cseq           ("(_;;/ _)" [60,61] 60)
notation Cassign        ("(_ :=\<^sub>C/ _)" [70, 65] 61)
notation Cread          ("(_ :=\<^sub>C/ \<lbrakk>_\<rbrakk>)" [70, 65] 61)
notation Cwrite         ("(\<lbrakk>_\<rbrakk> :=\<^sub>C/ _)" [70, 65] 61)
notation Calloc         ("(_ :=\<^sub>C/ ALLOC(_))" [70, 65] 61)
notation Cdispose       ("DISPOSE(_)"  61)
notation Cif            ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
notation Cwhile         ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)
notation Cwith          ("(0WITH _/ WHEN _/  DO_ /OD)" [0, 0, 0] 61)
notation Cresource      ("(0RESOURCE _/ IN _)" [0, 0] 61)
notation Cpar           ("_//\<parallel>//_" [60,57] 57)


(*
syntax
  "_Cassign"  :: "var \<Rightarrow> exp \<Rightarrow> cmd"                    ("(_ :=/ _)" [70, 65] 61)
  "_Cread"    :: "var \<Rightarrow> exp \<Rightarrow> cmd"                    ("(_ :=/ \<lbrakk>_\<rbrakk>)" [70, 65] 61)
  "_Cwrite"   :: "exp \<Rightarrow> exp \<Rightarrow> cmd"                    ("(\<lbrakk>_\<rbrakk> :=/ \<lbrakk>_\<rbrakk>)" [70, 65] 61)
  "_Calloc"   :: "var \<Rightarrow> exp \<Rightarrow> cmd"                    ("(_ :=/ ALLOC(_))" [70, 65] 61)
  "_Cdispoe"  :: "exp \<Rightarrow> cmd"                           ("DISPOSE(_)"  61)
  "_Cif"      :: "bexp \<Rightarrow> cmd \<Rightarrow> cmd \<Rightarrow> cmd"            ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cif2"      :: "bexp \<Rightarrow> cmd \<Rightarrow> cmd"                  ("(0IF _ THEN _ FI)" [0,0] 56)
  "_Cwhile"   :: "bexp \<Rightarrow> cmd \<Rightarrow> cmd"                   ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)
  "_Cwith"    :: "rname \<Rightarrow> bexp \<Rightarrow> cmd \<Rightarrow> cmd"          ("(0WITH _/ WHEN _/  DO_ /OD)" [0, 0, 0] 61)
  "_Cwith2"   :: "rname \<Rightarrow> cmd \<Rightarrow> cmd"                  ("(0WITH _/  DO_ /OD)" [0, 0] 61)

translations
  "x := E" \<rightharpoonup> "CONST Cassign x E"
  "x := \<lbrakk>E\<rbrakk>" \<rightharpoonup> "CONST Cread x E"
  "\<lbrakk>E1\<rbrakk> := \<lbrakk>E2\<rbrakk>" \<rightharpoonup> "CONST Cwrite E1 E2"
  "x := ALLOC(E)" \<rightharpoonup> "CONST Calloc x E"
  "DISPOSE (E)" \<rightharpoonup> "CONST Cdispose E"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cif b c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE (CONST Cskip) FI"
  "WHILE b DO c OD" \<rightharpoonup> "CONST Cwhile b c"
  "WITH r WHEN b DO c OD" \<rightharpoonup> "CONST Cwith r b c"
*)


end





