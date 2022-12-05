theory Lang
imports Main VHelper
begin

text {* This file defines the syntax and semantics of the programming language
  used by O'Hearn and Brookes. For simplicity, we do not allow resource-owned
  variables. *}

text {* (Adapted to Isabelle 2016-1 by Qin Yu and James Brotherston) *}

subsection {* Language syntax and semantics *}

text {* We define the syntax and the operational semantics of the programming 
language of O'Hearn and Brookes. *}

type_synonym  var   = string                (*r Variables *)
type_synonym  rname = string                (*r Resource names *)
type_synonym  heap  = "(nat \<rightharpoonup> nat)"        (*r Heaps *)
type_synonym  stack = "(var \<Rightarrow> nat)"        (*r Stacks *)
type_synonym  state = "stack \<times> heap"        (*r States *)
type_synonym  rnames = "rname list"          (*r List of Resource names *)

datatype exp =                  (*r Arithmetic expressions *)
    Evar var                    (*r Variable *)
  | Enum nat                    (*r Constant *)
  | Eplus exp exp               (*r Addition *)

datatype bexp =                 (*r Boolean expressions *)
    Beq exp exp                 (*r Equality of expressions *)
  | Band bexp bexp              (*r Conjunction *)
  | Bnot bexp                   (*r Negation *)
  | Bbool bool                 

datatype cmd =                  (*r Commands *)
    Cskip                       (*r Empty command *)
  | Cassign var exp             (*r Assignment *)
  | Cread   var exp             (*r Memory load *)
  | Cwrite  exp exp             (*r Memory store *)
  | Calloc  var exp             (*r Memory allocation *)
  | Cdispose exp                (*r Memory de-allocation *)
  | Cseq   cmd cmd              (*r Sequential composition *)
  | Cpar   cmd cmd              (*r Parallel composition *)
  | Cif    bexp cmd cmd         (*r If-then-else *)
  | Cwhile bexp cmd             (*r While loops *)
  | Clocal var exp cmd          (*r Local variable declaration *)
  | Cinlocal var nat cmd        (*r Local variable declaration (runtime) *) 
  | Cresource rname cmd         (*r Resource declaration *)
  | Cresources rnames cmd   
  | Cwith     rname bexp cmd    (*r Conditional critical region *)
  | Cinwith   rname cmd         (*r Conditional critical region (runtime) *)

text {* Arithmetic expressions (@{text exp}) consist of variables, constants, and
arithmetic operations. Boolean expressions (@{text bexp}) consist of comparisons
between arithmetic expressions.  Commands (@{text cmd}) include the empty command,
variable assignments, memory reads, writes, allocations and deallocations,
sequential and parallel composition, conditionals, while loops, local variable
declarations, resource declarations and conditional critical regions (CCRs).
There are two command forms (@{text Cinlocal}, @{text Cinwith}) that represent 
partially executed local variable declarations and CCRs and do not appear
in user programs. This restriction is captured by the following definition: *}

primrec 
  user_cmd :: "cmd \<Rightarrow> bool"
where
    "user_cmd Cskip            = True"
  | "user_cmd (Cassign x E)    = True"
  | "user_cmd (Cread x E)      = True"
  | "user_cmd (Cwrite E E')    = True"
  | "user_cmd (Calloc x E)     = True"
  | "user_cmd (Cdispose E)     = True"
  | "user_cmd (Cseq C1 C2)     = (user_cmd C1 \<and> user_cmd C2)"
  | "user_cmd (Cpar C1 C2)     = (user_cmd C1 \<and> user_cmd C2)"
  | "user_cmd (Cif B C1 C2)    = (user_cmd C1 \<and> user_cmd C2)"
  | "user_cmd (Cwhile B C)     = user_cmd C"
  | "user_cmd (Clocal x E C)   = user_cmd C"
  | "user_cmd (Cinlocal x v C) = False"
  | "user_cmd (Cresource r C)  = user_cmd C"
  | "user_cmd (Cresources rs C) = user_cmd C"
  | "user_cmd (Cwith r B C)    = user_cmd C"
  | "user_cmd (Cinwith r C)    = False"

text {* The following function returns the set of locks that a command is
currently holding. *} 

primrec 
  locked :: "cmd \<Rightarrow> rname set"
where
    "locked Cskip            = {}"
  | "locked (Cassign x E)    = {}"
  | "locked (Cread x E)      = {}"
  | "locked (Cwrite E E')    = {}"
  | "locked (Calloc x E)     = {}"
  | "locked (Cdispose E)     = {}"
  | "locked (Cseq C1 C2)     = (locked C1)"
  | "locked (Cpar C1 C2)     = (locked C1 \<union> locked C2)"
  | "locked (Cif B C1 C2)    = {}"
  | "locked (Cwhile B C)     = {}"
  | "locked (Clocal x E C)   = {}"
  | "locked (Cinlocal x v C) = (locked C)"
  | "locked (Cresource r C)  = (locked C - {r})"
  | "locked (Cresources rs C) = (locked C - set rs)"
  | "locked (Cwith r B C)    = {}"
  | "locked (Cinwith r C)    = ({r} \<union> locked C)"

text {* Now the same definition, but return a list of locks that the
  command is currently holding in some fixed order. This defnition 
  is needed to work around the deep embedding of assertions. *}

primrec 
  llocked :: "cmd \<Rightarrow> rname list"
where
    "llocked Cskip            = []"
  | "llocked (Cassign x E)    = []"
  | "llocked (Cread x E)      = []"
  | "llocked (Cwrite E E')    = []"
  | "llocked (Calloc x E)     = []"
  | "llocked (Cdispose E)     = []"
  | "llocked (Cseq C1 C2)     = llocked C1"
  | "llocked (Cpar C1 C2)     = (llocked C1 @ llocked C2)"
  | "llocked (Cif B C1 C2)    = []"
  | "llocked (Cwhile B C)     = []"
  | "llocked (Clocal x E C)   = []"
  | "llocked (Cinlocal x v C) = llocked C"
  | "llocked (Cresource r C)  = (removeAll r (llocked C))"
  | "llocked (Cresources rs C) = (list_minus (llocked C) rs)"
  | "llocked (Cwith r B C)    = []"
  | "llocked (Cinwith r C)    = (r # llocked C)"

lemma locked_eq: "locked C = set (llocked C)"
by (induct C, simp_all)

subsubsection {* Semantics of expressions *}

text {* Denotational semantics for arithmetic and boolean expressions. *}

primrec
  edenot :: "exp \<Rightarrow> stack \<Rightarrow> nat"
where
    "edenot (Evar v) s      = s v"
  | "edenot (Enum n) s      = n"
  | "edenot (Eplus e1 e2) s = edenot e1 s + edenot e2 s"

primrec
  bdenot :: "bexp \<Rightarrow> stack \<Rightarrow> bool" 
where
    "bdenot (Beq e1 e2) s   = (edenot e1 s = edenot e2 s)"
  | "bdenot (Band b1 b2) s  = (bdenot b1 s \<and> bdenot b2 s)"
  | "bdenot (Bnot b) s      = (\<not> bdenot b s)"
  | "bdenot (Bbool b) s     =  b"

subsubsection {* Semantics of commands *}

text {* We give a standard small-step operational semantics to commands
  with configurations being command-state pairs. *}

text {*
  For illustration purposes, our semantics for @{term "Cwrite E E'"} is unusual
  in that if @{term "E"} is not allocated, then the command will allocate @{term "E"}
  and do the assignment.  Requiring that @{term "(edenot E s) \<in> dom h"} does 
  not change the proof. *}

inductive
  red :: "cmd \<Rightarrow> state \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> bool"
where
  red_Seq1[intro]: "red (Cseq Cskip C) \<sigma> C \<sigma>"
| red_Seq2[elim]: "red C1 \<sigma> C1' \<sigma>' \<Longrightarrow> red (Cseq C1 C2) \<sigma> (Cseq C1' C2) \<sigma>'" 
| red_If1[intro]: "bdenot B (fst \<sigma>) \<Longrightarrow> red (Cif B C1 C2) \<sigma> C1 \<sigma>"
| red_If2[intro]: "\<not> bdenot B (fst \<sigma>) \<Longrightarrow> red (Cif B C1 C2) \<sigma> C2 \<sigma>"
| red_Par1[elim]: "\<lbrakk> red C1 \<sigma> C1' \<sigma>'; disjoint (locked C1') (locked C2) \<rbrakk> \<Longrightarrow> red (Cpar C1 C2) \<sigma> (Cpar C1' C2) \<sigma>'" 
| red_Par2[elim]: "\<lbrakk> red C2 \<sigma> C2' \<sigma>'; disjoint (locked C1) (locked C2') \<rbrakk> \<Longrightarrow> red (Cpar C1 C2) \<sigma> (Cpar C1 C2') \<sigma>'"
| red_Par3[intro]: "red (Cpar Cskip Cskip) \<sigma> (Cskip) \<sigma>"
| red_Loop[intro]: "red (Cwhile B C) \<sigma> (Cif B (Cseq C (Cwhile B C)) Cskip) \<sigma>"
| red_Local1[intro]: "v = edenot E (fst \<sigma>) \<Longrightarrow> red (Clocal x E C) \<sigma> (Cinlocal x v C) \<sigma>"
| red_Local2[intro]:"\<lbrakk> \<sigma> = (s,h); red C (s(x:=v),h) C' (s',h'); v' = s' x; \<sigma>' = (s'(x := s x), h') \<rbrakk> \<Longrightarrow> red (Cinlocal x v C) \<sigma> (Cinlocal x v' C') \<sigma>'"
| red_Local3[intro]: "red (Cinlocal x v Cskip) \<sigma> Cskip \<sigma>"
| red_Res1[intro]:  "red C \<sigma> C' \<sigma>' \<Longrightarrow> red (Cresource r C) \<sigma> (Cresource r C') \<sigma>'" 
| red_Res2[intro]:  "red (Cresource r Cskip) \<sigma> Cskip \<sigma>" 
| red_Res3[intro]:  "red C \<sigma> C' \<sigma>' \<Longrightarrow> red (Cresources rs C) \<sigma> (Cresources rs C') \<sigma>'" 
| red_Res4[intro]:  "red (Cresources rs Cskip) \<sigma> Cskip \<sigma>" 
| red_With1[intro]: "bdenot B (fst \<sigma>) \<Longrightarrow> red (Cwith r B C) \<sigma> (Cinwith r C) \<sigma>"
| red_With2[elim]:  "\<lbrakk> red C \<sigma> C' \<sigma>'; r \<notin> locked C' \<rbrakk> \<Longrightarrow> red (Cinwith r C) \<sigma> (Cinwith r C') \<sigma>'"
| red_With3[intro]: "red (Cinwith r Cskip) \<sigma> Cskip \<sigma>"
| red_Assign[intro]:"\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s(x := edenot E s), h) \<rbrakk> \<Longrightarrow> red (Cassign x E) \<sigma> Cskip \<sigma>'"
| red_Read[intro]:  "\<lbrakk> \<sigma> = (s,h); h(edenot E s) = Some v; \<sigma>' = (s(x := v), h) \<rbrakk> \<Longrightarrow> red (Cread x E) \<sigma> Cskip \<sigma>'"
| red_Write[intro]: "\<lbrakk> \<sigma> = (s,h); (*(edenot E s) \<in> dom h;*) \<sigma>' = (s, h(edenot E s \<mapsto> edenot E' s)) \<rbrakk>  \<Longrightarrow> red (Cwrite E E') \<sigma> Cskip \<sigma>'"
| red_Alloc[intro]: "\<lbrakk> \<sigma> = (s,h); v \<notin> dom h; \<sigma>' = (s(x := v), h(v \<mapsto> edenot E s)) \<rbrakk>  \<Longrightarrow> red (Calloc x E) \<sigma> Cskip \<sigma>'"
| red_Free[intro]:  "\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s, h(edenot E s := None)) \<rbrakk> \<Longrightarrow> red (Cdispose E) \<sigma> Cskip \<sigma>'"

inductive_cases red_par_cases: "red (Cpar C1 C2) \<sigma> C' \<sigma>'"

subsubsection {* Abort semantics *}

text {* Below, we define the sets of memory accesses and memory writes
  that a command performs in one step. These are used to define what a
  race condition is.  We do not count memory allocation as a memory
  access because the memory cell allocated is fresh. *}

primrec
  accesses :: "cmd \<Rightarrow> stack \<Rightarrow> nat set"
where
    "accesses Cskip            s = {}"
  | "accesses (Cassign x E)    s = {}"
  | "accesses (Cread x E)      s = {edenot E s}"
  | "accesses (Cwrite E E')    s = {edenot E s}"
  | "accesses (Calloc x E)     s = {}"
  | "accesses (Cdispose E)     s = {edenot E s}"
  | "accesses (Cseq C1 C2)     s = accesses C1 s"
  | "accesses (Cpar C1 C2)     s = accesses C1 s \<union> accesses C2 s"
  | "accesses (Cif B C1 C2)    s = {}"
  | "accesses (Cwhile B C)     s = {}"
  | "accesses (Clocal x E C)   s = {}"
  | "accesses (Cinlocal x v C) s = accesses C (s(x:=v))"
  | "accesses (Cresource r C)  s = accesses C s"
  | "accesses (Cresources rs C)  s = accesses C s"
  | "accesses (Cwith r B C)    s = {}"
  | "accesses (Cinwith r C)    s = accesses C s"

primrec
  writes :: "cmd \<Rightarrow> stack \<Rightarrow> nat set "
where
    "writes Cskip            s = {}"
  | "writes (Cassign x E)    s = {}"
  | "writes (Cread x E)      s = {}"
  | "writes (Cwrite E E')    s = {edenot E s}"
  | "writes (Calloc x E)     s = {}"
  | "writes (Cdispose E)     s = {edenot E s}"
  | "writes (Cseq C1 C2)     s = writes C1 s"
  | "writes (Cpar C1 C2)     s = writes C1 s \<union> writes C2 s"
  | "writes (Cif B C1 C2)    s = {}"
  | "writes (Clocal x E C)   s = {}"
  | "writes (Cinlocal x v C) s = writes C (s(x:=v))"
  | "writes (Cwhile B C)     s = {}"
  | "writes (Cresource r C)  s = writes C s"
  | "writes (Cresources rs C)  s = writes C s"
  | "writes (Cwith r B C)    s = {}"
  | "writes (Cinwith r C)    s = writes C s"

text {* A command aborts in a given state whenever it can access
  unallocated memory or has a race condition in its first execution
  step. The soundness statement of the logic asserts that these
  transitions never occur. *}

inductive
  aborts :: "cmd \<Rightarrow> state \<Rightarrow> bool"
where
  aborts_Seq[intro]:   "aborts C1 \<sigma> \<Longrightarrow> aborts (Cseq C1 C2) \<sigma>" 
| aborts_Par1[intro]:  "aborts C1 \<sigma> \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>" 
| aborts_Par2[intro]:  "aborts C2 \<sigma> \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"
| aborts_Race1[intro]:  "\<not> disjoint (accesses C1 (fst \<sigma>)) (writes C2 (fst \<sigma>)) \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"
| aborts_Race2[intro]:  "\<not> disjoint (writes C1 (fst \<sigma>)) (accesses C2 (fst \<sigma>)) \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"
| aborts_Local[intro]:  "aborts C ((fst \<sigma>)(x:=v), snd \<sigma>)  \<Longrightarrow> aborts (Cinlocal x v C) \<sigma>"
| aborts_Res[intro]:   "aborts C \<sigma>  \<Longrightarrow> aborts (Cresource r C) \<sigma>"
| aborts_Res2[intro]:  "aborts C \<sigma>  \<Longrightarrow> aborts (Cresources rs C) \<sigma>"
| aborts_With[intro]:  "aborts C \<sigma>  \<Longrightarrow> aborts (Cinwith r C) \<sigma>"
| aborts_Read[intro]:  "edenot E (fst \<sigma>) \<notin> dom (snd \<sigma>) \<Longrightarrow> aborts (Cread x E) \<sigma>"
| aborts_Write[intro]: "edenot E (fst \<sigma>) \<notin> dom (snd \<sigma>) \<Longrightarrow> aborts (Cwrite E E') \<sigma>"
| aborts_Free[intro]:  "edenot E (fst \<sigma>) \<notin> dom (snd \<sigma>) \<Longrightarrow> aborts (Cdispose E) \<sigma>"

subsubsection {* Well-formed commands *}

text {* Well-formed commands are those that can arise from a user
command by a reduction sequence.  In particular, they can have
partially executed CCRs only at reduction positions and their
partially executed CCRs must satisfy mutual exclusion.  *}

primrec 
  wf_cmd :: "cmd \<Rightarrow> bool"
where
    "wf_cmd Cskip           = True"
  | "wf_cmd (Cassign x E)   = True"
  | "wf_cmd (Cread x E)     = True"
  | "wf_cmd (Cwrite E E')   = True"
  | "wf_cmd (Calloc x E)    = True"
  | "wf_cmd (Cdispose E)    = True"
  | "wf_cmd (Cseq C1 C2)    = (wf_cmd C1 \<and> user_cmd C2)"
  | "wf_cmd (Cpar C1 C2)    = (wf_cmd C1 \<and> wf_cmd C2 \<and> disjoint (locked C1) (locked C2))"
  | "wf_cmd (Cif B C1 C2)   = (user_cmd C1 \<and> user_cmd C2 )"
  | "wf_cmd (Cwhile B C)    = (user_cmd C)"
  | "wf_cmd (Clocal x E C)  = (user_cmd C)"
  | "wf_cmd (Cinlocal x v C)= (wf_cmd C)"
  | "wf_cmd (Cresource r C) = (wf_cmd C)"
  | "wf_cmd (Cresources rs C) = (wf_cmd C)"
  | "wf_cmd (Cwith r B C)   = (user_cmd C)"
  | "wf_cmd (Cinwith r C)   = (wf_cmd C \<and> r \<notin> locked C)"

text {* Now, we establish some basic properties of well-formed commands: *}

text {* (1) User commands are well-formed and have no locks acquired. *}

lemma user_cmdD:
  "user_cmd C \<Longrightarrow> (wf_cmd C \<and> locked C = {})"
by (induct C, auto)

corollary user_cmd_wf[intro]:
  "user_cmd C \<Longrightarrow> wf_cmd C"
by (drule user_cmdD, simp)

corollary user_cmd_llocked[simp]:
  "user_cmd C \<Longrightarrow> llocked C = []"
by (drule user_cmdD, simp add: locked_eq)

text {* (2) Well-formedness is preserved under reduction. *}

lemma red_wf_cmd:
  "\<lbrakk> red C \<sigma> C' \<sigma>' ; wf_cmd C\<rbrakk> \<Longrightarrow> wf_cmd C'"
by (subgoal_tac "wf_cmd C \<longrightarrow> wf_cmd C'", erule_tac[2] red.induct, auto dest: user_cmdD)

text {* (3) Well-formed commands satisfy mutual-exclusion. *}

lemma wf_cmd_distinct_locked: "wf_cmd C \<Longrightarrow> distinct (llocked C)"
  by (induct C, auto simp add: distinct_removeAll locked_eq disjoint_def distinct_list_minus)

subsection {* Free variables, updated variables and substitutions *}

text {* The free variables of expressions, boolean expressions, and
commands are defined as expected: *}

primrec
  fvE :: "exp \<Rightarrow> var set"
where
  "fvE (Evar v) = {v}"
| "fvE (Enum n) = {}"
| "fvE (Eplus e1 e2) = (fvE e1 \<union> fvE e2)"

primrec
  fvB :: "bexp \<Rightarrow> var set"
where
  "fvB (Beq e1 e2)  = (fvE e1 \<union> fvE e2)"
| "fvB (Band b1 b2) = (fvB b1 \<union> fvB b2)"
| "fvB (Bnot b)     = (fvB b)"
| "fvB (Bbool b)    = {}"

primrec
  fvC :: "cmd \<Rightarrow> var set"
where
  "fvC (Cskip)         = {}"
| "fvC (Cassign v E)   = ({v} \<union> fvE E)"
| "fvC (Cread v E)     = ({v} \<union> fvE E)"
| "fvC (Cwrite E1 E2)  = (fvE E1 \<union> fvE E2)"
| "fvC (Calloc v E)    = ({v} \<union> fvE E)"
| "fvC (Cdispose E)    = (fvE E)"
| "fvC (Cseq C1 C2)    = (fvC C1 \<union> fvC C2)"
| "fvC (Cpar C1 C2)    = (fvC C1 \<union> fvC C2)"
| "fvC (Cif B C1 C2)   = (fvB B \<union> fvC C1 \<union> fvC C2)"
| "fvC (Cwhile B C)    = (fvB B \<union> fvC C)"
| "fvC (Clocal x E C)  = (fvE E \<union> (fvC C - {x}))"
| "fvC (Cinlocal x v C)= (fvC C - {x})"
| "fvC (Cresource r C) = (fvC C)"     
| "fvC (Cresources rs C) = (fvC C)"
| "fvC (Cwith r B C)   = (fvB B \<union> fvC C)"
| "fvC (Cinwith r C)   = (fvC C)"

text {* Below, we define the set of syntactically updated variables 
  of a command. This set overapproximates the set of variables that
  are actually updated during the command's execution. *}

primrec
  wrC :: "cmd \<Rightarrow> var set"
where
  "wrC (Cskip)         = {}"
| "wrC (Cassign v E)   = {v}"
| "wrC (Cread v E)     = {v}"
| "wrC (Cwrite E1 E2)  = {}"
| "wrC (Calloc v E)    = {v}"
| "wrC (Cdispose E)    = {}"
| "wrC (Cseq C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC (Cpar C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC (Cif B C1 C2)   = (wrC C1 \<union> wrC C2)"
| "wrC (Cwhile B C)    = (wrC C)"
| "wrC (Clocal x E C)  = (wrC C - {x})"
| "wrC (Cinlocal x v C)= (wrC C - {x})"
| "wrC (Cresource r C) = (wrC C)"
| "wrC (Cresources rs C) = (wrC C)"
| "wrC (Cwith r B C)   = (wrC C)"
| "wrC (Cinwith r C)   = (wrC C)"

text {* We also define the operation of substituting an expression for
a variable in expressions. *}

primrec
  subE :: "var \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp"
where
  "subE x E (Evar y)      = (if x = y then E else Evar y)"
| "subE x E (Enum n)      = Enum n"
| "subE x E (Eplus e1 e2) = Eplus (subE x E e1) (subE x E e2)"

primrec
  subB :: "var \<Rightarrow> exp \<Rightarrow> bexp \<Rightarrow> bexp"
where
  "subB x E (Beq e1 e2)  = Beq (subE x E e1) (subE x E e2)"
| "subB x E (Band b1 b2) = Band (subB x E b1) (subB x E b2)"
| "subB x E (Bnot b)     = Bnot (subB x E b)"
| "subB x E (Bbool b)    = Bbool b"

text {* Basic properties of substitutions: *}

lemma subE_assign:
 "edenot (subE x E e) s = edenot e (s(x := edenot E s))"
by (induct e, simp_all)

lemma subB_assign:
 "bdenot (subB x E b) s = bdenot b (s(x := edenot E s))"
by (induct b, simp_all add: subE_assign fun_upd_def)

subsection {* Variable erasure *}

text {* The following function erases all assignments and reads to
  variables in the set @{term X}. *}

primrec 
  rem_vars :: "var set \<Rightarrow> cmd \<Rightarrow> cmd"
where
    "rem_vars X Cskip          = Cskip"
  | "rem_vars X (Cassign x E)  = (if x \<in> X then Cseq Cskip Cskip else Cassign x E)"
  | "rem_vars X (Cread x E)    = (if x \<in> X then Cseq Cskip Cskip else Cread x E)"
  | "rem_vars X (Cwrite E E')  = Cwrite E E'"
  | "rem_vars X (Calloc x E)   = Calloc x E"
  | "rem_vars X (Cdispose E)   = Cdispose E"
  | "rem_vars X (Cseq C1 C2)   = Cseq (rem_vars X C1) (rem_vars X C2)"
  | "rem_vars X (Cpar C1 C2)   = Cpar (rem_vars X C1) (rem_vars X C2)"
  | "rem_vars X (Cif B C1 C2)  = Cif B (rem_vars X C1) (rem_vars X C2)"
  | "rem_vars X (Cwhile B C)   = Cwhile B (rem_vars X C)"
  | "rem_vars X (Clocal x E C) = Clocal x E (rem_vars (X - {x}) C)"
  | "rem_vars X (Cinlocal x v C) = Cinlocal x v (rem_vars (X - {x}) C)"
  | "rem_vars X (Cresource r C)  = Cresource r (rem_vars X C)"
  | "rem_vars X (Cresources rs C)  = Cresources rs (rem_vars X C)"
  | "rem_vars X (Cwith r B C) = Cwith r B (rem_vars X C)"
  | "rem_vars X (Cinwith r C) = Cinwith r (rem_vars X C)"

text {* Properties of variable erasure: *}

lemma remvars_simps[simp]:
  "locked (rem_vars X C) = locked C"
  "llocked (rem_vars X C) = llocked C"
  "user_cmd (rem_vars X C) = user_cmd C"
  "rem_vars X (rem_vars X C) = rem_vars X C"
by (induct C arbitrary: X, simp_all)+

lemma accesses_remvars: "accesses (rem_vars X C) s \<subseteq> accesses C s"
by (induct C arbitrary: X s, simp_all, fast)

lemma writes_remvars[simp]: 
  "writes (rem_vars X C) = writes C"
by (rule ext, induct C arbitrary: X, simp_all)

lemma skip_simps[simp]: 
  "\<not> red Cskip \<sigma> C' \<sigma>'"
  "\<not> aborts Cskip \<sigma>"
  "(rem_vars X C = Cskip) \<longleftrightarrow> (C = Cskip)"
  "(Cskip = rem_vars X C) \<longleftrightarrow> (C = Cskip)"
by (auto elim: aborts.cases red.cases)
   (induct C, auto split: if_split_asm)+

lemma disjoint_minus: "disjoint (X - Z) Y = disjoint X (Y - Z)"
by (auto simp add: disjoint_def)

lemma aux_red[rule_format]:
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> \<forall>X C1. C = rem_vars X C1 \<longrightarrow> disjoint X (fvC C) \<longrightarrow> \<not> aborts C1 \<sigma> \<longrightarrow>
   (\<exists>C2 s2. red C1 \<sigma> C2 (s2,snd \<sigma>') \<and> rem_vars X C2 = C' \<and> agrees (-X) (fst \<sigma>') s2)"
apply (erule_tac red.induct, simp_all, tactic {* ALLGOALS (clarify_tac @{context}) *})
apply (case_tac C1, simp_all split: if_split_asm, (fastforce simp add: agrees_def)+)
apply (case_tac[1-5] C1a, simp_all split: if_split_asm, (fastforce intro: agrees_refl)+)
apply (case_tac[!] C1, simp_all split: if_split_asm)
apply (tactic {* TRYALL (clarify_tac @{context}) *}, simp_all add: disjoint_minus [THEN sym])
apply (fastforce simp add: agrees_def)+
apply (intro exI conjI, rule_tac v=v in red_Alloc, (fastforce simp add: agrees_def)+)
done

lemma aborts_remvars:
  "aborts (rem_vars X C) \<sigma> \<Longrightarrow> aborts C \<sigma>"
apply (induct C arbitrary: X \<sigma>, erule_tac[!] aborts.cases, simp_all split: if_split_asm)
apply (tactic {* TRYALL (fast_tac @{context}) *})
apply (clarsimp, rule, erule contrapos_nn, simp, erule disjoint_search, rule accesses_remvars)+
done

subsection {* Basic properties of the semantics *}

lemma writes_accesses: "writes C s \<subseteq> accesses C s"
by (induct C arbitrary: s, auto)

text {* Proposition 4.1: Properties of basic properties of @{term red}. *}

lemma red_properties: 
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> 
     fvC C' \<subseteq> fvC C
   \<and> wrC C' \<subseteq> wrC C
   \<and> agrees (- wrC C) (fst \<sigma>') (fst \<sigma>)"
by (erule red.induct, auto simp add: agrees_def)

text {* Proposition 4.2: Semantics does not depend on variables not free in the term *}

lemma exp_agrees: "agrees (fvE E) s s' \<Longrightarrow> edenot E s = edenot E s'"
by (simp add: agrees_def, induct E, auto)

lemma bexp_agrees: "agrees (fvB B) s s' \<Longrightarrow> bdenot B s = bdenot B s'"
by (induct B, auto simp add: exp_agrees)

lemma accesses_agrees: "agrees (fvC C) s s' \<Longrightarrow> accesses C s = accesses C s'"
apply (induct C arbitrary: s s', simp_all add: exp_agrees, clarsimp)
apply (erule mall2_impD, simp add: agrees_def)
done

lemma writes_agrees: "agrees (fvC C) s s' \<Longrightarrow> writes C s = writes C s'"
apply (induct C arbitrary: s s', simp_all add: exp_agrees, clarsimp)
apply (erule mall2_impD, simp add: agrees_def)
done

lemma red_agrees[rule_format]: 
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvC C \<subseteq> X \<longrightarrow> 
   (\<exists>s' h'. red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
apply (erule red.induct, simp_all)
apply (tactic {* TRYALL (fast_tac @{context}) *}, auto)
apply (rule, rule conjI, rule red_If1, simp, subst bexp_agrees, fast+)
apply (rule, rule conjI, rule red_If2, simp, subst bexp_agrees, fast+)
apply (rule, rule conjI, rule, simp, subst exp_agrees, fast+)
apply (drule_tac a="X \<union> {x}" and b="sa(x:=v)" in all2_imp2D, fastforce simp add: agrees_def, fast)
 apply (clarsimp, rule, rule conjI, rule, fast+, fastforce simp add: agrees_def)
apply (rule, rule conjI, rule, simp, subst bexp_agrees, fast+)
apply (rule, rule, rule, fast, simp_all, subst exp_agrees, fast)
 apply (clarsimp simp add: agrees_def)
apply (rule, rule, rule, fast, simp_all, subst exp_agrees, fast, fast)
 apply (clarsimp simp add: agrees_def)
apply (rule, rule, rule, fast, simp_all, subst exp_agrees, fast, clarsimp?)
 apply (rule ext, clarsimp, fast intro: exp_agrees)
apply (rule, rule, rule_tac v=v in red_Alloc, simp_all, fast, auto)
 apply (rule ext, clarsimp, fast intro: exp_agrees)
 apply (clarsimp simp add: agrees_def)
apply (auto)
apply (rule, rule, rule, fast, simp_all)
 apply (rule ext, clarsimp, fast intro: exp_agrees)
done

lemma aborts_agrees[rule_format]:
  "aborts C \<sigma> \<Longrightarrow> \<forall>s'. agrees (fvC C) (fst \<sigma>) s' \<longrightarrow> snd \<sigma> = h' \<longrightarrow> aborts C (s', h')"
by (erule aborts.induct, simp_all, auto simp add: writes_agrees accesses_agrees exp_agrees, 
    auto simp add: agrees_def)

text {* Corollaries of Proposition 4.2, useful for automation. *}

corollary exp_agrees2[simp]:
  "x \<notin> fvE E \<Longrightarrow> edenot E (s(x := v)) = edenot E s"
by (rule exp_agrees, simp add: agrees_def)

corollary bexp_agrees2[simp]:
  "x \<notin> fvB B \<Longrightarrow> bdenot B (s(x := v)) = bdenot B s"
by (rule bexp_agrees, simp add: agrees_def)

end