# ReCore

## What is this repository for?
This project contains the Isabelle/HOL formalisation and soundness proof for semantics of concurrent reactive system(CRS) with resource ownership and 
two reasoning frameworks CSL and RGSep that can deal with systems with light and heavy interference respectively. It constains a case study, i.e.,
the concurrent stack in Zephyr, which utilize the CSL framework to prove its correctness.

## How do I get set up?
The project is developed by Isabelle/HOL 2022, older version may need some slight adjustments. You can load theorems by dragging them in the Isabelle/HOL GUI

## Layout

### Semantics and Reasoning Framework
* Lang : semantics for imperative language
* VHelper, CSLsound, RGSepSound : soundness proof of CSL and RGSep rules for imperative language  
* Aux_for_CSL, Aux_for_RGSep : useful proof rules of CSL and RGSep
* Event_Helper, AuxillaryLemma : auxiliary lemmas for CRS
* Event_Lang, Event_Computation : semantics for CRS
* Event_Safe, Event_RGsafe : CSL and RGSep reasoning frameworks and soundness proof for CRS
* CSL_Syntax : Syntax definition
### Case Study
* Stack_Spec : specification for stack at code level
* Invariant : definition of resource invariant
* Stack_Aux : auxiliary lemma for stack service reasoning 
* func_cor_pop, func_cor_push, func_cor_scheduler : proof for stack pop/push and scheduler service
* stack_sys : proof for the whole system
