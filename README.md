# ReCore

## What is this repository for?
This project contains the Isabelle/HOL formalisation and soundness proof for semantics of concurrent reactive system(CRS) with resource ownership and 
CSL reasoning framework that can deal with systems with light interference. It constains a case study, i.e.,
the concurrent stack in Zephyr, which utilize the CSL framework to prove its correctness.

## How do I get set up?
The project is developed by Isabelle/HOL 2023, older version may need some slight adjustments. You can load theorems by dragging them in the Isabelle/HOL GUI

## Layout

### Semantics and Reasoning Framework
* Lang : semantics for imperative language
* VHelper, CSLsound: soundness proof of CSL rules for imperative language  
* Aux_for_CSL: useful proof rules of CSL
* Event_Helper, AuxillaryLemma : auxiliary lemmas for CRS
* Event_Lang, Event_Computation : semantics for CRS
* Event_Safe: CSL reasoning frameworks and soundness proof for CRS
* CSL_Syntax : Syntax definition
### Case Study
* Stack_Spec : specification for stack at code level
* Invariant : definition of resource invariant
* Stack_Aux : auxiliary lemma for stack service reasoning 
* func_cor_pop, func_cor_push, func_cor_scheduler : proof for stack pop/push and scheduler service
* stack_sys : proof for the whole system
