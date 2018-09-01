
(* =================================================================================== *)
(** * Half Σ-equations
and their representations

*)
(* =================================================================================== *)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import Modules.Signatures.Signature.
Require Import Modules.SoftEquations.ModelCat.
Require Import Modules.SoftEquations.SignatureOver.

(* Local Infix  ";;" := (rep_ar_mor_mor _ _ _). *)
Local Notation  "R →→ S" := (rep_fiber_mor R S) (at level 6).


Section Equation.
  Context  {C : category} {Sig : signature C}.
  Local Notation REP := (rep_ar C Sig).
  (* Local Notation REP_CAT := (rep_fiber_category Sig). *)

  Definition half_equation (S1 S2 : signature_over Sig) := signature_over_Mor Sig S1 S2.
  Coercion half_equation_to_sig_mor S1 S2 (f : half_equation S1 S2) : signature_over_Mor _ S1 S2  := f.

  Context {S1 S2 : signature_over Sig}.
  Local Notation HALFEQ := (half_equation S1 S2).

  Definition satisfies_equation (eq1 eq2 : HALFEQ) (R : REP)  : UU := eq1 R = eq2 R.
  Definition satisfies_equation_isaprop (eq1 eq2 : HALFEQ) (R : REP)  :
     isaprop (satisfies_equation eq1 eq2 R) :=
    homset_property (category_LModule  _ _ ) _ _ _ _.
  Definition satisfies_equation_hp (eq1 eq2 : HALFEQ) (R : REP) : hProp  :=
    hProppair _ (satisfies_equation_isaprop eq1 eq2 R). 

  (** if it satisfies all the equations *)
  Definition satisfies_all_equations_hp {O} (eq1 eq2 : O -> HALFEQ) R :=
    forall_hProp (fun o => satisfies_equation_hp (eq1 o)(eq2 o) R).

  Definition model_equations {O : UU} (eq1 eq2 : O -> HALFEQ) : UU :=
    ∑ (R : REP), ∏ x, satisfies_equation (eq1 x) (eq2 x) R.

  Coercion model_equations_to_model {O eq1 eq2} (R : model_equations (O := O) eq1 eq2) : REP := pr1 R.

  Definition model_equations_eq {O} {eq1 eq2 : O -> HALFEQ} (R : model_equations eq1 eq2) :
    satisfies_all_equations_hp eq1 eq2 R := pr2 R.

  Definition precategory_model_equations {O} (eq1 eq2 : O -> HALFEQ) : precategory :=
    full_sub_precategory (C := rep_fiber_category Sig)
                         (satisfies_all_equations_hp eq1 eq2).
End Equation.


