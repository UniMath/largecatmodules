
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
Require Import UniMath.CategoryTheory.Categories.
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

  Definition model_equation (eq1 eq2 : HALFEQ) : UU := ∑ (R : REP), satisfies_equation eq1 eq2 R.

  Coercion model_equation_to_model {eq1 eq2} (R : model_equation eq1 eq2) : REP := pr1 R.

  Definition model_equation_eq {eq1 eq2 : HALFEQ} (R : model_equation eq1 eq2) : eq1 R = eq2 R := pr2 R.
End Equation.


