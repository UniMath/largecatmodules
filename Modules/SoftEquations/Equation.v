
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

  Definition equation :=
    ∑ (S1 S2 : signature_over Sig), half_equation S1 S2 × half_equation S1 S2 .

  Definition source_equation (e : equation) : signature_over Sig :=
    pr1 e.

  Definition target_equation (e : equation) : signature_over Sig :=
    pr1 (pr2 e).

  Definition halfeq1 (e : equation) : half_equation (source_equation e) (target_equation e) :=
    pr1 (pr2 (pr2 e)).

  Definition halfeq2 (e : equation) : half_equation (source_equation e) (target_equation e) :=
    pr2 (pr2 (pr2 e)).

  Local Notation σ := source_equation.
  Local Notation τ := target_equation.

  (* Context {S1 S2 : signature_over Sig}. *)
  (* Local Notation HALFEQ := (half_equation S1 S2). *)

  Definition satisfies_equation (e : equation) (R : REP)  : UU := halfeq1 e R = halfeq2 e R.

  Definition satisfies_equation_isaprop (e : equation) (R : REP)  :
     isaprop (satisfies_equation e R) :=
    homset_property (category_LModule  _ _ ) _ _ _ _.

  Definition satisfies_equation_hp (e : equation) (R : REP) : hProp  :=
    hProppair _ (satisfies_equation_isaprop e R). 

  (** if it satisfies all the equations *)
  Definition satisfies_all_equations_hp {O} (e : O -> equation) R :=
    forall_hProp (fun o => satisfies_equation_hp (e o) R).

  Definition model_equations {O : UU} (e : O -> equation) : UU :=
    ∑ (R : REP), ∏ x, satisfies_equation (e x)  R.

  Coercion model_equations_to_model {O e } (R : model_equations (O := O) e ) : REP := pr1 R.

  Definition model_equations_eq {O} {e : O -> equation} (R : model_equations e) :
    satisfies_all_equations_hp e  R := pr2 R.

  Definition precategory_model_equations {O} (e : O -> equation) : precategory :=
    full_sub_precategory (C := rep_fiber_category Sig)
                         (satisfies_all_equations_hp e).
End Equation.


