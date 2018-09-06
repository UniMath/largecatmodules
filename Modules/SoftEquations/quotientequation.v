(**


Proof that the quotient representation satisfies the equations

Definition of a soft signature with some examples (tautological, derivatives)

*)
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.Signature.
Require Import Modules.SoftEquations.ModelCat.
Require Import Modules.Prelims.modules.

Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.
Require Import Modules.SoftEquations.SignatureOverDerivation.

Local Notation  "R →→ S" := (rep_fiber_mor R S) (at level 6).


Section QuotientRep.

  Local Notation MOD Mon := (category_LModule Mon SET).
Local Notation MONAD := (Monad SET).
Local Notation SIG := (signature SET).

  (* Variable (choice : AxiomOfChoice.AxiomOfChoice_surj). *)
Context {Sig : SIG}.
Context (epiSig : ∏ (R S : Monad _)
                    (f : Monad_Mor R S),
                  isEpi (C := [ SET , SET]) ( f : nat_trans _ _) ->
                  isEpi (C := [ SET , SET]) (# Sig f : nat_trans _ _)%ar).
(** implied by the axiom of choice *)
Context (epiSigpw : ∏ (R : Monad _), preserves_Epi (Sig R)).

(** Definition of a soft-over signature

It is a signature Σ such that for any model R, and any family of model morphisms 
(f_j : R --> d_j), the following diagram can be completed in the category
of natural transformations:

<<<
           Σ(f_j)
    Σ(R) ----------->  Σ(d_j)
     |
     |
     |
 Σ(π)|
     |
     V
    Σ(S)

>>>

where π : R -> S is the canonical projection (S is R quotiented by the family (f_j)_j

 *)
  Definition isSoft (OSig : signature_over Sig) :=
    ∏ (R : model Sig) (Repi : preserves_Epi R) (J : UU)(d : J -> (model Sig))(f : ∏ j, R →→ (d j))
      X (x y : (OSig R X : hSet)) (pi := projR_rep Sig epiSig epiSigpw Repi d f),
    (∏ j, (# OSig (f j))%sigo X x  = (# OSig (f j))%sigo X y )
      -> (# OSig pi X x)%sigo = 
        (# OSig pi X y)%sigo  .

  Local Notation REP := (model Sig).
  (** Some examples of soft signatures *)

  Lemma isSoft_tauto : isSoft (tautological_signature_over Sig).
  Proof.
    red; cbn.
    intros.
    apply rel_eq_projR.
    assumption.
  Defined.

  (** Derivative of a soft is soft *)
  Lemma isSoft_derivative {OSig} (soft : isSoft OSig)
    : isSoft (signature_over_deriv (C := SET) BinCoproductsHSET TerminalHSET OSig).
  Proof.
    red; cbn.
    intros R J d f X x y h.
    use soft.
    (* use h. *)
  Defined.

  Local Notation σ := source_equation.
  Local Notation τ := target_equation.

  Definition isEpi_overSig (M : signature_over Sig) :=
        ∏ R S (f : R →→ S),
                   isEpi (C := [SET, SET]) (f : nat_trans _ _) ->
                   isEpi (C := [SET, SET]) (# M f : nat_trans _ _)%sigo.

  Definition soft_equation :=
    ∑ (e : equation), isSoft (τ e) × isEpi_overSig (σ e).

  Coercion eq_from_soft_equation (e : soft_equation) : equation := pr1 e.

  Definition soft_equation_isSoft (e : soft_equation) : isSoft (τ e) :=
    pr1 (pr2 e).

  Definition soft_equation_isEpi (e : soft_equation) : isEpi_overSig (σ e) :=
    pr2 (pr2 e).


  (** Back to the proof *)


  Context {R : REP}.
  (** implied by the axiom of choice *)
  Context (Repi : preserves_Epi R).

  Context {J : UU} (d : J -> REP) 
            (ff : ∏ (j : J), R →→ (d j)).

  Let R' : REP := R'_model Sig epiSig epiSigpw Repi d ff.
  Let projR : rep_fiber_mor R R' := projR_rep  Sig epiSig epiSigpw Repi d ff.

  Local Notation π := projR.
  Local Notation Θ := tautological_LModule.

  Lemma R'_satisfies_eq (e : soft_equation)
        (deq : ∏ j, satisfies_equation e (d j))
    : satisfies_equation e  R'.
  Proof.
    red.
    apply LModule_Mor_equiv; [apply homset_property|].
    apply (soft_equation_isEpi e _ _ projR).
    {  apply isEpi_projR. }
    etrans ; [apply signature_over_Mor_ax  |].
    etrans ; [ | apply pathsinv0; apply signature_over_Mor_ax  ].
    apply nat_trans_eq; [apply homset_property |].
    intro X.
    apply funextfun.
    intro x.
    apply soft_equation_isSoft.
    intro j.
    do 2 rewrite comp_cat_comp.
    use (toforallpaths _ _ _ _ x).
    do 2 rewrite nat_trans_comp_pointwise'.
    use (toforallpaths _ _ _ _ X).
    rewrite <- (signature_over_Mor_ax _ (halfeq1 e)).
    rewrite <- (signature_over_Mor_ax _ (halfeq2 e)).
    apply maponpaths.
    apply (cancel_precomposition  [SET,SET]).
    repeat apply maponpaths.
    apply deq.
  Qed.

  Definition R'_satisfies_all_equations {O : UU} (e : O -> soft_equation)
    (deq : ∏ j, satisfies_all_equations_hp e  (d j))
    : satisfies_all_equations_hp e R'
    := fun o => R'_satisfies_eq (e o) (fun j => deq j o).

  Definition R'_model_equations {O : UU} (e : O -> soft_equation)
    (deq : ∏ j, satisfies_all_equations_hp e (d j))
    : model_equations e 
    := R' ,, R'_satisfies_all_equations e deq. 



End QuotientRep.