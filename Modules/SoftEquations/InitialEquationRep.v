(** Proof that the signatures with soft equations is representable *)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
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
Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.quotientequation.

Require Import UniMath.CategoryTheory.limits.initial.

Local Notation  "R →→ S" := (rep_fiber_mor R S) (at level 6).


Section QuotientRep.

  Local Notation MOD Mon := (category_LModule Mon SET).
  Local Notation MONAD := (Monad SET).
  Local Notation SIG := (signature SET).

  Variable (choice : AxiomOfChoice.AxiomOfChoice_surj).
  Context {Sig : SIG}.
  Context (epiSig : ∏ (R S : Monad _)
                      (f : Monad_Mor R S),
                    isEpi (C := [ SET , SET]) ( f : nat_trans _ _) ->
                    isEpi (C := [ SET , SET]) (# Sig f : nat_trans _ _)%ar).
(** implied by the axiom of choice *)
Context (epiSigpw : ∏ (R : Monad _), preserves_Epi (Sig R)).

  Local Notation REP := (model Sig).

  Local Notation REP_CAT := (rep_fiber_category Sig).

  Context {O : UU} (eq : O -> soft_equation epiSig epiSigpw) .

  Local Notation REP_EQ := (model_equations eq ).
  Local Notation REP_EQ_PRECAT := (precategory_model_equations eq).

  Context (R : REP) .
  (** implied by the axiom of choice *)
  Context (R_epi : preserves_Epi R).

  Let J := ∑ (S : model_equations eq), R →→ S.
  Let d (j : J) : model_equations eq := pr1 j.
  Let ff (j : J) : R →→ (d j) := pr2 j.

  Let R' : REP_EQ := R'_model_equations  epiSig epiSigpw R_epi d ff eq
                                        (fun j => model_equations_eq (d j)).
  Let u_rep := u_rep Sig epiSig epiSigpw R_epi d ff.

  Lemma push_initiality : isInitial REP_CAT R -> isInitial REP_EQ_PRECAT R'.
    intro h.
    (* inspired by push_initiality of EpiSigRepresentability *)
    intro S.
    set (j := ((S ,, iscontrpr1 (h ((S : REP_EQ) : REP))) : J)).
    use iscontrpair.
    -
      (* ?? QUestion pour Benedkt : 
              pourquoi ce n'est pas convertible à change (R' →→ (S : REP_EQ)) ?? *)
      cbn.
      use tpair.
      + use (u_rep j).
      + exact tt.
    - intros [f []].
      apply (maponpaths (fun x => x ,, tt)).
      apply isEpi_projR_rep.
      etrans;[| apply (u_rep_def Sig epiSig epiSigpw R_epi d ff j)].
      apply iscontr_uniqueness.
  Qed.


End QuotientRep.

