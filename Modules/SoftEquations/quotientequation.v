(**


Proof that the quotient representation satisfies the equations

Definition of a soft signature

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
Require Import Modules.SoftEquations.HalfEquation.

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

(** Definition of a soft-over signature *)
  Definition isSoft (OSig : signature_over Sig) :=
    ∏ (R : rep_ar _ Sig) (J : UU)(d : J -> (rep_ar _ Sig))(f : ∏ j, R →→ (d j))
      X (x y : (OSig R X : hSet)),
    (∏ j, (# OSig (f j))%sigo X x  = (# OSig (f j))%sigo X y )
      -> (# OSig (projR_rep Sig epiSig choice d f) X x)%sigo = 
        (# OSig (projR_rep Sig epiSig choice d f) X y)%sigo  .

  Local Notation REP := (rep_ar SET Sig).

  Context {S1 S2 : signature_over Sig}.
  Context {eq1 eq2 : half_equation S1 S2}.
  Context (epiS1 : ∏ R S (f : R →→ S),
                   isEpi (C := [SET, SET]) (f : nat_trans _ _) ->
                   isEpi (C := [SET, SET]) (# S1 f : nat_trans _ _)%sigo).
  Context (softS2 : isSoft S2).


  Local Notation REP_EQ := (model_equation eq1 eq2).

  Context {R : REP} {J : UU} (d : J -> REP_EQ)
            (ff : ∏ (j : J), R →→ (d j)).

  Let R' : REP := R'_model Sig epiSig choice d ff.
  Let projR : rep_fiber_mor R R' := projR_rep  Sig epiSig choice d ff.

  Local Notation π := projR.
  Local Notation Θ := tautological_LModule.

  Lemma R'_satisfies_eq : satisfies_equation eq1 eq2 R'.
  Proof.
    red.
    apply LModule_Mor_equiv; [apply homset_property|].
    apply (epiS1 _ _ projR).
    {  apply isEpi_projR. }
    etrans ; [apply signature_over_Mor_ax  |].
    etrans ; [ | apply pathsinv0; apply signature_over_Mor_ax  ].
    apply nat_trans_eq; [apply homset_property |].
    intro X.
    apply funextfun.
    intro x.
    apply softS2.
    intro j.
    do 2 rewrite comp_cat_comp.
    use (toforallpaths _ _ _ _ x).
    do 2 rewrite nat_trans_comp_pointwise'.
    use (toforallpaths _ _ _ _ X).
    rewrite <- (signature_over_Mor_ax _ eq1).
    rewrite <- (signature_over_Mor_ax _ eq2).
    apply maponpaths.
    apply (cancel_precomposition  [SET,SET]).
    repeat apply maponpaths.
    apply model_equation_eq.
  Qed.

  Definition R'_model_equation : model_equation eq1 eq2 := R' ,, R'_satisfies_eq.


End QuotientRep.