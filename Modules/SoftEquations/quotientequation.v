(** * Equations satisfied by the quotient 1-model


Let Σ be an epi 1-signature.
Let R be a 1-model of Σ and (α_i : R → S_i)_i be a (possibly large) family of
1-model morphisms.

Then we can construct the quotient 1-model R' (see
quotienrepslice) which is defined as R'(X) = R(X) / ~
and x ~ y iff for all i, α_i(x) = α_i(y)

In this file, we show that if each S_i satisfies the same family of soft
equations, then it is also the case for R'.

- Definition of the soft condition [isSoft]
- Definition of a soft equation [soft_equation]
- Definition of an elementary equation [elementary_equation]
- The quotient model as a 2-model [R'_model_equations]

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

(** Notation for 1-model morphism *)
Local Notation  "R →→ S" := (rep_fiber_mor R S) (at level 6).


Section QuotientRep.

  Local Notation MOD Mon := (category_LModule Mon SET).
Local Notation MONAD := (Monad SET).
Local Notation SIG := (signature SET).

  (** We fix a 1-signature Sig *)
Context {Sig : SIG}.
  (** Sig must be an epi-signature, i.e. preserves epimorphicity of natural
      transformations *)
Context (epiSig : sig_preservesNatEpiMonad Sig).
(** implied by the axiom of choice *)
Context (epiSigpw : ∏ (R : Monad _), preserves_Epi (Sig R)).

(** Definition of a soft Sig-module

It is a soft module Σ such that for any model R, and any family of model morphisms 
(f_j : R --> d_j), the following triangle can be completed in the category
of natural transformations (from Σ(S) to Σ(d_j)):

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
    ∏ (R : model Sig) (R_epi : preserves_Epi R) (J : UU)(d : J -> (model Sig))(f : ∏ j, R →→ (d j))
      X (x y : (OSig R X : hSet)) (pi := projR_rep Sig epiSig epiSigpw R_epi d f),
    (∏ j, (# OSig (f j))%sigo X x  = (# OSig (f j))%sigo X y )
      -> (# OSig pi X x)%sigo = 
        (# OSig pi X y)%sigo  .

  Local Notation REP := (model Sig).

  (** Some examples of soft Sig-modules: the tautological soft module assigning
      a 1-model to itsefl.
    *)
  Lemma isSoft_tauto : isSoft (tautological_signature_over Sig).
  Proof.
    red; cbn.
    intros.
    apply rel_eq_projR.
    assumption.
  Defined.

  Local Notation BC := BinCoproductsHSET.
  Local Notation T := TerminalHSET.

  (** Derivative of a soft Sig-module is soft *)
  Lemma isSoft_derivative {OSig} (soft : isSoft OSig)
    : isSoft (signature_over_deriv (C := SET) BC T OSig).
  Proof.
    red; cbn.
    intros R J d f X x y h.
    use soft.
    (* use h. *)
  Defined.


  (** Any finite derivative of the tautological soft Sig-module is soft *)
  Corollary isSoft_finite_deriv_tauto n :
    isSoft (signature_over_deriv_n Sig BC T (tautological_signature_over Sig) n).
  Proof.
    induction n.
    - apply isSoft_tauto.
    - apply isSoft_derivative.
      apply IHn.
  Qed.

  Local Notation σ := source_equation.
  Local Notation τ := target_equation.

  (** An epi Sig-module is a module M which preserves the epimorphicity
      in the category of natural transformations *)
  Definition isEpi_overSig (M : signature_over Sig) :=
        ∏ R S (f : R →→ S),
                   isEpi (C := [SET, SET]) (f : nat_trans _ _) ->
                   isEpi (C := [SET, SET]) (# M f : nat_trans _ _)%sigo.

  (** An equation is soft if the source is an epi Sig-module
      and the target is soft *)
  Definition isSoft_eq (e : equation) :=
    isSoft (τ e) × isEpi_overSig (σ e).

  (** A soft equation is an equation where the source is an epi Sig-module
      and the target is soft *)
  Definition soft_equation :=
    ∑ (e : equation), isSoft_eq e.



  Coercion eq_from_soft_equation (e : soft_equation) : equation := pr1 e.

  Definition soft_equation_isSoft (e : soft_equation) : isSoft (τ e) :=
    pr1 (pr2 e).

  Definition soft_equation_isEpi (e : soft_equation) : isEpi_overSig (σ e) :=
    pr2 (pr2 e).


  (** Back to the proof *)


  (** Consider a 1-model R with a family of 1-model morphisms (ff_j :  R -> d_j)_j *)
  Context {R : REP}.
  (** implied by the axiom of choice *)
  Context (R_epi : preserves_Epi R).

  Context {J : UU} (d : J -> REP) 
            (ff : ∏ (j : J), R →→ (d j)).

  (** R' is the 1-model R quotiented by the following relation on R(X):
         x ~ y iff ff_j(x) = ff_j(y) for all j *)
  Let R' : REP := R'_model Sig epiSig epiSigpw R_epi d ff.
  (** The canonical projection R -> R' as a 1-model morphism *)
  Let projR : rep_fiber_mor R R' := projR_rep  Sig epiSig epiSigpw R_epi d ff.

  Local Notation π := projR.
  Local Notation Θ := tautological_LModule.

  (** If all the d_j satisifes the same soft equation, then it is the case
      of the quotient R' *)
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

  (** Thus, if all the d_j satisfy the same family of soft equations, then it is
       also the case of R' *)
  Definition R'_satisfies_all_equations {O : UU} (e : O -> soft_equation)
    (deq : ∏ j, satisfies_all_equations_hp e  (d j))
    : satisfies_all_equations_hp e R'
    := fun o => R'_satisfies_eq (e o) (fun j => deq j o).

  (** R' can be thus given the structure of a 2-model *)
  Definition R'_model_equations {O : UU} (e : O -> soft_equation)
    (deq : ∏ j, satisfies_all_equations_hp e (d j))
    : model_equations e 
    := R' ,, R'_satisfies_all_equations e deq. 


  (** ** Definition of elementary equations
   *)
  Local Notation θ := (tautological_signature_over Sig).
  Local Notation "M ^( n )" := (signature_over_deriv_n Sig BC T M n) (at level 6).

  (** An elementary equation

The source is an epi-Sig-module and the target a finite derivative of the tautological signature 

   *)
  Definition elementary_equation : UU :=
    ∑ (S1 : signature_over Sig)(n : nat), isEpi_overSig S1 × half_equation S1 (θ ^(n)) × half_equation S1 (θ ^(n)). 

  (** The Sig-module source of a soft equation *)
  Definition source_elem_eq (e : elementary_equation) : signature_over Sig :=
    pr1 e.
  (** The Sig-module target of a soft equation *)
  Definition target_elem_eq (e : elementary_equation) : nat :=
    pr1 (pr2 e).

  Local Notation σ' := source_elem_eq.
  Local Notation τ' := target_elem_eq.

  Definition source_elem_epiSig (e : elementary_equation) : isEpi_overSig (σ' e) := 
    pr1 (pr2 (pr2 e)).

  Definition half_elem_eqs (e : elementary_equation) :
    half_equation (σ' e) (θ ^(τ' e)) ×
    half_equation (σ' e) (θ ^(τ' e)) 
    :=
    pr2 (pr2 (pr2 e)).


  (** Helper to build a soft equation *)
  Definition mk_soft_equation {A B : signature_over Sig} (heq  : half_equation A B × half_equation A B)
             (hA : isEpi_overSig A) (hB : isSoft B) : soft_equation :=
    tpair isSoft_eq (A ,, B ,, heq) (hB ,, hA).

  Coercion soft_equation_from_elementary_equation (e : elementary_equation) : soft_equation :=
    mk_soft_equation (half_elem_eqs e)  (source_elem_epiSig e)
                     (isSoft_finite_deriv_tauto (target_elem_eq e)).


End QuotientRep.

Definition soft_equation_choice (choice : AxiomOfChoice.AxiomOfChoice_surj) (S : signature SET) 
            (** S preserves epimorphisms of monads *)
        (isEpi_sig : ∏ (R R' : Monad SET)
                      (f : Monad_Mor R R'),
                      (isEpi (C:= [SET,SET]) (f : nat_trans _ _) ->
                        isEpi (C:= [SET,SET]) ((#S f)%ar : nat_trans _ _))) : UU :=
    soft_equation isEpi_sig (λ R : Monad SET, preserves_to_HSET_isEpi choice (S R)).

Identity Coercion forget_choice : soft_equation_choice >-> soft_equation.
