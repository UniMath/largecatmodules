(** * Syntax for soft 2-signatures

Given an epi 1-signature Σ generating a syntax (i.e. whose category of models
has an initial object), the 2-signature consisting of
Σ and any family of soft equations also generates a syntax.

The initial 2-model is the quotient of the initial 1-model R by the
following relation on R(X):
   x ~ y iff their image are equalized by the initial arrow to any 1-model of Σ
             satisfying the equations.

See [push_initiality].



 *)


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
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import Modules.Prelims.EpiComplements.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.SoftEquations.ModelCat.
Require Import Modules.Prelims.modules.

Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.
Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.quotientequation.
Require Import Modules.SoftEquations.SignatureOverDerivation.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.SoftEquations.BindingSig.

Require Import UniMath.CategoryTheory.limits.initial.

Local Notation  "R →→ S" := (rep_fiber_mor R S) (at level 6).


Section QuotientRep.

  Local Notation MOD Mon := (category_LModule Mon SET).
  Local Notation MONAD := (Monad SET).
  Local Notation SIG := (signature SET).

  (** The axiom of choice allows to build quotients *)
  Variable (choice : AxiomOfChoice.AxiomOfChoice_surj).
  (** We fix an epi 1-signature [Sig] for the following *)
  Context {Sig : SIG}.
  (** Sig must be an epi-signature, i.e. preserves epimorphicity of natural
      transformations. Note that this is not implied by the axiom of choice
      because the retract may not be a monad morphism.
      This is used to give the quotient monad an action.
   *)
  Context (epiSig : sig_preservesNatEpiMonad Sig).
  (** implied by the axiom of choice *)
  Context (epiSigpw : ∏ (R : Monad _), preserves_Epi R -> preserves_Epi (Sig R)).

  Local Notation REP := (model Sig).

  Local Notation REP_CAT := (rep_fiber_category Sig).

  (** A family of soft equations indexed by O *)
  Context {O : UU} (eq : O -> soft_equation epiSig epiSigpw) .

  Local Notation REP_EQ := (model_equations eq ).
  Local Notation REP_EQ_PRECAT := (precategory_model_equations eq).

  (** [R] will be the candidate for the initial 1-model of [Sig] *)
  Context (R : REP) .
  (** implied by the axiom of choice *)
  Context (R_epi : preserves_Epi R).

  (** For the quotient, we consider the collections of morphisms
      from [R] to any 1-model of [Sig] satisfying the family of equations *)
  Let J := ∑ (S : model_equations eq), R →→ S.
  Let d (j : J) : model_equations eq := pr1 j.
  Let ff (j : J) : R →→ (d j) := pr2 j.

  (** The quotient model by this collection of arrows *)
  Let R' : REP_EQ := R'_model_equations  epiSig epiSigpw R_epi d ff eq
                                        (fun j => model_equations_eq (d j)).
  (** Any morphism from R to a 1-model satisfying the equations factorize through
      the canonical projection, followed by [u_rep] *)
  Let u_rep := u_rep Sig epiSig R_epi (epiSigpw _ R_epi) d ff.

  (** Initiality of [R] in the category of 1-models of [Sig] implies initiality of
      [R'] in the category of 2-models of [Sig] with the given family of equations *)
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
      etrans;[| apply (u_rep_def Sig epiSig R_epi (epiSigpw _ R_epi) d ff j)].
      apply iscontr_uniqueness.
  Qed.


End QuotientRep.

(** Mere reformulation which hides the initial object in the main statment (isInitial becomes Initial) *)
Section QuotientRepInit.

  Local Notation MOD Mon := (category_LModule Mon SET).
  Local Notation MONAD := (Monad SET).
  Local Notation SIG := (signature SET).

  Context {Sig : SIG}.
  Context (epiSig : sig_preservesNatEpiMonad Sig).





  Lemma soft_equations_preserve_initiality
(** implied by the axiom of choice *)
        (epiSigpw : ∏ (R : Monad _), preserves_Epi R -> preserves_Epi (Sig R))
        {O : UU}(eq : O -> soft_equation epiSig epiSigpw)
    : ∏ (R : Initial (rep_fiber_category Sig)) ,
      (preserves_Epi (InitialObject  R : model _)) ->
      Initial (precategory_model_equations eq).
  Proof.
    intros init R_epi.
    eapply mk_Initial.
    use push_initiality; revgoals.
    { exact (pr2 init). }
    assumption.
  Qed.

  Corollary elementary_equations_preserve_initiality
            (epiSigpw : ∏ (R : Monad _), preserves_Epi R -> preserves_Epi (Sig R))
        {O : UU}(eq : O -> elementary_equation (Sig := Sig))
          (eq' := fun o => soft_equation_from_elementary_equation epiSig epiSigpw (eq o))
    : ∏ (R : Initial (rep_fiber_category Sig)) ,
      (preserves_Epi (InitialObject  R : model _)) ->
      Initial (precategory_model_equations eq').
  Proof.
    apply soft_equations_preserve_initiality.
  Qed.

End QuotientRepInit.

(** As a corrolary, the case of an algebraic signature *)
Definition elementary_equations_on_alg_preserve_initiality 
          (S : BindingSig) (Sig := binding_to_one_sigHSET S)

           (O : UU) (eq : O → elementary_equation (Sig := Sig))
           (R := bindingSigHSET_Initial S : Initial (rep_fiber_category Sig))
           (** TODO: show this last step *)
           (iniEpi : preserves_Epi (InitialObject R : model Sig)) 
           (epiSig := algSig_NatEpi S)
           (SR_epi := BindingSigAreEpiEpiSig S)
           (** A family of equations *)
           (eq' := fun o => soft_equation_from_elementary_equation epiSig SR_epi (eq o)) :
        (** .. then the category of 2-models has an initial object *)
  Initial (precategory_model_equations eq')
          :=
  elementary_equations_preserve_initiality  epiSig SR_epi eq R iniEpi.


(** A version using the axiom of choice *)
Lemma soft_equations_preserve_initiality_choice 
  (ax_choice : AxiomOfChoice.AxiomOfChoice_surj) :

         ∏ (** The 1-signature *)
           (Sig : signature SET)
           (** The 1-signature must be an epi-signature *)
           (epiSig : sig_preservesNatEpiMonad Sig)
           (** A family of equations *)
           (O : UU) (eq : O → soft_equation_choice ax_choice Sig epiSig ),
         (** If the category of 1-models has an initial object, .. *)
         Initial (rep_fiber_category Sig) ->
        (** .. then the category of 2-models has an initial object *)
         Initial (precategory_model_equations (λ x : O, eq x)).
  intros; use soft_equations_preserve_initiality; try assumption.
  apply preserves_to_HSET_isEpi; assumption.
Qed.


(** A version using the axiom of choice *)
Lemma elementary_equations_preserve_initiality_choice 
  (ax_choice : AxiomOfChoice.AxiomOfChoice_surj) :

         ∏ (** The 1-signature *)
           (Sig : signature SET)
           (** The 1-signature must be an epi-signature *)
           (epiSig : ∏ (R S : Monad SET) (f : Monad_Mor R S),
                     isEpi (C := [SET, SET]) (f : nat_trans R S)
                     → isEpi (C := [SET, SET])
                             ((# Sig)%ar f : nat_trans (Sig R)  (pb_LModule f (Sig S))))
           (** A family of equations *)
           (O : UU) (eq : O → elementary_equation (Sig := Sig)),
         (** If the category of 1-models has an initial object, .. *)
         Initial (rep_fiber_category Sig) ->
        (** .. then the category of 2-models has an initial object *)
         Initial (precategory_model_equations
                    (fun o =>
                       soft_equation_from_elementary_equation
                         epiSig (fun R _ => preserves_to_HSET_isEpi ax_choice _)
                         (eq o))
                 ).
  intros; use soft_equations_preserve_initiality_choice;  assumption.
Qed.