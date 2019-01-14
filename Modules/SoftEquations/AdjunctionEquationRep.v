(** * Syntax for soft 2-signatures

Given an epi 1-signature Σ generating a syntax (i.e. whose category of models
has an initial object), the 2-signature consisting of
Σ and any family of soft equations also generates a syntax.

The initial 2-model is the quotient of the initial 1-model R by the
following relation on R(X):
   x ~ y iff their image are equalized by the initial arrow to any 1-model of Σ
             satisfying the equations.

See [push_initiality].

More generally, the forgetful functor from 2-models to 1-models has a left adjoint
[forget_2model_is_right_adjoint]





 *)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import Modules.Prelims.EpiComplements.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.Signatures.ModelCat.


Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.
Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.quotientequation.
Require Import Modules.SoftEquations.SignatureOverDerivation.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.SoftEquations.BindingSig.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
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

  Local Notation REP := (model Sig).

  Local Notation REP_CAT := (rep_fiber_category Sig).

  (** A family of soft equations indexed by O *)
  Context {O : UU} (eq : O -> soft_equation epiSig ) .

  Local Notation REP_EQ := (model_equations eq ).
  Local Notation REP_EQ_PRECAT := (precategory_model_equations eq).

  (* Local Notation R_epi := (modelEpi _). *)

  (** For the quotient, we consider the collections of morphisms
      from [R] to any 1-model of [Sig] satisfying the family of equations *)
  Let J R := ∑ (S : model_equations eq), R →→ S.
  Let d {R} (j : J R) : model_equations eq := pr1 j.
  Let ff {R} (j : J R) : R →→ (d j) := pr2 j.

  (** The quotient model by this collection of arrows *)
  Let R' {R : model Sig}
      (** implied by the axiom of choice *)
      (R_epi : preserves_Epi R) (SigR_epi : preserves_Epi (Sig R))
        : REP_EQ
    := R'_model_equations  epiSig  R_epi SigR_epi d ff eq
                                        (fun j => model_equations_eq (d j)).
  (** Any morphism from R to a 1-model satisfying the equations factorize through
      the canonical projection, followed by [u_rep] *)
  Definition u_rep_arrow {R : model Sig}{S : model_equations eq} R_epi SigR_epi (f : R →→ S)
    := u_rep Sig epiSig R_epi SigR_epi d ff (S ,, f).

  Let projR_rep (R : model Sig)
      (R_epi : preserves_Epi R)(SigR_epi : preserves_Epi (Sig R))
    := projR_rep Sig epiSig R_epi SigR_epi  d ff.

  Lemma u_rep_universal (R : model _) (R_epi: preserves_Epi R) (SigR_epi : preserves_Epi (Sig R))
    : is_universal_arrow_to (forget_2model eq) R (R' R_epi SigR_epi) (projR_rep R R_epi SigR_epi).
  Proof.
    intros S f.
    set (j := tpair (fun (x : model_equations _) => R →→ x) (S : model_equations _)  f).
    eassert (def_u :=(u_rep_def _ _ _  _ (@d R) (@ff R) j)).
    unshelve eapply unique_exists.
    - exact (u_rep_arrow R_epi SigR_epi f ,, tt).
    - exact (! def_u).
    - intro.
      apply homset_property.
    - intros g eq'.
      use eq_in_sub_precategory.
      cbn.
      use (_ : isEpi (C := REP_CAT) (projR_rep R _ _)); [apply isEpi_projR_rep|].
      etrans;[exact eq'|exact def_u].
  Qed.

  (** If all models preserve epis, and their image by the signature
      preserve epis, then we have an adjunctions *)
  Definition forget_2model_is_right_adjoint
             (modepis : ∏ (R : model Sig), preserves_Epi R)
             (SigR_epis : ∏ (R : model Sig) , preserves_Epi (Sig R))
    : is_right_adjoint (forget_2model eq) :=
    right_adjoint_left_from_partial (forget_2model (λ x : O, eq x))
                                    (fun R => R' (modepis R) (SigR_epis R ))
                                    (fun R => projR_rep R (modepis R)(SigR_epis R ))
                                    (fun R => u_rep_universal R (modepis R)(SigR_epis R )).


  (** If the initial model and its image by the signature preserve epis,
     then there is an initial model *)
  Definition push_initiality (R : Initial REP_CAT)
             (R_epi : preserves_Epi (InitialObject R : model _))
             (SigR_epi : preserves_Epi (Sig (InitialObject R : model _)))
    : isInitial REP_EQ_PRECAT (R' R_epi SigR_epi) :=
  initial_universal_to_lift_initial (forget_2model (λ x : O, eq x)) R (u_rep_universal _ R_epi SigR_epi).

End QuotientRep.

(** Mere reformulation which hides the initial object in the main statment (isInitial becomes Initial) *)
Section QuotientRepInit.

  Local Notation MOD Mon := (category_LModule Mon SET).
  Local Notation MONAD := (Monad SET).
  Local Notation SIG := (signature SET).

  Context {Sig : SIG}.
  Context (epiSig : sig_preservesNatEpiMonad Sig).





  Lemma soft_equations_preserve_initiality
        {O : UU}(eq : O -> soft_equation epiSig )
    : ∏ (R : Initial (rep_fiber_category Sig)) ,
(** implied by the axiom of choice *)
      (preserves_Epi (InitialObject  R : model _)) ->
      (preserves_Epi (Sig (InitialObject  R : model _))) ->
      Initial (precategory_model_equations eq).
  Proof.
    intros init R_epi SigR_epi.
    eapply mk_Initial.
    use push_initiality.
    - exact init.
    - assumption.
    - assumption.
  Qed.

  Corollary elementary_equations_preserve_initiality
            (* (epiSigpw : ∏ (R : Monad _), preserves_Epi R -> preserves_Epi (Sig R)) *)
        {O : UU}(eq : O -> elementary_equation (Sig := Sig))
          (eq' := fun o => soft_equation_from_elementary_equation epiSig  (eq o))
    : ∏ (R : Initial (rep_fiber_category Sig)) ,
      (preserves_Epi (InitialObject  R : model _)) ->
      preserves_Epi (Sig (InitialObject R : model _)) ->
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
           (iniEpi :=  algebraic_model_Epi S : preserves_Epi (InitialObject R : model Sig)) 
           (epiSig := algSig_NatEpi S)
           (SR_epi := BindingSigAreEpiEpiSig S)
           (** A family of equations *)
           (eq' := fun o => soft_equation_from_elementary_equation epiSig  (eq o)) :
        (** .. then the category of 2-models has an initial object *)
  Initial (precategory_model_equations eq')
          :=
  elementary_equations_preserve_initiality  epiSig eq R iniEpi (SR_epi _ iniEpi).


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
  - apply preserves_to_HSET_isEpi; assumption.
  - apply preserves_to_HSET_isEpi; assumption.
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
                         epiSig 
                         (eq o))
                 ).
  intros; use soft_equations_preserve_initiality_choice;  assumption.
Qed.