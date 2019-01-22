(** * Lambda calculus modulo beta eta


We start with the algebraic signature Θ × Θ + Θ' specified by the binding
signature [0,0] , [1]. The associated syntax is the lambda-calculus monad.

Two elementary equations are imposed:

1. Beta equivalence

The two half-equations are:

<<<
      abs × id         app
θ' × θ -------> θ × θ ---> θ
>>>

and

<<<
         subst
θ' × θ  ----> θ
>>>



2. Eta equivalence

The two half-equations are:

<<<
    in         abs
θ  -----> θ' -----> θ
>>>

and

<<<
   id
θ ----> θ
>>>

Some results:

- Definition of the beta and eta elementary equations  [beta_equation] and [eta_equation]


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
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.SubstitutionSystems.LamFromBindingSig.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesComplements.
Require Import Modules.Prelims.EpiComplements.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.Signatures.ModelCat.
Require Import Modules.Prelims.LModulesBinProducts.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.Signatures.SignatureBinproducts.
Require Import Modules.Signatures.SignatureCoproduct.
Require Import Modules.Signatures.SignatureDerivation.

Require Import Modules.Signatures.SigWithStrengthToSignature.
Require Import Modules.Signatures.HssSignatureCommutation.
Require Import Modules.Prelims.deriveadj.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.
Require Import Modules.SoftEquations.AdjunctionEquationRep.
Require Import Modules.SoftEquations.quotientequation.
Require Import Modules.Prelims.BinProductComplements.
Require Import Modules.Prelims.CoproductsComplements.

Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import Modules.SoftEquations.SignatureOverBinproducts.
Require Import Modules.SoftEquations.BindingSig.



Local Notation θ := (tautological_signature).
Local Notation τ := (tautological_LModule).
Local Notation BPO := (limits.binproducts.BinProductObject _ ).
Local Notation CPO := (limits.coproducts.CoproductObject _ _ ).
Local Notation ι := (sig_over_from_sig _).


Section BindingSigOp.

Context {C : category} (bpC : BinProducts C) (bcpC : BinCoproducts C) (TC : Terminal C)
        (cpC : ∏ (X : UU) (setX : isaset X), Coproducts X C).

Local Notation hsC := (homset_property C).


Local Notation "∂" := (signature_deriv bcpC TC).
Local Infix "××" :=  (signature_BinProduct (cpC := bpC)  ) (at level 20).




(** The LC algebraic signature is to Θ' + Θ × Θ
The binding signature [LamSig] is defined in UniMath as [1], [0,0] 
 *)
Definition LamOneSig := binding_to_one_sig bpC bcpC cpC TC LamSig.


(** Indexes for the operations in the family LamSig *)
Definition appIdx := true.
Definition absIdx := false.

(** The algebraic signature of app is isomorphic to θ × θ *)
Lemma source_app_iso :
  iso (C := signature_category)
      (arity_to_one_sig bpC bcpC TC (BindingSigMap LamSig appIdx))
      (BPO (θ ×× θ)).
Proof.
  eapply iso_comp; [ use binprod_sigs_har_iso|use BinProduct_pw_iso]; cbn ; apply tauto_sigs_har_iso. 
Defined.

(** The next lemmas show that the arity of abs is isomorphic to θ' *)
Definition arity_abs := arity_to_one_sig bpC bcpC TC (BindingSigMap LamSig absIdx).

Lemma arity_abs_mod_eq_mult R c : 
  (ModulesFromSignatures.lift_lm_mult (Arity_to_Signature hsC bpC bcpC TC (BindingSigMap LamSig absIdx)) R (τ R) :
  nat_trans _ _) c =
  (nat_trans_comp (whiskering.post_whisker (Derivative.deriv_dist TC bcpC R) (θ R))
     (whiskering.pre_whisker (Derivative.maybe_monad TC bcpC) (lm_mult R (θ R)))) c.
Proof.
  cbn.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Lemma arity_abs_eq (R S : Monad C) (f : Monad_Mor R S) (c : C) :
  (signature_deriv_on_morphisms bcpC TC θ R S f) c =
  ((lift_lmodule_mor (Arity_to_Signature hsC bpC bcpC TC (BindingSigMap LamSig absIdx)) R (monad_mor_to_lmodule f) c) · 

   (lift_pb_LModule (Arity_to_Signature hsC bpC bcpC TC (BindingSigMap LamSig absIdx)) f) c).
Proof.
  cbn.
  repeat rewrite id_right.
  reflexivity.
Qed.


Definition source_abs_iso :
  iso (C := signature_category)
      (arity_to_one_sig bpC bcpC TC (BindingSigMap LamSig absIdx))
      (∂ θ).
Proof.
  use signature_S1_S2_iso.
  - exact arity_abs_mod_eq_mult.
  - use arity_abs_eq.
Defined.


    

(**
The first beta half-equation:

<<<
      abs × id         app
θ' × θ -------> θ × θ ---> θ
>>>
*)
Lemma abs_app_halfeq : signature_over_Mor (binding_to_one_sig bpC bcpC cpC TC LamSig) 
                                          (ι (BPO ((∂ θ) ×× θ)))
                                          (ι θ).
Proof.
  eapply (compose (C := signature_over_category _)); revgoals.
  - apply (bindingSig_op_to_sig_mor bpC bcpC cpC TC LamSig appIdx).
  - eapply compose; revgoals.
    + apply sig_sig_over_mor.
      apply (inv_from_iso (C := signature_category)).
      apply source_app_iso.
    + eapply compose;[|apply  signature_over_BinProducts_commutes_sig].
      eapply (compose );[apply inv_from_iso, signature_over_BinProducts_commutes_sig|]. 
      apply BinProductOfArrows.
      * eapply compose; [apply sig_sig_over_mor, (inv_from_iso (C := signature_category)), source_abs_iso|].
        apply bindingSig_op_to_sig_mor.
      * apply identity.
Defined.

(**
The first eta half-equation:
<<<
    in         abs
θ  -----> θ' -----> θ
>>>
*)
Definition in_abs_halfeq : signature_over_Mor (binding_to_one_sig bpC bcpC cpC TC LamSig) 
                                          (ι θ)
                                          (ι θ).
Proof.
  eapply (compose (C := signature_over_category _)); revgoals.
  { apply bindingSig_op_to_sig_mor. }
  apply sig_sig_over_mor.
  eapply (compose (C := signature_category )); revgoals.
  { apply (inv_from_iso (C := signature_category)), source_abs_iso. }
  apply signature_to_deriv.
Defined.

End BindingSigOp.


Local Notation BP := (BinProductsHSET : limits.binproducts.BinProducts SET).
Local Notation BCP := (BinCoproductsHSET : limits.bincoproducts.BinCoproducts SET).
Local Notation T := (TerminalHSET : limits.terminal.Terminal SET).
Local Notation CP := (CoproductsHSET).
Local Notation "∂" := (signature_deriv BCP T).

(** The algebraic lambda calculus signature (in SET) *)
Definition LamOneSigHSET := binding_to_one_sigHSET LamSig.

(** It is an epi-signature *)
Definition LamOneSigHSET_epiSig : sig_preservesNatEpiMonad LamOneSigHSET :=
  algSig_NatEpi LamSig.

(** It has an initial model *)
Definition LamOneSigHSET_Initial :  Initial (rep_fiber_category LamOneSigHSET) :=
  bindingSigHSET_Initial LamSig.


Local Notation  "S1 →→s S2" := (signature_over_Mor LamOneSigHSET
                                                  (sig_over_from_sig _ S1)
                                                  (sig_over_from_sig _ S2)) (at level 6).



Local Infix "××" :=  (signature_BinProduct (cpC := BP)  ) (at level 20).
Local Notation "R ××M S" :=  (LModule_BinProducts _ BP (homset_property SET)
                                                  (R : LModule _ _)
                                                  (S : LModule _ _)
                              ) (at level 20).


(** The source of the beta equation *)
Definition beta_sig_source : signature SET  :=
  BPO ((∂ θ) ×× θ).

Lemma isEpi_beta_sig_source : sig_preservesNatEpiMonad beta_sig_source.
Proof.
  apply sig_preservesNatEpiMonad_reduce_pw_SET.
  apply binProd_epiSigSET;[apply deriv_epiSig|]; red; auto.
Qed.

(** The second half-equation for beta:
<<<
         subst
θ' × θ  ----> θ
>>>
 *)
Definition half_beta_subst : signature_over_Mor LamOneSigHSET
                                           (ι beta_sig_source)
                                           (ι θ).
Proof.
  use tpair.
  - intro R.
    apply (counit_from_are_adjoints (deriv_adj (R := R))).
  - cbn.
    intros R S f.
    apply pathsinv0.
    apply (nat_trans_eq (homset_property SET)).
    use functorial_counit_derivadj.
Defined.

(** the beta equation *)
Definition beta_equation : @elementary_equation LamOneSigHSET :=
  (ι beta_sig_source ,, 0 ,,
     (fun R S (f : rep_fiber_mor R S) => isEpi_beta_sig_source (R : Monad _) (S : Monad _) (f : Monad_Mor _ _)) ,,
      abs_app_halfeq BP BCP T CP ,, half_beta_subst).

(** the eta equation *)
Definition eta_equation  : @elementary_equation LamOneSigHSET :=
   (ι θ ,, 0 ,,
            (λ (M N : model LamOneSigHSET) (f : rep_fiber_mor M N), tautological_epiSig M N f)
            ,, in_abs_halfeq BP BCP T CP ,, (signature_over_Mor_id _ _)  ).

(** gather the beta and eta equations into a family of equations indexed over
the boolean *)
Definition beta_eta_equations (b : bool) : elementary_equation :=
  if true then beta_equation else eta_equation.

(** The lambda calculus modulo beta eta *)
Definition LCBetaEta : Initial
  (precategory_model_equations
                    (fun o =>
                       soft_equation_from_elementary_equation
                         LamOneSigHSET_epiSig 
                         (beta_eta_equations o))
                 ). 
Proof.
  use  elementary_equations_on_alg_preserve_initiality.
Defined.