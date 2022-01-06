(**
HSS Signature to Signature functor

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
(* Require Import UniMath.CategoryTheory.Chains.All. *)
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesComplements.
Require Import Modules.Signatures.Signature.
Open Scope cat.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.PointedFunctors.
Set Automatic Introduction.


Section LiftLModuleMor.

Context {C D : category} (H : Signature C D C)
          (T : Monad C).



Local Notation θ_nat_2_pw := (θ_nat_2_pointwise _ _ _ H (theta H)).
Local Notation θ_nat_1_pw := (θ_nat_1_pointwise _ _ _ H (theta H) ).
Local Notation "'p' T" := (ptd_from_mon  T) (at level 3).

(* Has this been already defined somewhere ?? *)
Definition ptd_mor_from_Monad_mor {M N : Monad C} (f : Monad_Mor M N)
  : ptd_mor _ (p M) (p N).
Proof.
  use tpair.
  - apply f.
  - intro c.
    apply (Monad_Mor_η f).
Defined.

Local Notation liftlmodule := (ModulesFromSignatures.lift_lmodule H T).
(* We should move this part (that turns a signature into a functor)
 into UniMath/ModulesFromSignatures *)
(**
The following diagram must be proved commutative:
<<<

                H f (T X)                θ
  (H M) (T X) ---------> (H N) (T X) --------> H (N T) X
       |                                           |
       |                                           |
       |                                           |
 θ     |                                           |  H (σ_N) X
       |                                           |
       |                                           |
       V                                           V
   H (M T) X ------------> (H M) X ----------->  (H N) X
                H (σ_M) X            (H f) X

>>>

By naturality of θ, the top arrow rewrites
<<<
                θ                      H (f T) X
  (H M) (T X) ---------> (H (M T)) X ----------> H (N T) X
>>>
And the remaining diagram comes from the fact that f is a module morphism

*)

Lemma lift_lmodule_mor_law {M N : LModule T C} (f : LModule_Mor T M N) :
  LModule_Mor_laws T (T := liftlmodule M) (T' := liftlmodule N) (# H (f : _ ⟹ _)).
Proof.
  intro X.
  etrans; [apply assoc|].
  etrans.
  {
    apply cancel_postcomposition.
    apply (θ_nat_1_pw _ _ (f : nat_trans _ _) (p T) X).
  }
  etrans;[|apply assoc].
  etrans;[eapply pathsinv0; apply assoc |].
  apply cancel_precomposition.
  etrans; [apply functor_comp_pw|].
  etrans; [| eapply pathsinv0; apply functor_comp_pw].
  apply functor_cancel_pw.
  apply (nat_trans_eq (homset_property _)).
  intro x.
  cbn. unfold HorizontalComposition.horcomp_data; cbn.
  rewrite functor_id, id_right.
  apply LModule_Mor_σ.
Qed.

Definition lift_lmodule_mor {M N : LModule T C} (f : LModule_Mor T M N) :
  LModule_Mor T (liftlmodule M) (liftlmodule N)
  := # H (f : M ⟹ N),, lift_lmodule_mor_law f.

End LiftLModuleMor.

Section SigWithStrengthToSignature.

Context {C : category}.

Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).

Local Notation hsC := (homset_property C).


Context (H : Signature C C C).
Local Notation liftlmodule := (ModulesFromSignatures.lift_lmodule H ).

Local Notation θ_nat_2_pw := (θ_nat_2_pointwise _ _ _ H (theta H)).
Local Notation θ_nat_1_pw := (θ_nat_1_pointwise _ _ _ H (theta H) ).
(** commutation pullback module/liftlmodule *)
(**
It is almost the same diagram than for liftlmodule_mor, but now we exploit
the naturality in the second component
<<<

                H S (T X)                θ
  (H S) (R X) ---------> (H S) (S X) --------> H (S S) X
       |                                           |
       |                                           |
       |                                           |
 θ     |                                           |  H (μ_S) X
       |                                           |
       |                                           |
       V                                           V
   H (S R) X ------------> (H M) X ----------->  (H S) X
                H (σ_M) X            (H f) X

>>>

By naturality of θ, the top arrow rewrites
<<<
                θ                      H (f T) X
  (H M) (T X) ---------> (H (M T)) X ----------> H (N T) X
>>>
*)
Lemma lift_pb_LModule_eq_mult {R S : Monad C} ( f : Monad_Mor R S) c :
  (ModulesFromSignatures.lift_lm_mult H R (pb_LModule f (tautological_LModule S)) : nat_trans _ _) c =
  (pb_LModule_σ f (liftlmodule S (tautological_LModule S))) c.
Proof.
  apply pathsinv0.
    etrans;[ apply assoc|].
  etrans.
  {
    apply cancel_postcomposition.
    apply (θ_nat_2_pw (S : functor _ _) _ _ (ptd_mor_from_Monad_mor f)).
  }
  apply pathsinv0.
  cbn.
  etrans;[|apply assoc].
  apply cancel_precomposition.
  apply pathsinv0.
  etrans;[apply functor_comp_pw|].
  apply functor_cancel_pw.
  apply nat_trans_eq.
  - apply homset_property.
  - intro x.
    cbn. unfold HorizontalComposition.horcomp_data; cbn.
    rewrite id_left.
    apply idpath.
Qed.

Lemma lift_pb_LModule_iso 
  {R S : Monad C}
  (f : Monad_Mor R S) :
    iso (C := precategory_LModule _ _)
    (liftlmodule R (pb_LModule f (tautological_LModule S)))
    (pb_LModule f (liftlmodule S (tautological_LModule S))).
Proof.
  apply LModule_same_func_iso.
  apply lift_pb_LModule_eq_mult.
Defined.

Definition lift_pb_LModule 
  {R S : Monad C}
  (f : Monad_Mor R S) :
  LModule_Mor R (liftlmodule R (pb_LModule f (tautological_LModule S)))
              (pb_LModule f (liftlmodule S (tautological_LModule S))) :=
  morphism_from_iso (lift_pb_LModule_iso f).


Definition sigWithStrength_to_sig_data : @signature_data C.
Proof.
  use tpair.
  + intro R.
    apply (ModulesFromSignatures.lift_lmodule H _ (tautological_LModule _ )).
  + cbn.
    intros R S f.
    cbn.
    (* We need a morphism H R ---> H (f* S)
        defined as H R ---> H (f* S) ---> f* (H S)
     *)
    eapply (compose (C := category_LModule R C)).
           (* LModule_composition. *)
    * use lift_lmodule_mor.
      -- apply (pb_LModule f).
         apply (tautological_LModule S).
      -- apply monad_mor_to_lmodule.
    * apply lift_pb_LModule.
Defined.

Lemma sigWithStrength_to_sig_is_signature : is_signature sigWithStrength_to_sig_data.
Proof.
  split.
  - intros R X.
    cbn.
    rewrite id_right.
    assert (h := functor_id H (R : functor _ _)).
    eapply nat_trans_eq_pointwise in h.
    etrans; [|apply h].
    apply functor_cancel_pw.
    apply (nat_trans_eq (homset_property _)).
    intro; apply idpath.
  - intros R S T f g.
    apply LModule_Mor_equiv;[apply homset_property|].
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn.
    rewrite !id_right.
    apply pathsinv0.
    apply functor_comp_pw.
Qed.

Definition sigWithStrength_to_sig : signature C := sigWithStrength_to_sig_data ,, sigWithStrength_to_sig_is_signature.

End SigWithStrengthToSignature.

Section SigWithStrengthToSignatureMor.
  Context {C  : category}.

  Let Sig := Signature_category C C C.
  Local Notation F := sigWithStrength_to_sig.

  Context {A B : Sig}.
  Variable (f : Sig ⟦ A, B⟧).

  (* Let θ_nat_2_pw (H : Signature C (homset_property C) C (homset_property C)) := *)
  (*   (θ_nat_2_pointwise _ _ _ _ H (theta H)). *)
  (* Let θ_nat_1_pw (H : Signature C (homset_property C) C (homset_property C)) := *)
  (*   (θ_nat_1_pointwise _ _ _ _ H (theta H)). *)
  Local Notation "'p' T" := (ptd_from_mon T) (at level 3).

  Lemma sigWithStrength_to_sig_mod_mor_laws (R : Monad C) :
  @LModule_Mor_laws C R C (F A R) (F B R)
    ( (# (SignatureForgetfulFunctor C C C) f : nat_trans _ _) ( R : functor _ _ )).
  Proof.
    (*
<<<
              f_R R
    A(R) R -----------> B(R) R
       |                   |
       |                   |
 θ A   |                   | θ B
       |                   |
       |                   |
       V                   V
    A(R R)              B (R R)
       |                   |
       |                   |
 A(μ)  |                   | B(μ)
       |                   |
       |                   |
       V                   V
      A(R) ----------->  B(R)
             f_R
>>>
And as f is a signature morphism, we have


<<<
              f_X R
    A(X) R ---------->  B(X) R
       |                   |
       |                   |
 θ A   |                   | θ B
       |                   |
       |                   |
       V                   V
    A(X R) ----------->  B(X R)
             f_XR
>>>
*)
    intro c.
    assert (hf := nat_trans_eq_pointwise (pr2 f (R : functor _ _) (p R)) c).
    cbn in hf. unfold HorizontalComposition.horcomp_data in hf; cbn in hf.
    rewrite functor_id,id_right in hf.
    cbn.
    etrans.
    {
      etrans;[apply assoc|].
      apply cancel_postcomposition.
      exact ( !hf).
    }
    do 2 rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    assert (hf' := (nat_trans_ax (pr1 f) _ _ (μ R) )).
    eapply nat_trans_eq_pointwise in hf'.
    apply hf'.
  Qed.

  Definition sigWithStrength_to_sig_mod_mor (R : Monad C) :
    LModule_Mor  R  (F A R) (F B R) :=
    _ ,, sigWithStrength_to_sig_mod_mor_laws R.

  Lemma sigWithStrength_to_sig_is_signature_Mor : is_signature_Mor (F A) (F B) sigWithStrength_to_sig_mod_mor.
  Proof.
    intros R S g.
    change ((#(A : Signature _ _ _ ) (g : nat_trans _ _))· identity _ · (pr11 f (S : functor _ _)) =
            (pr11 f (R : functor _ _)) · (# (B : Signature _ _ _ ) (g : nat_trans _ _) · identity _)).
    do 2 rewrite id_right.
    apply nat_trans_ax.
  Qed.
  Definition sigWithStrength_to_sig_mor   : signature_Mor (F A) (F B) :=
    _ ,, sigWithStrength_to_sig_is_signature_Mor.
End SigWithStrengthToSignatureMor.

Section SigWithStrengthToSignatureFunctor.
  Context {C  : category}.

  Let Sig := Signature_category C C C.
  Local Notation F := sigWithStrength_to_sig.

  Definition sigWithStrength_to_sig_functor_data : functor_data Sig (signature_category (C := C)) :=
    make_functor_data (C' := signature_category) _ (@sigWithStrength_to_sig_mor C).

  Lemma sigWithStrength_to_sig_is_functor : is_functor sigWithStrength_to_sig_functor_data.
  Proof.
    split.
    - intro S.
      apply signature_Mor_eq.
      intro X.
      apply LModule_Mor_equiv;[apply homset_property|].
      apply idpath.
    - intros R S T f g.
      apply signature_Mor_eq.
      intro X.
      apply LModule_Mor_equiv;[apply homset_property|].
      apply idpath.
  Defined.

  Definition sigWithStrength_to_sig_functor : functor Sig (signature_category (C := C)) :=
    make_functor _ sigWithStrength_to_sig_is_functor.
End SigWithStrengthToSignatureFunctor.
