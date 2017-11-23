
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.aritiesalt.
Open Scope cat.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.PointedFunctors.
Set Automatic Introduction.

(** strangely enough, I didn't find the following lemma :*)
Lemma monad_mor_to_lmodule_law {C : precategory} {R S : Monad C}
           (f : Monad_Mor R S) :
  LModule_Mor_laws R (T := tautological_LModule R)
                   (T' := pb_LModule f (tautological_LModule S)) f.
Proof.
  intro x.
  cbn.
  rewrite assoc.
  apply pathsinv0.
  apply Monad_Mor_μ.
Qed.

Definition monad_mor_to_lmodule {C : precategory} {R S : Monad C}
  (f : Monad_Mor R S) : LModule_Mor R (tautological_LModule R) (pb_LModule f (tautological_LModule S))
  := (f : nat_trans _ _) ,, monad_mor_to_lmodule_law f.

Section LiftLModuleMor.

Context {C D : category} (H : Signature C (homset_property C) D (homset_property D))
          (T : Monad C).



Local Notation θ_nat_2_pw := (θ_nat_2_pointwise _ _ _ _ H (theta H)).
Local Notation θ_nat_1_pw := (θ_nat_1_pointwise _ _ _ _ H (theta H) ).
Local Notation "'p' T" := (ptd_from_mon (homset_property C) T) (at level 3).

(* Has this been already defined somewhere ?? *)
Definition ptd_mor_from_Monad_mor {M N : Monad C} (f : Monad_Mor M N)
    : ptd_mor _ (p M) (p N).
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
  cbn.
  rewrite functor_id, id_right.
  apply LModule_Mor_σ.
Qed.

Definition lift_lmodule_mor {M N : LModule T C} (f : LModule_Mor T M N) :
  LModule_Mor T (liftlmodule M) (liftlmodule N)
 := # H (f : M ⟹ N),, lift_lmodule_mor_law f.

End LiftLModuleMor.

Section HssToArity.

Context {C : category}.

Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).

Local Notation hsC := (homset_property C).


Context (H : Signature C hsC C hsC).
Local Notation liftlmodule := (ModulesFromSignatures.lift_lmodule H ).

Local Notation θ_nat_2_pw := (θ_nat_2_pointwise _ _ _ _ H (theta H)).
Local Notation θ_nat_1_pw := (θ_nat_1_pointwise _ _ _ _ H (theta H) ).
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
Lemma lift_pb_LModule_laws {R S : Monad C} (f : Monad_Mor R S) :
  LModule_Mor_laws R
                   (T := (liftlmodule R (pb_LModule f (tautological_LModule S))))
                   (T' := (pb_LModule f (liftlmodule S (tautological_LModule S))))
                     (nat_trans_id _).
Proof.
  intro X.
  cbn.
  rewrite id_left,id_right.
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
    cbn.
    now rewrite id_left.
Qed.

Definition lift_pb_LModule 
  {R S : Monad C}
  (f : Monad_Mor R S) :
  LModule_Mor R (liftlmodule R (pb_LModule f (tautological_LModule S)))
    (pb_LModule f (liftlmodule S (tautological_LModule S)))
  := _ ,, lift_pb_LModule_laws f.

Definition hss_to_ar_data : @arity_data C.
Proof.
  use tpair.
  + intro R.
    eapply (ModulesFromSignatures.lift_lmodule H).
    apply tautological_LModule.
  + cbn.
    intros R S f.
    cbn.
    (* We need a morphism H R ---> H (f* S)
        defined as H R ---> H (f* S) ---> f* (H S)
     *)
    eapply (compose (C := category_LModule R C)).
           (* LModule_composition. *)
    * unshelve eapply lift_lmodule_mor.
      -- apply (pb_LModule f).
         apply (tautological_LModule S).
      -- apply monad_mor_to_lmodule.
    * apply lift_pb_LModule.
Defined.

Lemma hss_to_ar_is_arity : is_arity hss_to_ar_data.
Proof.
  split.
  - intros R X.
    cbn.
    rewrite id_right.
    assert (h := functor_id H (R : functor _ _)).
    eapply nat_trans_eq_pointwise in h.
    etrans; [|apply h].
    apply functor_cancel_pw.
    now apply (nat_trans_eq (homset_property _)).
  - intros R S T f g.
    apply LModule_Mor_equiv;[apply homset_property|].
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn.
    rewrite !id_right.
    apply pathsinv0.
    apply functor_comp_pw.
Qed.

Definition hss_to_ar : arity C := hss_to_ar_data ,, hss_to_ar_is_arity.

End HssToArity.