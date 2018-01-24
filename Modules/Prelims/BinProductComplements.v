(*
- commutativity
- iso pointwise -> iso
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.EpiFacts.

Open Scope cat.

Section BinProdComplements.
  Context {C : precategory}.
  Definition BinProduct_commutative {a b : C} (bpab : BinProduct _ a b) (bpba : BinProduct _ b a)
    : C ⟦BinProductObject _ bpab, BinProductObject _ bpba ⟧
   := BinProductArrow C bpba (BinProductPr2 C bpab) (BinProductPr1 C bpab).

  Lemma BinProduct_commutative_id_commute {a b : C} (bpab : BinProduct _ a b) (bpba : BinProduct _ b a):
    BinProduct_commutative bpab bpba · BinProduct_commutative bpba bpab =
  identity (BinProductObject C bpab).
  Proof.
    etrans; [apply precompWithBinProductArrow|].
    apply pathsinv0.
    apply BinProduct_endo_is_identity.
    - etrans;[apply BinProductPr1Commutes|].
      apply BinProductPr2Commutes.
    - etrans;[apply BinProductPr2Commutes|].
      apply BinProductPr1Commutes.
  Qed.
  Definition BinProduct_commutative_iso {a b : C} (bpab : BinProduct _ a b)
             (bpba : BinProduct _ b a)
    : iso (BinProductObject _ bpab) (BinProductObject _ bpba ).
    eapply isopair.
    use is_iso_from_is_z_iso.
    eapply mk_is_z_isomorphism.
    split; apply BinProduct_commutative_id_commute.
  Defined.
  Local Notation BPO := (BinProductObject _).

  Definition BinProduct_pw_iso_mor {a b a' b' : C} (bp_ab : BinProduct _ a b)
             (bp_ab' : BinProduct _ a' b') (isoa : iso a a') (isob : iso b b') :
    C ⟦ BPO bp_ab, BPO bp_ab'⟧ :=
    BinProductOfArrows C bp_ab' bp_ab isoa isob. 

  Lemma BinProduct_pw_eq_id  {a b a' b' : C} (bp_ab : BinProduct _ a b)
             (bp_ab' : BinProduct _ a' b') (isoa : iso a a') (isob : iso b b') :
    BinProduct_pw_iso_mor bp_ab bp_ab' isoa isob · BinProduct_pw_iso_mor bp_ab' bp_ab
                          (iso_inv_from_iso isoa) 
                          (iso_inv_from_iso isob) = 
    identity (BPO bp_ab).
  Proof.
   etrans;[apply postcompWithBinProductArrow|].
   apply pathsinv0.
   cbn.
   do 2 rewrite <- assoc.
   do 2 rewrite iso_inv_after_iso.
   do 2 rewrite id_right.
   apply  BinProduct_endo_is_identity; [apply BinProductPr1Commutes| apply BinProductPr2Commutes].
  Qed.
  Definition BinProduct_pw_iso_is_inverse {a b a' b' : C} (bp_ab : BinProduct _ a b)
             (bp_ab' : BinProduct _ a' b') (isoa : iso a a') (isob : iso b b') :
      is_inverse_in_precat (BinProduct_pw_iso_mor bp_ab bp_ab' isoa isob)
    (BinProduct_pw_iso_mor bp_ab' bp_ab (iso_inv_from_iso isoa) (iso_inv_from_iso isob)).
  Proof.
    - use mk_is_inverse_in_precat.
      + apply BinProduct_pw_eq_id.
      + 
        etrans.
        {
        apply maponpaths.
        apply map_on_two_paths; eapply pathsinv0; apply iso_inv_iso_inv.
        }
        apply BinProduct_pw_eq_id.
  Defined.
  Definition BinProduct_pw_iso {a b a' b' : C} (bp_ab : BinProduct _ a b)
             (bp_ab' : BinProduct _ a' b') (isoa : iso a a') (isob : iso b b') :
    iso (BPO bp_ab) (BPO bp_ab').
  Proof.
    eapply isopair.
    eapply is_iso_from_is_z_iso.
    eapply mk_is_z_isomorphism.
    unshelve apply BinProduct_pw_iso_is_inverse; assumption.
  Defined.
    


End BinProdComplements.