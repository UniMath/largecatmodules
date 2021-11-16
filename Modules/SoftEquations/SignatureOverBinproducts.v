(**
BinProducts of over-signatures using LModulesBinProducts
(inspired by SignatureBinproducts
pullback binproducts

TODO: réfléchir à comment factoriser avec signatureBinproducts

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import Modules.Prelims.lib.

Require Import Modules.Prelims.LModulesBinProducts.
Require Import Modules.Prelims.BinProductComplements.

Require Import Modules.Signatures.HssSignatureCommutation.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.SignatureBinproducts.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.Signatures.ModelCat.


Local Notation BPO := (BinProductObject _ ).

Section Binprod.
  Context {C : category} .

  Context {cpC : BinProducts  C}.
  Context (Sig : signature C).

  Local Notation hsC := (homset_property C).


  Local Notation Signature := (signature C).
  Local Notation MOD R := (category_LModule R C).

  Let cpLM (X : Monad C) := LModule_BinProducts   X cpC.
  Let cpFunc := BinProducts_functor_precat  C _ cpC.

  Context (a b : signature_over Sig).

  Definition signature_over_BinProduct_on_objects (R : model Sig ) : LModule R C :=
    BPO (cpLM R (a R) (b R)).

  Let ab := signature_over_BinProduct_on_objects.

  Definition signature_over_BinProduct_on_morphisms (R S : model Sig)
             (f : rep_fiber_mor R S) : LModule_Mor _ (ab R)
                                               (pb_LModule f (ab S)).
    eapply (compose (C := (MOD _))); revgoals.
    - cbn.
      apply binprod_pbm_to_pbm_binprod.
    - apply  (BinProductOfArrows _  (cpLM R _ _) (cpLM R _ _)).
      exact ((# a f)%sigo).
      exact ((# b f)%sigo).
  Defined.

  Definition signature_over_binProd_data : signature_over_data Sig
    := signature_over_BinProduct_on_objects ,, signature_over_BinProduct_on_morphisms.

  Lemma signature_over_binProd_is_signature_over : is_signature_over _ signature_over_binProd_data.
  Proof.
    split.
    - intros R c.
      cbn  -[BinProductOfArrows].
      rewrite id_right.
      apply pathsinv0.
      apply BinProductArrowUnique.
      + etrans;[apply id_left|].
        apply pathsinv0.
        etrans;[|apply id_right].
        apply cancel_precomposition.
        apply signature_over_id.
      + etrans;[apply id_left|].
        apply pathsinv0.
        etrans;[|apply id_right].
        apply cancel_precomposition.
        apply signature_over_id.
    - intros R S T f g.
      apply LModule_Mor_equiv.
      { apply homset_property. }
      apply nat_trans_eq.
      apply homset_property.
      intro x.
      cbn  -[BinProductOfArrows ].
      repeat  rewrite id_right.
      apply pathsinv0.
      etrans; [apply BinProductOfArrows_comp|].
      apply BinProductOfArrows_eq.
      + assert (h := signature_over_comp _ a f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
      + assert (h := signature_over_comp _ b f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
  Qed.
      
  Definition signature_over_binProd : signature_over Sig := _ ,, signature_over_binProd_is_signature_over.

  Lemma signature_over_binProductPr1_laws : 
    is_signature_over_Mor _ signature_over_binProd a 
                 (fun R => BinProductPr1  _  (cpLM R (a R) (b R)   )).
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn -[BinProductPr1 BinProductOfArrows].
    rewrite id_right.
    cbn.
    unfold binproduct_nat_trans_pr1_data.
    set (CC := cpC _ _).
    use (BinProductOfArrowsPr1 _  CC).
  Qed.

  Lemma signature_over_binProductPr2_laws : 
    is_signature_over_Mor _ signature_over_binProd b 
                 (fun R => BinProductPr2  _  (cpLM R (a R) (b R)   )).
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn -[BinProductPr2 BinProductOfArrows].
    rewrite id_right.
    cbn.
    unfold binproduct_nat_trans_pr2_data.
    set (CC := cpC _ _).
    use (BinProductOfArrowsPr2 _  CC).
  Qed.

  Definition signature_over_binProductPr1 : 
    signature_over_Mor  _ signature_over_binProd a := _ ,, signature_over_binProductPr1_laws .

  Definition signature_over_binProductPr2 : 
    signature_over_Mor  _ signature_over_binProd b := _ ,, signature_over_binProductPr2_laws .

  (* TODO : move to Signature_Over *)
  Definition signature_over_binProductArrow_laws {c : signature_over _} (ca :  signature_over_Mor _ c a )
             (cb : signature_over_Mor _ c b)
    :
    is_signature_over_Mor
      _ c signature_over_binProd 
      (fun R => BinProductArrow  _  (cpLM R (a R) (b R)) (ca R) (cb R))  .
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn -[BinProductPr1 BinProductPr2 BinProductOfArrows].
    rewrite id_right.
    unfold binproduct_nat_trans_data.
    apply pathsinv0.
    etrans;[apply postcompWithBinProductArrow|].
    apply pathsinv0.
    apply BinProductArrowUnique.
    - cbn.
      etrans.
      {
        rewrite <- assoc.
        apply cancel_precomposition.
        set (CC := cpC _ _).
        apply (BinProductPr1Commutes _ _ _ CC).
      }
      apply signature_over_Mor_ax_pw.
    - cbn.
      etrans.
      {
        rewrite <- assoc.
        apply cancel_precomposition.
        set (CC := cpC _ _).
        apply (BinProductPr2Commutes _ _ _ CC).
      }
      apply signature_over_Mor_ax_pw.
  Qed.

  Definition signature_over_binProductArrow {c : signature_over _} (ca :  signature_over_Mor _ c a )
             (cb : signature_over_Mor _ c b) : 
    signature_over_Mor _ c signature_over_binProd  := _ ,, signature_over_binProductArrow_laws ca cb.

  Lemma signature_over_isBinProduct : isBinProduct (signature_over_category _)  _ _ _
                                           signature_over_binProductPr1 signature_over_binProductPr2.
  Proof.
    intros c ca cb.
    use unique_exists.
    - exact (signature_over_binProductArrow ca cb).
    - split.
      + apply signature_over_Mor_eq.
        intro R.
        apply (BinProductPr1Commutes  (MOD R) _ _ (cpLM R (a R) (b R))).
      + apply signature_over_Mor_eq.
        intro R.
        apply (BinProductPr2Commutes  (MOD R) _ _ (cpLM R (a R) (b R))).
    - intro y.
      cbn -[isaprop].
      apply isapropdirprod; apply signature_over_category_has_homsets.
    - intros y [h1 h2].
      apply signature_over_Mor_eq.
      intro R.
      apply (BinProductArrowUnique   (MOD R) _ _ (cpLM R (a R) (b R))).
      + rewrite <- h1. apply idpath.
      + rewrite <- h2. apply idpath.
  Defined.

  Definition signature_over_BinProduct : BinProduct (signature_over_category _) a b :=
    make_BinProduct  _ _ _ _ _ _ signature_over_isBinProduct.


End Binprod.

(** inspired by HssSignaturecommutation *)
Section GenericStrat.
  Context {C : category}.
  Context (Sig : signature C).

  (* Context (Ff :  ∏ (R : model Sig), LModule R C). *)
  (* Context (Sf : ∏ (R S : model Sig) (f : rep_fiber_mor R S), LModule_Mor _ (Ff R) (pb_LModule f (Ff S))). *)
  Context (S_data : signature_over_data Sig).

  (* Let S1_data : signature_over_data Sig  := _ ,, Sf1. *)
  (* Let S2_data : signature_over_data  Sig  := _ ,, Sf2. *)

  Context (isS1 : is_signature_over _ S_data).
  Context (isS2 : is_signature_over _ S_data).

  Let S1 : signature_over Sig := _ ,, isS1.
  Let S2 : signature_over Sig := _ ,, isS2.



  Lemma signature_over_S1_S2_laws :
    is_signature_over_Mor _ S1 S2 (fun R => identity (C := category_LModule _ _) _).
  Proof.
    intros R S f.
    etrans; [apply id_right|].
    apply pathsinv0.
    apply id_left.
  Defined.

  Lemma signature_over_S2_S1_laws :
    is_signature_over_Mor _ S2 S1 (fun R => identity (C := category_LModule _ _) _).
  Proof.
    intros R S f.
    etrans; [apply id_right|].
    apply pathsinv0.
    apply id_left.
  Defined.

  Definition signature_over_S1_S2 : signature_over_Mor _ S1 S2 := _ ,, signature_over_S1_S2_laws.
  Definition signature_over_S2_S1 : signature_over_Mor _ S2 S1 := _ ,, signature_over_S2_S1_laws.


  Lemma signature_over_S1_S2_is_inverse  :
    is_inverse_in_precat (C := signature_over_category Sig)
                         signature_over_S1_S2 signature_over_S2_S1.
  Proof.
    use make_is_inverse_in_precat.
    - apply signature_over_Mor_eq.
      intro R.
      cbn.
      apply (id_left (C := category_LModule _ _)).
    - apply signature_over_Mor_eq.
      intro R.
      cbn.
      apply (id_left (C := category_LModule _ _)).
  Defined.

  Definition signature_over_S1_S2_iso : iso (C := signature_over_category Sig) S1 S2 :=
    make_iso _ (
              is_iso_from_is_z_iso
                _
                (make_is_z_isomorphism _ _ signature_over_S1_S2_is_inverse)).


End GenericStrat.
Local Notation ι := (sig_over_from_sig _).

Definition signature_over_BinProducts
           {C : category}
           (cpC : BinProducts C) (Sig : signature C)
            : BinProducts (signature_over_category (C := C) Sig) :=
   signature_over_BinProduct (cpC := cpC) Sig.

Definition signature_over_BinProducts_commutes_sig 
           {C : category}
           (cpC : BinProducts C) (Sig : signature C)
           (a b : signature C) :
  (* iso (C := signature_over_category Sig) *)
   iso (C := signature_over_category Sig) 
      (BPO (signature_over_BinProducts cpC _ (ι a) (ι b))) (ι (BPO (signature_BinProducts cpC a b))).
      
Proof.
  use signature_over_S1_S2_iso.
Defined.

