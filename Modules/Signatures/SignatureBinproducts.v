(**
BinProducts of  arities using LModulesBinProducts
(inspired by SignatureCoproduct
pullback binproducts
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
Require Import Modules.Prelims.BinProductComplements.
Require Import Modules.Prelims.LModulesBinProducts.
Require Import Modules.Signatures.Signature.


Section Binprod.
  Context {C : category} .

  Context {cpC : BinProducts  C}.

  Local Notation hsC := (homset_property C).


  Local Notation Signature := (signature C).
  Local Notation MOD R := (category_LModule R C).

  Let cpLM (X : Monad C) := LModule_BinProducts   X cpC .
  Let cpFunc := BinProducts_functor_precat  C _ cpC  .


  (* Local Notation SIGNATURE := (signature C). *)

  Context (a b : Signature).
  Local Notation BPO := (BinProductObject _ ).

  Definition signature_BinProduct_on_objects (R : Monad C) : LModule R C :=
    BPO (cpLM R (a R) (b R)).

  Let ab := signature_BinProduct_on_objects.

  Definition signature_BinProduct_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (ab R)
                                               (pb_LModule f (ab S)).
    eapply (compose (C := (MOD _))); revgoals.
    - cbn.
      apply binprod_pbm_to_pbm_binprod.
    - apply  (BinProductOfArrows _  (cpLM R _ _) (cpLM R _ _)).
      exact ((# a f)%ar).
      exact ((# b f)%ar).
  Defined.

  Definition signature_binProd_data : @signature_data C
    := signature_BinProduct_on_objects ,, signature_BinProduct_on_morphisms.

  Lemma signature_binProd_is_signature : is_signature signature_binProd_data.
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
        apply signature_id.
      + etrans;[apply id_left|].
        apply pathsinv0.
        etrans;[|apply id_right].
        apply cancel_precomposition.
        apply signature_id.
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
      + assert (h := signature_comp a f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
      + assert (h := signature_comp b f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
  Qed.
      
  Definition signature_binProd : Signature := _ ,, signature_binProd_is_signature.

  Lemma signature_binProductPr1_laws : 
    is_signature_Mor signature_binProd a 
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

  Lemma signature_binProductPr2_laws : 
    is_signature_Mor signature_binProd b 
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

  Definition signature_binProductPr1 : 
    signature_Mor  signature_binProd a := _ ,, signature_binProductPr1_laws .

  Definition signature_binProductPr2 : 
    signature_Mor  signature_binProd b := _ ,, signature_binProductPr2_laws .

  (* TODO : move to Signature *)
  Definition signature_binProductArrow_laws {c : Signature} (ca :  signature_Mor c a )
             (cb : signature_Mor c b)
    :
    is_signature_Mor
      c signature_binProd 
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
      apply signature_Mor_ax_pw.
    - cbn.
      etrans.
      {
        rewrite <- assoc.
        apply cancel_precomposition.
        set (CC := cpC _ _).
        apply (BinProductPr2Commutes _ _ _ CC).
      }
      apply signature_Mor_ax_pw.
  Qed.

  Definition signature_binProductArrow {c : Signature} (ca :  signature_Mor c a )
             (cb : signature_Mor c b) : 
    signature_Mor c signature_binProd  := _ ,, signature_binProductArrow_laws ca cb.

  Lemma signature_isBinProduct : isBinProduct signature_category   _ _ _
                                           signature_binProductPr1 signature_binProductPr2.
  Proof.
    intros c ca cb.
    use unique_exists.
    - exact (signature_binProductArrow ca cb).
    - split.
      + apply signature_Mor_eq.
        intro R.
        apply (BinProductPr1Commutes  (MOD R) _ _ (cpLM R (a R) (b R))).
      + apply signature_Mor_eq.
        intro R.
        apply (BinProductPr2Commutes  (MOD R) _ _ (cpLM R (a R) (b R))).
    - intro y.
      cbn -[isaprop].
      apply isapropdirprod; apply signature_category_has_homsets.
    - intros y [h1 h2].
      apply signature_Mor_eq.
      intro R.
      apply (BinProductArrowUnique   (MOD R) _ _ (cpLM R (a R) (b R))).
      + rewrite <- h1. apply idpath.
      + rewrite <- h2. apply idpath.
  Defined.

  Definition signature_BinProduct : BinProduct signature_category a b :=
    make_BinProduct  _ _ _ _ _ _ signature_isBinProduct.


End Binprod.

Definition signature_BinProducts {C : category}
           (cpC : BinProducts C)
            : BinProducts (signature_category (C := C)) :=
   signature_BinProduct (cpC := cpC).
