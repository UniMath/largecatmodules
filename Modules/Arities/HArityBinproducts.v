(**
BinProducts of half arities using LModuleBinProduct
(inspired by HArityCoproduct
pullback binproducts
 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.LModuleBinProduct.
Require Import Modules.Prelims.LModPbCommute.
Require Import Modules.Arities.aritiesalt.


Section Binprod.
  Context {C : category} .

  Context {cpC : BinProducts  C}.

  Local Notation hsC := (homset_property C).


  Local Notation HalfArity := (arity C).
  Local Notation MOD R := (precategory_LModule R C).

  Let cpLM (X : Monad C) := LModule_BinProducts   X cpC hsC.
  Let cpFunc := BinProducts_functor_precat  C _ cpC hsC .


  (* Local Notation HARITY := (arity C). *)

  Context (a b : HalfArity).
  Local Notation BPO := (BinProductObject _ ).

  Definition harity_BinProduct_on_objects (R : Monad C) : LModule R C :=
    BPO (cpLM R (a R) (b R)).

  Let ab := harity_BinProduct_on_objects.

  Definition harity_BinProduct_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (ab R)
                                               (pb_LModule f (ab S)).
    eapply (compose (C := (MOD _))); revgoals.
    - cbn.
      apply binprod_pbm_to_pbm_binprod.
    - apply  (BinProductOfArrows _  (cpLM R _ _) (cpLM R _ _)).
      exact ((# a f)%ar).
      exact ((# b f)%ar).
  Defined.

  Definition harity_binProd_data : @arity_data C
    := harity_BinProduct_on_objects ,, harity_BinProduct_on_morphisms.

  Lemma harity_binProd_is_arity : is_arity harity_binProd_data.
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
        apply (maponpaths (compose _ )).
        apply arity_id.
      + etrans;[apply id_left|].
        apply pathsinv0.
        etrans;[|apply id_right].
        apply (maponpaths (compose _ )).
        apply arity_id.
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
      + assert (h := arity_comp a f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
      + assert (h := arity_comp b f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
  Qed.
      
  Definition harity_binProd : HalfArity := _ ,, harity_binProd_is_arity.

  Lemma harity_binProductPr1_laws : 
    is_arity_Mor harity_binProd a 
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

  Lemma harity_binProductPr2_laws : 
    is_arity_Mor harity_binProd b 
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

  Definition harity_binProductPr1 : 
    arity_Mor  harity_binProd a := _ ,, harity_binProductPr1_laws .

  Definition harity_binProductPr2 : 
    arity_Mor  harity_binProd b := _ ,, harity_binProductPr2_laws .

  (* TODO : move to aritiesalt *)
  Definition harity_binProductArrow_laws {c : HalfArity} (ca :  arity_Mor c a )
             (cb : arity_Mor c b)
    :
    is_arity_Mor
      c harity_binProd 
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
        apply maponpaths.
        set (CC := cpC _ _).
        apply (BinProductPr1Commutes _ _ _ CC).
      }
      apply arity_Mor_ax_pw.
    - cbn.
      etrans.
      {
        rewrite <- assoc.
        apply maponpaths.
        set (CC := cpC _ _).
        apply (BinProductPr2Commutes _ _ _ CC).
      }
      apply arity_Mor_ax_pw.
  Qed.

  Definition harity_binProductArrow {c : HalfArity} (ca :  arity_Mor c a )
             (cb : arity_Mor c b) : 
    arity_Mor c harity_binProd  := _ ,, harity_binProductArrow_laws ca cb.

  Lemma harity_isBinProduct : isBinProduct arity_precategory   _ _ _
                                           harity_binProductPr1 harity_binProductPr2.
  Proof.
    intros c ca cb.
    use unique_exists.
    - exact (harity_binProductArrow ca cb).
    - split.
      + apply arity_Mor_eq.
        intro R.
        apply (BinProductPr1Commutes  (MOD R) _ _ (cpLM R (a R) (b R))).
      + apply arity_Mor_eq.
        intro R.
        apply (BinProductPr2Commutes  (MOD R) _ _ (cpLM R (a R) (b R))).
    - intro y.
      cbn -[isaprop].
      apply isapropdirprod; apply arity_category_has_homsets.
    - intros y [h1 h2].
      apply arity_Mor_eq.
      intro R.
      apply (BinProductArrowUnique   (MOD R) _ _ (cpLM R (a R) (b R))).
      + rewrite <- h1. apply idpath.
      + rewrite <- h2. apply idpath.
  Defined.

  Definition harity_BinProduct : BinProduct arity_precategory a b :=
    mk_BinProduct  _ _ _ _ _ _ harity_isBinProduct.


End Binprod.

Definition harity_BinProducts {C : category}
           (cpC : BinProducts C)
            : BinProducts (arity_precategory (C := C)) :=
   harity_BinProduct (cpC := cpC).