(**
pullback of coproducts
 Coproducts of arities using LModule Coproducts (more
conveninent than LModule.Colims) 
 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import Modules.Prelims.lib.


Require Import Modules.Prelims.LModulesCoproducts.
Require Import Modules.Signatures.Signature.


Section Coprod.
  Context {C : category} .

  Context {O : UU}.
  Context {cpC : Coproducts O C}.

  Local Notation hsC := (homset_property C).


  Local Notation Signature := (signature C).
  Local Notation MOD R := (precategory_LModule R C).

  Let cpLM (X : Monad C) := LModule_Coproducts C  X cpC.
  Let cpFunc := Coproducts_functor_precat _ C _ cpC (homset_property C).


  (* Local Notation SIGNATURE := (signature C). *)

  Context (α : O -> Signature).
  Local Notation α' R := (fun o => α o R).

  Definition signature_coprod_on_objects (R : Monad C) : LModule R C :=
    CoproductObject _ _ (cpLM R (α' R)).

  Definition signature_coprod_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (signature_coprod_on_objects R)
                                               (pb_LModule f (signature_coprod_on_objects S)).
    eapply (compose (C := (MOD _))); revgoals.
    - cbn.
      apply coprod_pbm_to_pbm_coprod.
    - apply  (CoproductOfArrows _ _ (cpLM R _) (cpLM R _)).
      intro o.
      exact ((# (α o) f)%ar).
  Defined.

  Definition signature_coprod_data : @signature_data C
    := signature_coprod_on_objects ,, signature_coprod_on_morphisms.

  Lemma signature_coprod_is_signature : is_signature signature_coprod_data.
  Proof.
    split.
    - intros R c.
      cbn  -[CoproductOfArrows].
      rewrite id_right.
      apply pathsinv0.
      apply CoproductArrowUnique.
      intro o.
      etrans;[apply id_right|].
      apply pathsinv0.
      etrans;[|apply id_left].
      apply cancel_postcomposition.
      apply signature_id.
    - intros R S T f g.
      apply LModule_Mor_equiv.
      + apply homset_property.
      + apply nat_trans_eq.
        apply homset_property.
        intro x.
        cbn  -[CoproductOfArrows ].
        repeat  rewrite id_right.
        apply pathsinv0.
        etrans; [apply CoproductOfArrows_comp|].
        apply CoproductOfArrows_eq.
        apply funextsec.
        intro i.
        assert (h := signature_comp (α i) f g).
        apply LModule_Mor_equiv in h;[|apply homset_property].
        eapply nat_trans_eq_pointwise in h.
        apply pathsinv0.
        etrans;[eapply h|].
        cbn.
        rewrite id_right.
        apply idpath.
  Qed.
      
  Definition signature_coprod : Signature := _ ,, signature_coprod_is_signature.

  Lemma signature_coproductIn_laws o : 
    is_signature_Mor (α o) signature_coprod
                 (fun R => CoproductIn  _ _  (cpLM R (fun o => α o R)) o  ).
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn -[CoproductIn CoproductOfArrows].
    rewrite id_right.
    apply pathsinv0.
    cbn.
    unfold coproduct_nat_trans_in_data.
    set (CC := cpC _).
    use (CoproductOfArrowsIn _ _ CC).
  Qed.

  Definition signature_coproductIn o : 
    signature_Mor  (α o) signature_coprod := _ ,, signature_coproductIn_laws o.

  (* TODO : move to Signature *)
  Definition signature_coproductArrow_laws {b : Signature} (cc : ∏ o, signature_Mor (α o) b ) :
    is_signature_Mor
      signature_coprod b
      (fun R => CoproductArrow  _ _  (cpLM R (fun o => α o R)) (c := b R) (fun o => cc o R)).
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn -[CoproductIn CoproductOfArrows].
    rewrite id_right.
    unfold coproduct_nat_trans_data.
    etrans;[apply precompWithCoproductArrow|].
    cbn.
    apply pathsinv0.
    apply CoproductArrowUnique.
    intro o.
    cbn.
    etrans.
    {
      etrans;[apply assoc|].
      apply cancel_postcomposition.
      set (CC := cpC _).
      apply (CoproductInCommutes _ _ _ CC).
    }
    apply pathsinv0.
    apply signature_Mor_ax_pw.
  Qed.

  Definition signature_coproductArrow {b : Signature} (cc : ∏ o, signature_Mor (α o) b ) :
    signature_Mor signature_coprod b := _ ,, signature_coproductArrow_laws cc.

  Lemma signature_isCoproduct : isCoproduct _ signature_precategory   _ _ signature_coproductIn.
  Proof.
    intros b cc.
    use unique_exists.
    - exact (signature_coproductArrow cc).
    - intro v.
      apply signature_Mor_eq.
      intro R.
      apply (CoproductInCommutes  _ (MOD R) _ (cpLM R (fun o => α o R))).
    - intro y.
      cbn -[isaprop].
      apply impred_isaprop.
      intro o.
      apply signature_category_has_homsets.
    - intros y h.
      apply signature_Mor_eq.
      intro R.
      apply (CoproductArrowUnique  _ (MOD R) _ (cpLM R (fun o => α o R))).
      cbn in h.
      intro i.
      specialize (h i).
      rewrite <- h.
      apply idpath.
  Defined.

  Definition signature_Coproduct : Coproduct _ signature_precategory α :=
    mk_Coproduct  _ _ _ _ _ signature_isCoproduct.


End Coprod.

Definition signature_Coproducts {C : category}
           {O : UU}
           (cpC : Coproducts O C)
            : Coproducts O (signature_precategory (C := C)) :=
   signature_Coproduct (cpC := cpC).