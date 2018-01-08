(**
pullback of coproducts
 Coproducts of half-arities using LModule Coproducts (more
conveninent than LModule.Colims) 
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

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Arities.LModuleCoproducts.
Require Import Modules.Arities.aritiesalt.

Section pullback_coprod.
  Context {C : category} {B : precategory}.
  Context {R : Monad B}{S : Monad B} (f : Monad_Mor R S).

  Context {O : UU}.
  Context {cpC : Coproducts O C}.

  Let cpLM (X : Monad B) := LModule_Coproducts C  X cpC.
  Let cpFunc := Coproducts_functor_precat _ B _ cpC (homset_property C).

  Context (α : O -> LModule S C ).

  Let αF : O -> functor B C := fun o => α o.
  Let pbm_α : O -> LModule R C := fun o => pb_LModule f (α o).

  Definition pbm_coprod := pb_LModule f (CoproductObject _ _ (cpLM _ α)).
  Definition coprod_pbm : LModule _ _ := CoproductObject _ _ (cpLM _ pbm_α).

  Definition coprod_pbm_to_pbm_coprod_nat_trans : nat_trans coprod_pbm pbm_coprod :=
    nat_trans_id _ .

  Lemma coprod_pbm_to_pbm_coprod_laws : LModule_Mor_laws _ (T := coprod_pbm) (T' := pbm_coprod)
                                                         coprod_pbm_to_pbm_coprod_nat_trans.
  Proof.
    intro c.
    etrans;[apply id_left|].
    apply pathsinv0.
    etrans;[apply id_right|].
    cbn.
    apply pathsinv0.
    apply CoproductOfArrows_comp.
  Qed.
  
  Definition coprod_pbm_to_pbm_coprod : LModule_Mor  _ coprod_pbm pbm_coprod :=
    _ ,, coprod_pbm_to_pbm_coprod_laws.
End pullback_coprod.

Section Coprod.
  Context {C : category} .

  Context {O : UU}.
  Context {cpC : Coproducts O C}.

  Local Notation hsC := (homset_property C).


  Local Notation HalfArity := (arity C).
  Local Notation MOD R := (precategory_LModule R C).

  Let cpLM (X : Monad C) := LModule_Coproducts C  X cpC.
  Let cpFunc := Coproducts_functor_precat _ C _ cpC (homset_property C).


  (* Local Notation HARITY := (arity C). *)

  Context (α : O -> HalfArity).
  Local Notation α' R := (fun o => α o R).

  Definition harity_coprod_on_objects (R : Monad C) : LModule R C :=
    CoproductObject _ _ (cpLM R (α' R)).

  Definition harity_coprod_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (harity_coprod_on_objects R)
                                               (pb_LModule f (harity_coprod_on_objects S)).
    eapply (compose (C := (MOD _))); revgoals.
    - cbn.
      apply coprod_pbm_to_pbm_coprod.
    - apply  (CoproductOfArrows _ _ (cpLM R _) (cpLM R _)).
      intro o.
      exact ((# (α o) f)%ar).
  Defined.

  Definition harity_coprod_data : @arity_data C
    := harity_coprod_on_objects ,, harity_coprod_on_morphisms.

  Lemma harity_coprod_is_arity : is_arity harity_coprod_data.
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
      apply arity_id.
    - intros R S T f g.
      apply LModule_Mor_equiv.
      now apply homset_property.
      apply nat_trans_eq.
      now apply homset_property.
      intro x.
      cbn  -[CoproductOfArrows ].
      repeat  rewrite id_right.
      apply pathsinv0.
      etrans; [apply CoproductOfArrows_comp|].
      apply CoproductOfArrows_eq.
      apply funextsec.
      intro i.
      assert (h := arity_comp (α i) f g).
      apply LModule_Mor_equiv in h;[|apply homset_property].
      eapply nat_trans_eq_pointwise in h.
      apply pathsinv0.
      etrans;[eapply h|].
      cbn.
      now rewrite id_right.
  Qed.
      
  Definition harity_coprod : HalfArity := _ ,, harity_coprod_is_arity.

  Lemma harity_coproductIn_laws o : 
    is_arity_Mor (α o) harity_coprod
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

  Definition harity_coproductIn o : 
    arity_Mor  (α o) harity_coprod := _ ,, harity_coproductIn_laws o.

  (* TODO : move to aritiesalt *)
  Definition harity_coproductArrow_laws {b : HalfArity} (cc : ∏ o, arity_Mor (α o) b ) :
    is_arity_Mor
      harity_coprod b
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
    apply arity_Mor_ax_pw.
  Qed.

  Definition harity_coproductArrow {b : HalfArity} (cc : ∏ o, arity_Mor (α o) b ) :
    arity_Mor harity_coprod b := _ ,, harity_coproductArrow_laws cc.

  Lemma harity_isCoproduct : isCoproduct _ arity_precategory   _ _ harity_coproductIn.
  Proof.
    intros b cc.
    use unique_exists.
    - exact (harity_coproductArrow cc).
    - intro v.
      apply arity_Mor_eq.
      intro R.
      apply (CoproductInCommutes  _ (MOD R) _ (cpLM R (fun o => α o R))).
    - intro y.
      cbn -[isaprop].
      apply impred_isaprop.
      intro o.
      apply arity_category_has_homsets.
    - intros y h.
      apply arity_Mor_eq.
      intro R.
      apply (CoproductArrowUnique  _ (MOD R) _ (cpLM R (fun o => α o R))).
      cbn in h.
      intro i.
      specialize (h i).
      now rewrite <- h.
  Defined.

  Definition harity_Coproduct : Coproduct _ arity_precategory α :=
    mk_Coproduct  _ _ _ _ _ harity_isCoproduct.


End Coprod.

Definition harity_Coproducts {C : category}
           {O : UU}
           (cpC : Coproducts O C)
            : Coproducts O (arity_precategory (C := C)) :=
   harity_Coproduct (cpC := cpC).