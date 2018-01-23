(* coproducts are computed pointwise in the category of left modules
This is redundant with LModuleColims, but maybye more convenient to use ? Cf HArityCoproducts
to compare both uses
(inspired by LModuleColims )
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import Modules.Prelims.lib.

Local Open Scope cat.

Section ColimsModule.
  Context 
          {C : precategory}
          {O : UU} (cpC : Coproducts O C)
          {B:precategory} {R:Monad B}
          (* (hsB : has_homsets B) *)
          (hsC : has_homsets C).
  Local Notation cpFunc := (Coproducts_functor_precat _ B _ cpC hsC).
  Local Notation MOD := (precategory_LModule R (C ,, hsC)).
  Variable (d : O -> MOD).
  (* Local Notation FORGET := (forget_LMod R (C ,, hsC)). *)
  Local Notation d'  := ( fun x => (d x : LModule _ _) : functor _ _).
  (* [B , C , hsC] ). *)
  (* The natural candidate *)
  Local Notation F := (CoproductObject  _ _ (cpFunc d') : functor _ _).
  (* Local Notation F' := (lim (limFunc d') : functor _ _). *)
  (* Local Notation BP := (binproduct_functor bpC). *)

  (* Is there a lemma that state the existence of a natural transformation
  (A x B) o R --> A o R x B o R  ? *)
  (* TODO define it without nat_trans *)
  Definition LModule_coproduct_mult_data (x : B) : C ⟦ (R ∙ F) x, F x ⟧.
    use CoproductOfArrows.
    - intro v.
      cbn.
      use lm_mult.
  Defined.


  Lemma LModule_coproduct_mult_is_nat_trans : is_nat_trans _ _  LModule_coproduct_mult_data.
  Proof.
    intros x y f.
    cbn.
    unfold LModule_coproduct_mult_data.
    cbn.
    (* par unicité de la colimite *)

    etrans; [use CoproductOfArrows_comp|].
    apply pathsinv0.
    etrans; [use CoproductOfArrows_comp|].
    cbn.
    use CoproductOfArrows_eq.
    apply funextsec.
    intro i.
    cbn.
    apply pathsinv0.
    apply (nat_trans_ax (lm_mult R _)).
  Qed.

  Definition LModule_coproduct_mult : R ∙ F ⟹ F :=
    (_ ,, LModule_coproduct_mult_is_nat_trans).


  Definition LModule_coproduct_data : LModule_data R C :=
    (F ,, LModule_coproduct_mult).

  Lemma LModule_coproduct_laws : LModule_laws _ LModule_coproduct_data.
  Proof.
    split.
    - intro x.
      etrans; [use CoproductOfArrows_comp|].
      cbn.
      apply pathsinv0            .
      apply CoproductArrowUnique.
      (* etrans; [use precompWithColimOfArrows|]. *)
      intro u.
      cbn.
      rewrite id_right.
      apply pathsinv0.
      etrans;[|apply id_left].
      apply maponpaths_2.
      apply LModule_law1.
    - intro x.
      etrans; [use CoproductOfArrows_comp|].
      apply pathsinv0.
      etrans; [use CoproductOfArrows_comp|].
      cbn.
      use CoproductOfArrows_eq.
      apply funextsec.
      intro i.
      cbn.
      apply pathsinv0.
      apply LModule_law2.
  Qed.

  Definition LModule_coproduct : LModule R C := (_ ,, LModule_coproduct_laws).

  Lemma LModule_coproductIn_laws v : 
    LModule_Mor_laws R
                     (T := (d v : LModule _ _)) (T' := LModule_coproduct)
      ((CoproductIn  _ _ ( (cpFunc d')) v : nat_trans _ _) ).
  Proof.
    intro c.
    
    cbn.
    unfold LModule_coproduct_mult_data.
    set (CC1 := cpC _ ).
    set (CC2 := cpC _ ).
    use (CoproductOfArrowsIn _ _ CC1 CC2).
  Defined.


  Definition LModule_coproductIn v : MOD ⟦ d v, LModule_coproduct ⟧ :=
    _ ,, LModule_coproductIn_laws v.

  Definition LModule_coproductArrow_laws {M : LModule R C} (cc : ∏ o, MOD ⟦ d o, M ⟧) :
    LModule_Mor_laws
      _ (T := LModule_coproduct) (T' := M)
      (CoproductArrow _ _ (cpFunc d') (c := M : functor _ _) (fun o => ((cc o : LModule_Mor _ _ _) :
                                                                    nat_trans _ _))).
  Proof.
    intro c.
    apply pathsinv0.
    cbn.
    unfold LModule_coproduct_mult_data.
    cbn.
    unfold coproduct_nat_trans_data.
    etrans;[apply precompWithCoproductArrow|].
    apply pathsinv0.
    etrans.
    apply postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply LModule_Mor_σ.
  Qed.


  Definition LModule_coproductArrow {M : LModule R C} (cc : ∏ o, MOD ⟦ d o, M ⟧) :
    LModule_Mor _ LModule_coproduct M := _ ,, LModule_coproductArrow_laws  cc.



  Lemma LModule_isCoproduct : isCoproduct _ _  _ _ LModule_coproductIn.
    intros M cc.
    use unique_exists.
    - exact (LModule_coproductArrow cc).
    - intro v.
      apply LModule_Mor_equiv;[exact hsC|].
      apply (CoproductInCommutes _ _ _ (cpFunc d')).
    - intro y.
      cbn -[isaprop].
      apply  impred_isaprop.
      intro u.
      use has_homsets_LModule.
    - cbn.
      intros y h.
      apply LModule_Mor_equiv;[exact hsC|].
      apply (CoproductArrowUnique _ _ _ (cpFunc d')).
      intro u.
      exact (  maponpaths pr1 (h u)).
  Defined.


  Definition LModule_Coproduct : Coproduct _ _ d :=
    mk_Coproduct  _ _ _ _ _ LModule_isCoproduct.


End ColimsModule.

Definition LModule_Coproducts (C : category) {B : precategory}
           {O : UU}
           (R : Monad B)
           (cpC : Coproducts O C)
           (* (colims_g : Colims_of_shape g C) *)
            : Coproducts O (precategory_LModule R C) :=
   LModule_Coproduct  cpC (homset_property C).

