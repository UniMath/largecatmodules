(**

forgetful functor
pullback functor

- pull back functor (base change). This is mathematically redundant with the
proof that it is a fibration
but more convenient to use

let f : R -> S be a morphism of monads

- f' : R -> f* S morphism of R-modules
- displayed categories of modules over a monad 
- proof that it is a fibration

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
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModPbCommute.

Open Scope cat.

Section ForgetLModFunctor.
  Context {B : precategory} (R : Monad B) (C : category).
  Local Notation MOD := (precategory_LModule R C).

  Definition forget_LMod_data : functor_data MOD [B,C] :=
    mk_functor_data (C := MOD) (C' := [B,C])
                    (fun X => ((X : LModule _ _): functor _ _))
                    (fun a b f => ((f : LModule_Mor _ _ _) : nat_trans _ _)).

  Definition forget_LMod_is_functor : is_functor forget_LMod_data :=
    (( fun x => idpath _) : functor_idax forget_LMod_data)
      ,, ((fun a b c f g => idpath _) : functor_compax forget_LMod_data).

  Definition forget_LMod: functor MOD [B,C] :=
    mk_functor forget_LMod_data forget_LMod_is_functor.
End ForgetLModFunctor.
Section PbmFunctor.
  Context {B : precategory} {C : category} {R S : Monad B} (f : Monad_Mor R S).
  Let MOD (R : Monad B) := (precategory_LModule R C).
  Definition pbm_functor_data : functor_data (MOD S) (MOD R) :=
    mk_functor_data (C := MOD S) (C' := MOD R) (pb_LModule f )
                    (@pb_LModule_Mor _ _ _ f _).
  Lemma pbm_is_functor : is_functor pbm_functor_data.
  Proof.
    split.
    - intro M.
      apply LModule_Mor_equiv;[apply homset_property|]; apply idpath.
    - intros X Y Z u v.
      apply LModule_Mor_equiv;[apply homset_property|]; apply idpath.
  Qed.

  Definition pb_LModule_functor : functor (MOD S) (MOD R) :=
                              mk_functor _ pbm_is_functor.
End PbmFunctor.
(** strangely enough, I didn't find the following lemma :
 *)
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



(**
The pullback module/morphism construction allow to construct a large category of modules over monads
where objects are pairs (Monad, Module over this monad).
*)
Section LargeCatMod.

Context (C: category).
(* range of modules *)
Context (D:category).

Local Notation MONAD := (category_Monad C).
Local Notation MODULE R := (category_LModule R D).

Definition bmod_disp_ob_mor : disp_cat_ob_mor MONAD.
Proof.
  exists (fun R : MONAD => ob (MODULE R)).
  intros xx' yy' g h ff'.
  exact (precategory_morphisms  g ( pb_LModule  ff'  h )).
Defined.

Definition bmod_id_comp : disp_cat_id_comp _ bmod_disp_ob_mor.
Proof.
  split.
  - intros x xx.
    simpl.
    apply pbm_id.
  - intros x y z f g xx yy zz ff gg.
    set (pbm_g := pb_LModule_Mor f gg).
    set (pbm_gf := (LModule_composition _ pbm_g (pbm_mor_comp f g _))).
    simpl in ff.
    exact (compose (C:=category_LModule _ _ ) ff pbm_gf).
Defined.

Definition bmod_data : disp_cat_data _
    := (bmod_disp_ob_mor ,, bmod_id_comp).

(* Peut etre que c'est le genre de pb qui intéresse André.. Cf utilisation de foo *)
Lemma bmod_transport (x y : MONAD) (f g : MONAD ⟦ x, y ⟧)
      (e : f = g)
      (xx : bmod_data x)
      (yy : pr1 bmod_data y)
      (ff : xx -->[ f] yy)
      (c : C) : (pr1 (transportf (mor_disp xx yy) e ff) c = pr1 ff c).
Proof.
  induction e.
  intros.
  apply idpath.
Qed.


Lemma bmod_axioms : disp_cat_axioms MONAD bmod_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  - simpl.
    unfold id_disp; simpl.
    apply (invmap ((@LModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
    apply nat_trans_eq; try apply homset_property.
    intros c; simpl.
    simpl.
    rewrite assoc; simpl.
    apply pathsinv0.
    etrans; [apply bmod_transport |].
    rewrite id_right,id_left; apply idpath.
  - set (heqf := id_right f).
    apply (invmap ((@LModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
    apply nat_trans_eq; try apply homset_property.
    simpl.
    intros c.
    rewrite id_right,id_right.
    revert ff.
    induction (heqf).
    intros; simpl.
    reflexivity.
  - set (heqf:= assoc f g h).
    apply (invmap ((@LModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
    apply nat_trans_eq; try apply homset_property.
    intros c; simpl.
    apply pathsinv0.
    etrans; [ apply bmod_transport |].
    cbn.
    repeat rewrite id_right.
    apply pathsinv0, assoc.
Qed.

Definition bmod_disp : disp_cat MONAD := (bmod_data ,, bmod_axioms).

Definition cleaving_bmod : cleaving bmod_disp.
Proof.
  intros R R' f M.
  use tpair.
  - cbn in *.  
    exact (pb_LModule f M).
  - use tpair.
    + exact (LModule_identity _ _ ).
    + intros R'' f' M'' a.
      cbn in *.
      use unique_exists.
      * use (LModule_composition R'' a). 
        apply (pbm_comp_mor _ _ _ ).
      * hnf.
        apply (invmap ((@LModule_Mor_equiv _ _  _ (homset_property D) _ _ _ _  ))).
        cbn.
        apply nat_trans_eq. { apply homset_property. }
        intro c. cbn. 
        repeat rewrite id_right. apply idpath.
      * intro s. simpl.
        apply (has_homsets_LModule).
      * intros s Hs.
        hnf in Hs.
        apply (invmap ((@LModule_Mor_equiv _ _  _ (homset_property D) _ _ _ _  ))).
        apply nat_trans_eq. { apply homset_property. }
        intro c. cbn.
        apply (((@LModule_Mor_equiv _ _  _ (homset_property D) _ _ _ _  ))) in Hs.
        set (XR := nat_trans_eq_pointwise Hs c). cbn in XR.
        repeat rewrite id_right in XR.
        repeat rewrite id_right.
        apply XR.
Defined.
        
End LargeCatMod.