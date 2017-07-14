Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.

Require Import Modules.Prelims.lib.


(*
Let T be a module on M'.

In this section, we construct the module morphism T -> id* T (which is
actully an iso) where id* T is the pullback module of T along
the identity morphism in M'.

*)
Section Pullback_Identity_Module.

Context {B} {M':Monad B}  {C:precategory} {T : LModule M' C}.

Local Notation pbmid := (pb_LModule (Monad_identity M') T).

Lemma  pbm_id_is_nat_trans  :  is_nat_trans T pbmid (fun x => identity _).
Proof.
  intros a b f; simpl.
  now rewrite id_right, id_left.
Qed.

Definition pbm_id_nat_trans : nat_trans T pbmid  := (_ ,, pbm_id_is_nat_trans).

Lemma pbm_id_law : LModule_Mor_laws _ (T:=T) (T':=pbmid) pbm_id_nat_trans.
Proof.
  intros b; simpl.
  rewrite id_left,id_right.
  etrans.
    cpost _. apply functor_id.
  apply id_left.
Qed.

Definition pbm_id  : LModule_Mor _ T pbmid := (_ ,, pbm_id_law) .

End Pullback_Identity_Module.

(*

In this section, we construct the module morphism (which is actually an iso)
between m*(m'*(T'')) and (m o m')*(T'')

*)

Section Pullback_Composition.

Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory}
        {M'': Monad B} (m' : Monad_Mor M' M'') (T'' : LModule M'' C).

Local Notation comp_pbm := (pb_LModule m (pb_LModule m' T'')).
Local Notation pbm_comp := (pb_LModule (Monad_composition m  m') T'').

Lemma pbm_mor_comp_is_nat_trans
  : is_nat_trans comp_pbm pbm_comp (fun x => identity _).
Proof.
  red; intros; simpl.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Qed.

Definition pbm_mor_comp_nat_trans := (_ ,, pbm_mor_comp_is_nat_trans ).

Lemma pbm_mor_comp_law : LModule_Mor_laws (T:=comp_pbm) (T':=pbm_comp) _ pbm_mor_comp_nat_trans.
Proof.
  intros b; simpl.
  now rewrite id_left,id_right, (functor_comp T''), assoc.
Qed.

Definition pbm_mor_comp : LModule_Mor _ comp_pbm pbm_comp := (_ ,, pbm_mor_comp_law).
End Pullback_Composition.

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
    now rewrite id_right,id_left.
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


End LargeCatMod.