Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.Monads.
(* Require Import Modules.Prelims.modules. *)
Require Import UniMath.CategoryTheory.RModules.


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import Modules.Prelims.lib.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).



(*
Let T be a module on M'.

In this section, we construct the module morphism T -> id* T (which is
actully an iso) where id* T is the pullback module of T along
the identity morphism in M'.

*)
Section Pullback_Identity_Module.

    Context {B} {M':Monad B}  {C:precategory} {T  :RModule M' C}.

    Local Notation pbmid := (pb_RModule (Monad_identity M') T).

    Lemma  pbm_id_is_nat_trans  :  is_nat_trans T  pbmid (fun x => identity _).
      red; intros; simpl.
      now rewrite id_right, id_left.
    Qed.

    Definition pbm_id_nat_trans : nat_trans T pbmid  := (_ ,, pbm_id_is_nat_trans).

    Lemma pbm_id_law : RModule_Mor_laws _ (T:=T) (T':=pbmid) pbm_id_nat_trans.
      red.
      intros b; simpl.
      rewrite id_left,id_right.
      etrans.
      cpost _.
      apply Precategories.Functor_identity.
      apply id_left.
    Qed.

    Definition pbm_id  : RModule_Mor _ T pbmid := (_ ,, pbm_id_law) .

End Pullback_Identity_Module.

(*

In this section, we construct the module morphism (which is actually an iso)
between m*(m'*(T'')) and (m o m')*(T'')

*)
Section Pullback_Composition.

   Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory}
     {M'': Monad B} (m' : Monad_Mor M' M'') (T'' : RModule M'' C).

    Local Notation comp_pbm := (pb_RModule m (pb_RModule m' T'')).
    Local Notation pbm_comp := (pb_RModule (Monad_composition m  m') T'').

    Lemma pbm_mor_comp_is_nat_trans
      : is_nat_trans comp_pbm pbm_comp (fun x => identity _).
      red; intros; simpl.
      rewrite id_right.
      rewrite id_left.
      reflexivity.
    Qed.

    Definition pbm_mor_comp_nat_trans := (_ ,, pbm_mor_comp_is_nat_trans ).

    Lemma pbm_mor_comp_law : RModule_Mor_laws (T:=comp_pbm) (T':=pbm_comp) _ pbm_mor_comp_nat_trans.
      intros b; simpl.
      now rewrite id_left,id_right, (functor_comp T''), assoc.
    Qed.

    Definition pbm_mor_comp : RModule_Mor _ comp_pbm pbm_comp := (_ ,, pbm_mor_comp_law).
End Pullback_Composition.

(**
The pullback module/morphism construction allow to construct a large category of modules over monads
where objects are pairs (Monad, Module over this monad).
*)
Section LargeCatMod.

  Context (C:Precategory).


  (* range of modules *)
  Context (D:Precategory).


  Local Notation MONAD := (Precategory_Monad C).
  Local Notation MODULE R := (precategory_RModule R D).

  Definition bmod_disp_ob_mor : disp_precat_ob_mor MONAD.
  Proof.
    exists (fun R : MONAD => ob (MODULE R)).
    intros xx' yy' g h ff'.
    exact (precategory_morphisms  g ( pb_RModule  ff'  h )).
  Defined.

  Definition bmod_id_comp : disp_precat_id_comp _ bmod_disp_ob_mor.
  Proof.
    split.
    - intros x xx.
      simpl.
      apply pbm_id.
    - intros x y z f g xx yy zz ff gg.
      set (pbm_g := pb_RModule_Mor f gg).
      set (pbm_gf := (RModule_composition _ pbm_g (pbm_mor_comp f g _))).
      exact (compose ff pbm_gf).
  Defined.

  Definition bmod_data : disp_precat_data _
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


  Lemma bmod_axioms : disp_precat_axioms MONAD bmod_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    - simpl.
      unfold id_disp; simpl.
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      intros c; simpl.
      simpl.
      rewrite assoc; simpl.
      apply pathsinv0.
      etrans.
      apply bmod_transport.
      now rewrite id_right,id_left.
    - set (heqf := id_right f).
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      simpl.
      intros c.
      rewrite id_right,id_right.
      revert ff.
      induction (heqf).
      intros; simpl.
      reflexivity.
    - set (heqf:= assoc f g h).
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      intros c; simpl.
      apply pathsinv0.
      etrans.
      (* set (z:= (ff:nat c ;; gg c ;; hh c). *)
      clearbody heqf.
      apply bmod_transport.
      cbn.
      repeat rewrite id_right.
      rewrite assoc.
      reflexivity.
    - simpl.
      apply has_homsets_RModule.
  Qed.

  Definition bmod_disp : disp_precat MONAD:=
    (bmod_data ,, bmod_axioms).


End LargeCatMod.