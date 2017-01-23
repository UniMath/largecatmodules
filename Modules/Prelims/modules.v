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

(**
TODO : To be moved in the files Monads and modules

Monads and Modules are more than precategories : they are Precategories (homset property)

*)
Section PrecatModulesMonads.

  (* mis dans UniMaths *)
  Section MonadPrecategory.
    Variable  (C:Precategory).

    (* total_precat_has_homsets *)
    Lemma monad_category_has_homsets : has_homsets (precategory_Monad C (homset_property C)).
      intros F G.
      simpl.

      unfold Monad_Mor.
      apply isaset_total2 .
      apply isaset_nat_trans.
      apply homset_property.
      intros m.

      apply isasetaprop.
      apply isaprop_Monad_Mor_laws.
      apply homset_property.
    Qed.

    Definition monadPrecategory  : Precategory :=
      (precategory_Monad C (homset_property C) ,, monad_category_has_homsets ).

  End MonadPrecategory.

  (* mis dans UniMaths *)
  Section ModulePrecategory.

    (* We don't need the hypothesis that C has homsets *)
    Context {C:precategory} (R:Monad C) (D:Precategory).

    Lemma rmodule_category_has_homsets : has_homsets
                                           (precategory_RModule R D (homset_property D)).
      intros F G.
      simpl.

      apply isaset_total2 .
      apply isaset_nat_trans.
      apply homset_property.
      intros m.

      apply isasetaprop.
      apply isaprop_RModule_Mor_laws.
      apply homset_property.
    Qed.

    Definition rmodulePrecategory  : Precategory :=
      (precategory_RModule R D (homset_property D) ,, rmodule_category_has_homsets ).

  End ModulePrecategory.

End PrecatModulesMonads.


(* The name is self-explainatory : any monad R is a module over R *)
(* mis dans UniMath (PR) *)
Section TautologicalModule.

  Context {C:precategory} (R:Monad C).



  Definition taut_rmod_data  : RModule_data R C.
    intros.
    exists (pr1 R).
    apply μ.
  Defined.

  Lemma taut_rmod_law  : RModule_laws R (taut_rmod_data ).
  Proof.
    split; intro c.
    - apply Monad_law2.
    - apply Monad_law3.
  Qed.

  Definition taut_rmod : RModule R C := (taut_rmod_data ,, taut_rmod_law ).


End TautologicalModule.


(* Let m : M -> M' a monad morphism.

m induces a functor m* between the category of modules over M' and the category of modules over M

If T is a module over M', we call m* T the pullback module of T along m
*)
(* mis dans UniMath *)
Section Pullback_module.
  Context {B:precategory} {M M':Monad B} (m: Monad_Mor M M').

  Context {C:precategory}.

  Variable (T:RModule M' C).

  Definition pbm_σ : T □ M ⟶ T :=  (T ∘ m) ;;; σ _ T.

  Definition pbm_data : Σ F : functor B C, F □ M ⟶ F := tpair _ (T:functor B C) pbm_σ.

  Definition pbm_laws : RModule_laws M pbm_data.
    split.
    - simpl.
      assert (hT1:= RModule_law2 _ (T:=T)).
      assert (hT2:= RModule_law1 _ (T:=T)).
      intro c.
      rewrite <- hT2; clear hT2.
      simpl.
      assert (hm := Monad_Mor_η m).
      rewrite <- hm; clear hm.
      rewrite functor_comp.
      now rewrite assoc.
    - simpl.
      intro c.
      assert (hT1:= RModule_law2 _ (T:=T)).
      assert (hm := Monad_Mor_μ m).
      rewrite assoc.
      rewrite <- (functor_comp T).
      specialize (hm c).
      simpl in hm.
      etrans.
      apply cancel_postcomposition.
      apply cancel_functor_on_morph.
      apply hm.

      rewrite functor_comp.
      rewrite <- assoc.
      etrans.
      apply cancel_precomposition.
      apply hT1.
      repeat rewrite functor_comp.
      assert (hs := nat_trans_ax (σ M' T)).
      
      etrans.
      rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_ax (σ M' T)).
      now repeat rewrite assoc.
  Qed.

  Definition pullback_module : RModule M C := tpair _ _ pbm_laws.

End Pullback_module.


(*

Let m:M -> M' be a monad morphism et n : T -> T' a morphism in the category of modules over M'.
In this section we construct the morphism m* n : m*T -> m*T' in the category of modules over M
between the pullback modules along m.

*)
(* mis dans UniMath *)
Section Pullback_Module_Morphism.

  Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :RModule M' C}
          (n : RModule_Mor _ T T').

  Local Notation pbmT := (pullback_module m T).
  Local Notation pbmT' := (pullback_module m T').

  Lemma pbm_mor_law : RModule_Mor_laws M (T:=pbmT) (T':=pbmT') n.
    intros b.
    set (pbmT := pullback_module m T).
    set (pbmT' := pullback_module m T').
    cbn.
    eapply pathscomp0;revgoals.
    rewrite <-assoc.
    cpre _.
    apply RModule_Mor_σ.    
    repeat rewrite assoc.
    cpost _.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition pbm_mor  : RModule_Mor _  pbmT pbmT'  := ( _ ,, pbm_mor_law).


End Pullback_Module_Morphism.



(*
Let T be a module on M'.

In this section, we construct the module morphism T -> id* T (which is
actully an iso) where id* T is the pullback module of T along
the identity morphism in M'.

*)
Section Pullback_Identity_Module.

    Context {B} {M':Monad B}  {C:precategory} {T  :RModule M' C}.

    Local Notation pbmid := (pullback_module (Monad_identity M') T).

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

    Local Notation comp_pbm := (pullback_module m (pullback_module m' T'')).
    Local Notation pbm_comp := (pullback_module (Monad_composition m  m') T'').

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
