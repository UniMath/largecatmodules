Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
(*
Require Import UniMath.CategoryTheory.UnicodeNotations.
*)
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.LModules. 


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.Epis.

Local Notation "'SET'" := hset_precategory.
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local  Notation "α ∙∙ β" := (horcomp β α) (at level 20).

Tactic Notation "cpre" uconstr(x) := apply (cancel_precomposition x).
Tactic Notation "cpost" uconstr(x) := apply (cancel_postcomposition (C:=x)).

Set Automatic Introduction.

Lemma changef_path   {T1 T2 : UU} (f g : T1 → T2) (t1 t2 : T1) :
  f = g -> f t1 = f t2 ->g t1 = g t2.
Proof.
  now induction 1.
Qed.
Lemma comp_cat_comp {A B C:hSet} (f : A -> B) (g:B -> C) x :
  g (f x) = compose (C:= SET) f g x.
Proof.
  reflexivity.
Qed.


Lemma isEpi_pre_whisker (B C :precategory)( D: category)
      (G H : functor C D) ( K : functor B C) (f:nat_trans G H)
  : (∏ x, isEpi (* (C:= functor_Precategory _ _) *) (f x)) -> isEpi (C:=functor_category B D )
                                                                   (x:= (G □ K)) (y:= (H □ K))
                                                                   (pre_whisker K f).
Proof.
  clear.
  intro isEpif.
  apply is_nat_trans_epi_from_pointwise_epis.
  intro a.
  apply isEpif.
Qed.

(* This is true for finitary endofunctors
or assuming the axiom of choice if the target
category has effective epis
(because in this case, any epi is absolute)

 *)
Lemma isEpi_post_whisker (B :precategory)(C D: category)
      (G H : functor B C) ( K : functor C D) (f:nat_trans G H)
  : isEpi (C:= functor_category _ _) f
    -> isEpi (C:=functor_category B D)
            (x:= (K □ G)) (y:= (K □ H))
            (post_whisker f K).
Proof.
  clear.
Admitted.

(*
Le mettre dans UniMath
Lemma horcomp_pre_post :
  Π (C D:precategory) ( E : Precategory) (F F' : functor C D) (G G' : functor D E) (f:F ⟶ F') (g:G ⟶ G'),
  horcomp f g = compose (C:=functor_Precategory C E) (a:= (G □ F)) (b:= (G' □ F)) (c:= (G' □ F'))
                        (pre_whisker F g)
                        (post_whisker f G').
Proof.
  intros.
  apply nat_trans_eq.
  apply homset_property.
  intros;
    apply idpath.
Qed.    
*)


Lemma isEpi_horcomp (B :precategory)(C D: category)
      (G H : functor B C) (G' H' : functor C D)
      (f:nat_trans G H) (f':nat_trans G' H')
  : isEpi (C:= functor_category _ _) f
    -> (∏ x, isEpi  (f' x))
    -> isEpi (C:= functor_category B D)
            (x:= (G' □ G)) (y:= (H' □ H))
            (horcomp f f').
Proof.
  intros epif epif'.
  rewrite horcomp_pre_post.
  apply isEpi_comp.
  -now apply isEpi_pre_whisker.
  -now apply isEpi_post_whisker.
Qed.


Lemma horcomp_assoc : ∏ {B C D E : precategory} {H H':functor B C}
                        {F F' : functor C D}
                        {G G'  : functor D E} (a: H ⟶ H')(b: F ⟶ F') (c:G ⟶ G') x,
                      ((c ∙∙ b) ∙∙ a) x = (c ∙∙( b ∙∙ a)) x.
Proof.
  intros.
  cbn.
  symmetry.
  now rewrite functor_comp,assoc.
Qed.

Lemma compose_nat_trans : ∏ {C D:precategory} {F G H} (a:nat_trans F G)
                            (b:nat_trans G H) (X:C),  a X ;; b X =
                                                      nat_trans_comp
                                                        (C:=C) (C':=D)
                                                        F G H a b X.
Proof.
  intros; apply idpath.
Qed.


(* copié de ssreflect. Pour l'instant inutile *)
Lemma master_key : unit.
  exact tt.
Qed.
Definition locked {A} := unit_rect _  (fun x : A => x) master_key.

Lemma lock A x : x = locked x :> A.
Proof.
  unfold locked.
  now destruct master_key.
Qed.    
