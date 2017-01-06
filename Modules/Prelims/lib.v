Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.RModules. 


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

Local Notation SET := hset_precategory.
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local  Notation "α ∙∙ β" := (horcomp β α) (at level 20).

Set Automatic Introduction.
Lemma comp_cat_comp {A B C:hSet} (f : A -> B) (g:B -> C) x :
  g (f x) = compose (C:= SET) f g x.
Proof.
  reflexivity.
Qed.

Lemma cancel_functor_on_morph :
  Π (C C' : precategory_ob_mor)
    (F : functor_data C C') (a b : C) (m m': C ⟦ a, b ⟧) ,
  m = m' -> #F m = #F m'.
Proof.
  intros ??????? e.
  now destruct e.
Qed.



Lemma isEpi_pre_whisker (B C :precategory)( D:Precategory)
      (G H : functor C D) ( K : functor B C) (f:nat_trans G H)
  : (Π x, isEpi (* (C:= functor_Precategory _ _) *) (f x)) -> isEpi (C:=functor_Precategory B D )
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
or assuming the axiom of choice
 *)
Lemma isEpi_post_whisker (B :precategory)(C D:Precategory)
      (G H : functor B C) ( K : functor C D) (f:nat_trans G H)
  : isEpi (C:= functor_Precategory _ _) f
    -> isEpi (C:=functor_Precategory B D)
            (x:= (K □ G)) (y:= (K □ H))
            (post_whisker f K).
Proof.
  clear.
Admitted.

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


Lemma isEpi_horcomp (B :precategory)(C D:Precategory)
      (G H : functor B C) (G' H' : functor C D)
      (f:nat_trans G H) (f':nat_trans G' H')
  : isEpi (C:= functor_Precategory _ _) f
    -> (Π x, isEpi  (f' x))
    -> isEpi (C:=functor_Precategory B D)
            (x:= (G' □ G)) (y:= (H' □ H))
            (horcomp f f').
Proof.
  intros epif epif'.
  rewrite horcomp_pre_post.
  apply isEpi_comp.
  -now apply isEpi_pre_whisker.
  -now apply isEpi_post_whisker.
Qed.


Lemma horcomp_assoc : Π {B C D E : precategory} {H H':functor B C}
                        {F F' : functor C D}
                        {G G'  : functor D E} (a: H ⟶ H')(b: F ⟶ F') (c:G ⟶ G') x,
                      ((c ∙∙ b) ∙∙ a) x = (c ∙∙( b ∙∙ a)) x.
Proof.
  intros.
  cbn.
  symmetry.
  now rewrite functor_comp,assoc.
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
