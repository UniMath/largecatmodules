Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.


Local Notation "'SET'" := hset_precategory.
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local  Notation "α ∙∙ β" := (horcomp β α) (at level 20).

Tactic Notation "cpre" uconstr(x) := apply (cancel_precomposition x).
Tactic Notation "cpost" uconstr(x) := apply (cancel_postcomposition).

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

(*
Lemma isEpi_pre_whisker (B C :precategory)(D : category)
      (G H : functor C D) (K : functor B C) (f : nat_trans G H)
  : (∏ x, isEpi (f x)) 
    -> 
    isEpi (C:=functor_category B D )
          (x:= (G □ K)) (y:= (H □ K))
          (pre_whisker K f).
Proof.
  clear.
  intro isEpif.
  apply is_nat_trans_epi_from_pointwise_epis.
  intro a.
  apply isEpif.
Qed.
*)

(* This is true for finitary endofunctors
or assuming the axiom of choice if the target
category has effective epis
(because in this case, any epi is absolute)

 *)
(*
Lemma isEpi_post_whisker_pw (B :precategory)(C D : category)
      (G H : functor B C) (K : functor C D) (f : nat_trans G H)
  (KpreservesEpis : forall a b (g : (C ⟦ a, b⟧)%Cat), isEpi g -> isEpi ((#K g)%cat)) :
    (forall x, isEpi (C:=  _ ) (f x))
    -> ∏ b,
    isEpi 
            (post_whisker f K b).
Proof.
  intros epif b.
  apply KpreservesEpis, epif.
Qed.
*)
(*
Lemma isEpi_post_whisker (B :precategory)(C D : category)
      (G H : functor B C) (K : functor C D) (f : nat_trans G H)
  (KpreservesEpis : forall a b (g : (C ⟦ a, b⟧)%Cat), isEpi g -> isEpi ((#K g)%cat)) :
    (forall x, isEpi (C:=  _ ) (f x))
    -> isEpi (C:=functor_category B D)
            (x:= (K □ G)) (y:= (K □ H))
            (post_whisker f K ).
Proof.
  intros epif.
  apply is_nat_trans_epi_from_pointwise_epis.
  apply isEpi_post_whisker_pw; assumption.
Qed.
*)

(*
Lemma isEpi_post_whisker_HSET (choice : AxiomOfChoice.AxiomOfChoice_surj)
      (B :precategory) (C:=hset_category) ( D : category)
      (G H : functor B C) (K : functor C D) (f : nat_trans G H) :
    (forall b, isEpi  (f b))
    -> 
    isEpi (C:=functor_category B D)
            (x:= (K □ G)) (y:= (K □ H))
            (post_whisker f K).
Proof.
  apply isEpi_post_whisker.
  intros a b g epig.
  apply isSplitEpi_isEpi; [ apply homset_property|].
  apply preserves_isSplitEpi.
  apply SplitEpis_HSET; [|apply epig].
  apply choice.
Qed.
*)
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


Lemma isEpi_horcomp_pw (B : precategory)(C D : category)
      (G H : functor B C) (G' H' : functor C D)
      (f : nat_trans G H) (f':nat_trans G' H')
  (H'epi : ∏ (a b : C) (g : (C ⟦ a, b ⟧)%Cat), isEpi g → isEpi ((# H')%Cat g))
  : (∏ x, isEpi  (f x))
    -> (∏ x, isEpi (f' x))
    -> ∏ x,  isEpi (horcomp f f' x).
Proof.
  intros epif epif'.
  intro x.
  apply isEpi_comp.
  - apply epif'.
  - apply H'epi, epif.
Qed.

Lemma isEpi_horcomp_pw_HSET (choice : AxiomOfChoice.AxiomOfChoice_surj)
      {B : precategory} (C := hset_category){D : category}
      (G H : functor B C) (G' H' : functor C D)
      (f : nat_trans G H) (f':nat_trans G' H')
  : (∏ x, isEpi  (f x))
    -> (∏ x, isEpi (f' x))
    -> ∏ x, isEpi (horcomp f f' x).
Proof.
  apply isEpi_horcomp_pw.
  intros a b g epig.
  apply isSplitEpi_isEpi; [ apply homset_property|].
  apply preserves_isSplitEpi.
  apply SplitEpis_HSET; [|apply epig].
  apply choice.
Qed.
(*
Lemma isEpi_horcomp (B : precategory)(C D : category)
      (G H : functor B C) (G' H' : functor C D)
      (f : nat_trans G H) (f':nat_trans G' H')
  (H'epi : ∏ (a b : C) (g : (C ⟦ a, b ⟧)%Cat), isEpi g → isEpi ((# H')%Cat g))
  : (∏ x, isEpi  (f x))
    -> (∏ x, isEpi (f' x))
    -> isEpi (C:= functor_category B D)
             (x:= (G' □ G)) (y:= (H' □ H))
             (horcomp f f').
Proof.
  intros epif epif'.
  apply is_nat_trans_epi_from_pointwise_epis.
  apply isEpi_horcomp_pw; assumption.
Qed.
*)

(*
Lemma isEpi_horcomp_pw_HSET (choice : AxiomOfChoice.AxiomOfChoice_surj)
      {B : precategory} (C := hset_category){D : category}
      (G H : functor B C) (G' H' : functor C D)
      (f : nat_trans G H) (f':nat_trans G' H')
  : (∏ x, isEpi  (f x))
    -> (∏ x, isEpi (f' x))
    -> isEpi (C:= functor_category B D)
             (x:= (G' □ G)) (y:= (H' □ H))
             (horcomp f f').
Proof.
  apply isEpi_horcomp.
  intros a b g epig.
  apply isSplitEpi_isEpi; [ apply homset_property|].
  apply preserves_isSplitEpi.
  apply SplitEpis_HSET; [|apply epig].
  apply choice.
Qed.
*)

Lemma horcomp_assoc 
  : ∏ {B C D E : precategory} {H H' : functor B C}
      {F F' : functor C D} {G G' : functor D E} 
      (a : H ⟶ H') (b : F ⟶ F') (c : G ⟶ G') x,
    ((c ∙∙ b) ∙∙ a) x = (c ∙∙( b ∙∙ a)) x.
Proof.
  intros.
  cbn.
  symmetry.
  now rewrite functor_comp,assoc.
Qed.

(*
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

*)