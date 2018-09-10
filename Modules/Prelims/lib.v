(** * Some useful lemmas

Among other things:
- associativity of horizontal composition of natural transformations [horcomp_assoc]
- functors from Set preserves epis, assuming the axiom of choice [preserves_to_HSET_isEpi]

*)
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


Local Notation "'SET'" := hset_category.
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local  Notation "α ∙∙ β" := (horcomp β α) (at level 20).

Tactic Notation "cpre" uconstr(x) := apply (cancel_precomposition x).
Tactic Notation "cpost" uconstr(x) := apply (cancel_postcomposition).

Open Scope cat.
(**
If the source category B is Set, then with the axiom of choice every epimorphism is split,
thus absolute (i.e. any functor preserves epis).
*)
Definition preserves_Epi {B C : precategory} (F : functor B C) : UU :=
  ∏ a b (f : B ⟦a , b⟧), isEpi  f -> isEpi (# F f)%Cat.

(** Functor from Set preserves epimorphisms because thanks to the axiom of choice, any
    set epimorphism is absolute *)
Lemma preserves_to_HSET_isEpi (ax_choice : AxiomOfChoice.AxiomOfChoice_surj)
      (B := hset_category)  {C : category}
      (G : functor B C)
      : preserves_Epi G.
Proof.
  intros a b f epif.
  apply isSplitEpi_isEpi; [ apply homset_property|].
  apply preserves_isSplitEpi.
  apply SplitEpis_HSET; [|apply epif].
  apply ax_choice.
Qed.

Lemma isEpi_horcomp_pw (B : precategory)(C D : category)
      (G H : functor B C) (G' H' : functor C D)
      (f : nat_trans G H) (f':nat_trans G' H')
  : (∏ x, isEpi  (f' x))
    -> (∏ x, isEpi ((# H')%Cat (f x)))
    -> ∏ x,  isEpi (horcomp f f' x).
Proof.
  intros epif' epif.
  intro x.
  apply isEpi_comp.
  - apply epif'.
  - apply epif.
Qed.

Lemma isEpi_horcomp_pw2 (B : precategory)(C D : category)
      (G H : functor B C) (G' H' : functor C D)
      (f : nat_trans G H) (f':nat_trans G' H')
  : (∏ x, isEpi  (f' x))
    -> (∏ x, isEpi ((# G')%Cat (f x)))
    -> ∏ x,  isEpi (horcomp f f' x).
Proof.
  intros epif epif'.
  intro x.
  cbn.
  rewrite <- (nat_trans_ax f').
  apply isEpi_comp.
  - apply epif'.
  - apply epif.
Qed.

(** Epimorphic natural transformation between Set valued functors are pointwise epimorphic
 *)
Lemma epi_nt_SET_pw {C : precategory} {A B : functor C SET} (a : nat_trans A B) :
    isEpi (C := functor_category C  SET) a → ∏ x : C, isEpi (a x).
Proof.
  apply Pushouts_pw_epi.
  apply PushoutsHSET_from_Colims.
Qed.
(** common generalization to [maponpaths] and [toforallpaths] *)
Lemma changef_path   {T1 T2 : UU} (f g : T1 → T2) (t1 t2 : T1) :
  f = g -> f t1 = f t2 -> g t1 = g t2.
Proof.
  induction 1; auto.
Qed.


(** Associativity of horizontal composition of natural transformations *)
Lemma horcomp_assoc 
  : ∏ {B C D E : precategory} {H H' : functor B C}
      {F F' : functor C D} {G G' : functor D E} 
      (a : nat_trans H H') (b : nat_trans F F') (c : nat_trans G G') x,
    ((c ∙∙ b) ∙∙ a) x = (c ∙∙( b ∙∙ a)) x.
Proof.
  intros.
  cbn.
  symmetry.
  rewrite functor_comp,assoc. apply idpath.
Qed.

(** Same as [nat_trans_comp_pointwise], but with B = A · A' *)
Definition nat_trans_comp_pointwise' :
  ∏ (C : precategory) (C' : category)  (F G H : ([C, C' , _ ])%Cat)
    (A : ([C, C' , _] ⟦ F, G ⟧)%Cat) (A' : ([C, C' , _] ⟦ G, H ⟧)%Cat) (a : C),
  ((A  : nat_trans _ _) a ·  (A' : nat_trans _ _) a)%Cat =  (A · A' : nat_trans _ _)%Cat a
  :=
  fun C C'  F G H A A' => @nat_trans_comp_pointwise C C' (homset_property C') F G H A A' _ (idpath _).


(** Composition in Set category is the usual composition of function *)
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


(* inutile, c'est juste la composition de deux morphismes *)
(*
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
*)
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