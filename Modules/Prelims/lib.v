(** * Some useful lemmas

Among other things:
- associativity of horizontal composition of natural transformations [horcomp_assoc]
- functors from Set preserves epis, assuming the axiom of choice [preserves_to_HSET_isEpi]
- isomorphisms of categories transfer initiality
- if there is a universal arrow from the initial object, then the target category has
  an initial object [initial_universal_to_lift_initial]
- an adjunction whose unit is iso is a coreflection (i.e. the left adjoint is full and faithful)
    [isounit_coreflection]
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.


Local Notation "'SET'" := hset_category.
(* obsolete: Local Notation "G □ F" := (functor_composite F G) (at level 35).
already loaded: Local Notation "F ∙ G" := (functor_composite F G) (at level 35).*)
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local  Notation "α ∙∙ β" := (horcomp β α) (at level 20).

Tactic Notation "cpre" uconstr(x) := apply (cancel_precomposition x).
Tactic Notation "cpost" uconstr(x) := apply (cancel_postcomposition).

Open Scope cat.

(** Even true of equivalences *)
Lemma catiso_initial {C D : precategory} (w : catiso C D) (ini : Initial C) : Initial D.
Proof.
  set (obweq := catiso_ob_weq w).
  use make_Initial.
  - exact (w ini).
  - use make_isInitial.
    intro b.
    assert (h := homotweqinvweq obweq b).
    rewrite <- h.
    eapply iscontrweqb.
    + apply invweq.
      use catiso_fully_faithful_weq.
    + apply (pr2 ini).
Defined.

Lemma initial_universal_to_lift_initial {D C : category}
      (S : D ⟶ C)
      (c : Initial C)
      {r : D} {f : C ⟦ c, S r ⟧}
      (unif : is_reflection (make_reflection_data r f)) :
  isInitial _ r.
Proof.
  intro d.
  specialize (unif (make_reflection_data d (InitialArrow _ _))).
  use make_iscontr.
  - apply (iscontrpr1 unif).
  - intro g.
    apply path_to_ctr.
    refine (!InitialArrowUnique _ _ _).
Qed.

(**
hom(X , Y) ~ hom(X , U F Y) ~ hom(F X , F Y)
*)
Lemma isounit_coreflection {C : category}{D : category } {F} (isF : is_left_adjoint (A := C) (B := D) F) :
  is_iso (C := [C , C])
         (unit_from_left_adjoint isF
          : [C,C] ⟦ functor_identity _, F ∙ right_adjoint isF ⟧) -> fully_faithful F.
Proof.
  intro isounit.
  assert (homweq := (adjunction_homsetiso_weq (pr2 isF))).
  assert (isounitpw := is_functor_iso_pointwise_if_iso _ _ _ _ _ _ isounit).
  intros S1 S2.
  eapply isweqhomot; revgoals.
  - unshelve apply weqproperty.
    eapply weqcomp.
    + eapply iso_comp_left_weq.
      use (_ ,, isounitpw S2 ).
    + apply invweq.
      use hom_weq.
      apply (adjunction_homsetiso_weq (pr2 isF)).
  - intro ff.
    cbn.
    unfold φ_adj_inv; cbn.
    rewrite functor_comp.
    rewrite <- assoc.
    etrans;[ apply cancel_precomposition, triangle_id_left_ad|].
    apply id_right.
Defined.



(** common generalization to [maponpaths] and [toforallpaths] *)

Lemma changef_path   {T1 T2 : UU} (f g : T1 → T2) (t1 t2 : T1) :
  f = g -> f t1 = f t2 -> g t1 = g t2.
Proof.
  induction 1; auto.
Qed.

Lemma changef_path_pw   {T1 T2 : UU} (f g : T1 → T2) (t1 t2 : T1) :
  (∏ x, f x = g x) -> f t1 = f t2 -> g t1 = g t2.
Proof.
  intro eq.
  induction (eq t1); induction (eq t2); auto.
Qed.


(** Associativity of horizontal composition of natural transformations *)
Lemma horcomp_assoc
  : ∏ {B C D E : category} {H H' : functor B C}
      {F F' : functor C D} {G G' : functor D E}
      (a : nat_trans H H') (b : nat_trans F F') (c : nat_trans G G') x,
    ((c ∙∙ b) ∙∙ a) x = (c ∙∙( b ∙∙ a)) x.
Proof.
  intros.
  cbn.
  do 2 (unfold horcomp_data; cbn).
  symmetry.
  rewrite functor_comp,assoc. apply idpath.
Qed.

(** Same as [nat_trans_comp_pointwise], but with B = A · A' *)
Definition nat_trans_comp_pointwise' :
  ∏ (C : precategory) (C' : category)  (F G H : ([C, C' , _ ]))
    (A : ([C, C' , _] ⟦ F, G ⟧)) (A' : ([C, C' , _] ⟦ G, H ⟧)) (a : C),
  ((A  : nat_trans _ _) a ·  (A' : nat_trans _ _) a) =  (A · A' : nat_trans _ _) a
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
