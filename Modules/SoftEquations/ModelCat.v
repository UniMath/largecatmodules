(** * Category of models of a signature

- [rep_fiber_category]: Direct definition 
- [catiso_modelcat]: proof that this category is isomorphic to the definition as a fiber category
  of the fibration of the total 1-model category over the 1-signatures category,
  as defined in Signatures/Signature.v

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.

Require Import Modules.Signatures.Signature.

Section ModelCat.

(**
We work  in a category [C], and are going to define the 1-models of a fixed 1-signature.
*)
Context {C : category}.

Local Notation MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).
Local Notation SIG := (signature C).

(** This proposition states that the monad morphism [g] between two 1-models
    commutes with the action [model_τ].
 *)
Definition rep_fiber_mor_law {a : SIG} (M N : model a) 
           (g : Monad_Mor M N)
  : UU
  := ∏ c : C, model_τ M c · g c = ((#a g)%ar:nat_trans _ _) c ·  model_τ N c .

(** This statment is hProp *)
Lemma isaprop_rep_fiber_mor_law {a  : SIG} (M N : model a)
      (g : Monad_Mor M N) 
  : isaprop (rep_fiber_mor_law  M N  g).
Proof.
  intros.
  apply impred; intro c.
  apply homset_property.
Qed.

(** A model morphism [g] between two 1-models [M] and [N] is a monad morphism
    commuting with the action [model_τ].
 *)
Definition rep_fiber_mor {a : SIG} (M N : model a)  :=
  ∑ g:Monad_Mor M N, rep_fiber_mor_law  M N g.

(** Homsets of 1-models are hSet *)
Lemma isaset_rep_fiber_mor {a : SIG} (M N : model a)  :
  isaset (rep_fiber_mor  M N ).
Proof.
  intros.
  apply isaset_total2 .
  - apply has_homsets_Monad.
  - intros.
    apply isasetaprop.
    apply isaprop_rep_fiber_mor_law.
Qed.

(** Coercion from 1-model morphism to monad morphisms *)
Coercion monad_morphism_from_rep_fiber_mor {a : SIG} {M N : model a} 
          (h : rep_fiber_mor M N) : Monad_Mor M N
  := pr1 h.

(** A model morphism commutes with the action *)
Definition rep_fiber_mor_ax {a : SIG} {M N : model a} 
            (h:rep_fiber_mor  M N ) :
  ∏ c, model_τ M c · h c = (#a h)%ar c ·  model_τ N c 
  := pr2 h.

(** If two 1-model morphisms are equal as natural transformations, then they are equal *)
Lemma rep_fiber_mor_eq_nt {a : SIG} (R S:model a)
      (u v: rep_fiber_mor R S) :
  (u : nat_trans _ _) = v -> u = v.
Proof.
  intros.
  use (invmap (subtypeInjectivity _ _ _ _  )). 
  - intro g.
    apply isaprop_rep_fiber_mor_law.
  - use (invmap (Monad_Mor_equiv _ _  _  )).  
     +  apply homset_property.
     +  assumption.
Qed.

(** If two 1-model morphisms are pointwise equal, then they are equal *)
Lemma rep_fiber_mor_eq {a : SIG} (R S:model a)
      (u v: rep_fiber_mor R S) :
  (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c) -> u = v.
Proof.
  intros.
  apply rep_fiber_mor_eq_nt.
  apply nat_trans_eq.
  - apply homset_property.
  - assumption.
Qed.

(** The identity natural transformation commutes with the action *)
Lemma is_rep_fiber_id {a : SIG} (M : model a)
  : rep_fiber_mor_law M M (identity (C := MONAD) (M : Monad _)).
Proof.
  intro c.
  rewrite signature_id.
  etrans;[apply id_right|].
  apply pathsinv0.
  apply id_left.
Qed.

(** The composition of two 1-model morphisms commutes with the action *)
Lemma is_rep_fiber_comp {a : SIG} {M N O: model a}
      (f : rep_fiber_mor M N) (g : rep_fiber_mor N O) : rep_fiber_mor_law M O
                                                                          (compose (C := MONAD)
                                                                                   (f : Monad_Mor _ _)
                                                                                   (g : Monad_Mor _ _)).
Proof.
  intro c.
  rewrite signature_comp.
  cbn.
  rewrite id_right.
  rewrite assoc.
  rewrite (rep_fiber_mor_ax f).
  rewrite <- assoc.
  rewrite (rep_fiber_mor_ax g).
  rewrite assoc.
  reflexivity.
Qed.

(** The identity 1-model morphism *)
Definition rep_fiber_id {a : SIG} (M : model a) : rep_fiber_mor M M :=
    tpair _ _ (is_rep_fiber_id M).

(** Composition of 1-model morphisms *)
Definition rep_fiber_comp {a : SIG} {M N O: model a}
      (f : rep_fiber_mor M N) (g : rep_fiber_mor N O) : rep_fiber_mor M O :=
  tpair _ _ (is_rep_fiber_comp f g).

(** Intermediate data to build the category of 1-models of a 1-signature [a] *)
Definition rep_fiber_precategory_ob_mor (a : SIG) : precategory_ob_mor :=
  precategory_ob_mor_pair _ (rep_fiber_mor (a := a) ).

Definition rep_fiber_precategory_data (a : SIG) : precategory_data.
Proof.
  apply (precategory_data_pair (rep_fiber_precategory_ob_mor a)).
  + intro x; simpl in x.
    apply (rep_fiber_id ).
  + intros M N O.
    apply rep_fiber_comp.
Defined.

(** 1-model morphisms satisfy the axioms of category:
- identity is a neutral element for composition
- composition is associative
 *)
Lemma is_precategory_rep_fiber_precategory_data (S : SIG) :
   is_precategory (rep_fiber_precategory_data S).
Proof.
  repeat split; simpl; intros.
  - unfold identity.
    simpl.
    apply rep_fiber_mor_eq. 
    intro x; simpl.
    apply id_left.
  - apply rep_fiber_mor_eq. 
    intro x; simpl.
    apply id_right.
  - apply rep_fiber_mor_eq. 
    intro x; simpl.
    apply assoc.
Qed.

(** The precategory of 1-model morphisms *)
Definition rep_fiber_precategory (S : SIG) : precategory :=
  tpair (fun C => is_precategory C)
        (rep_fiber_precategory_data S)
        (is_precategory_rep_fiber_precategory_data S).

(** Homsets are hSet *)
Lemma rep_fiber_category_has_homsets (S : SIG) : has_homsets (rep_fiber_precategory S).
Proof.
  intros F G.
  apply isaset_rep_fiber_mor.
Qed.


(** The category of 1-model morphisms (= precategory + Homsets are hSet *)
Definition rep_fiber_category (S : SIG) : category.
Proof.
  exists (rep_fiber_precategory S).
  apply rep_fiber_category_has_homsets.
Defined.

  (** The pullback of models along a 1-signature morphism sends morphisms
onto morphisms. This is a consequence of 1-models being fibered over 1-sigs.
However we do a direct proof here because using the fibration would lead to
a dirty term *)
  Lemma pb_rep_mor_law  {S1 S2 : signature C} (f : signature_Mor S1 S2) {R S : model S2}
             (m : rep_fiber_mor R S) : rep_fiber_mor_law (pb_rep f R) (pb_rep f S) m.
  Proof.
    intro c.
    cbn.
    etrans;[apply pathsinv0,assoc|].
    etrans;[ apply cancel_precomposition, rep_fiber_mor_ax|].
    do 2 rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply signature_Mor_ax_pw.
  Qed.

  Definition pb_rep_mor  {S1 S2 : signature C} (f : signature_Mor S1 S2) {R S : model S2}
        (m : rep_fiber_mor R S) : rep_fiber_mor (pb_rep f R) (pb_rep f S) :=
    _ ,, pb_rep_mor_law f m.

  Lemma pb_rep_mor_comp   {S1 S2 : signature C} (f : signature_Mor S1 S2) {R S T : model S2}
        (m : rep_fiber_mor R S)(n : rep_fiber_mor S T)
    : pb_rep_mor f (compose (C := rep_fiber_category S2) m n) =
      compose (C := rep_fiber_category S1) (pb_rep_mor _ m)(pb_rep_mor _ n).
  Proof.
    apply rep_fiber_mor_eq; intro; apply idpath.
  Defined.

  Lemma pb_rep_mor_id  {S1 S2 : signature C} (f : signature_Mor S1 S2) (R : model S2) :
   (pb_rep_mor f (rep_fiber_id R))  = identity (C := rep_fiber_category S1) _.
  Proof.
      apply rep_fiber_mor_eq; intro; apply idpath.
  Defined.
(**

In our presentable signatures formalization (Cf Signatures/), we have defined the
fibration (using the displayed category framework) of the total 1-model category
over the 1-signatures category (Signature.v).

A definition of 1-model category over a 1-signature is retrieved by taking the fiber category over
this signature.

The following is a proof that the two definitions (here and there) yield isomorphic categories.

 *)

Context (S : SIG).

Local Notation FIBER_CAT := (fiber_category (rep_disp C) S).
Local Notation MODEL_CAT := (rep_fiber_category S).

  Definition fib_to_dir_weq : FIBER_CAT  ≃ MODEL_CAT := idweq _.
  Local Notation FSob := fib_to_dir_weq.

  Definition fib_to_dir_mor_weq (R R' : FIBER_CAT) :
    FIBER_CAT ⟦ R , R' ⟧ ≃ MODEL_CAT  ⟦ FSob R , FSob R' ⟧.
  Proof.
    apply weqfibtototal.
    intro f.
    apply weqonsecfibers.
    intro o.
    apply eqweqmap.
    apply maponpaths.
    apply cancel_postcomposition.
    apply ( (id_right _)).
  Defined.
  Local Notation FSmor := fib_to_dir_mor_weq.

  Definition fib_to_dir_functor_data : functor_data FIBER_CAT MODEL_CAT :=
    functor_data_constr _ _  FSob  FSmor.

  Lemma fib_to_dir_is_functor : is_functor fib_to_dir_functor_data.
  Proof.
    split.
    - intro R.
      apply rep_fiber_mor_eq_nt.
      apply idpath.
    - intros R R' T f g.
      apply rep_fiber_mor_eq_nt.
      cbn.
      set (e := id_right _).
      induction e.
      apply idpath.
  Defined.

  Definition fib_to_dir_functor : functor FIBER_CAT MODEL_CAT :=
    _ ,, fib_to_dir_is_functor.
  Local Notation FS := fib_to_dir_functor.

  Definition catiso_modelcat : catiso FIBER_CAT MODEL_CAT
    := FS,, (λ x y : FIBER_CAT, weqproperty (FSmor x y)),, weqproperty FSob.


End ModelCat.