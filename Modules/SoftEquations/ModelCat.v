
(** * Category of models of a signature

- Direct definition, not as a fiber category over a displayed category
- proof  that it is isomorphic to the definition as a fiber category ([catiso_modelcat])

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

Context {C : category}.

Local Notation MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).
Local Notation SIG := (signature C).

(** *)
Definition rep_fiber_mor_law {a : SIG} (M N : model a) 
           (g : Monad_Mor M N)
  : UU
  := ∏ c : C, rep_τ M c · g c = ((#a g)%ar:nat_trans _ _) c ·  rep_τ N c .

Lemma isaprop_rep_fiber_mor_law {a  : SIG} (M N : model a)
      (g : Monad_Mor M N) 
  : isaprop (rep_fiber_mor_law  M N  g).
Proof.
  intros.
  apply impred; intro c.
  apply homset_property.
Qed.

Definition rep_fiber_mor {a : SIG} (M N : model a)  :=
  ∑ g:Monad_Mor M N, rep_fiber_mor_law  M N g.

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

Coercion monad_morphism_from_rep_fiber_mor {a : SIG} {M N : model a} 
          (h : rep_fiber_mor M N) : Monad_Mor M N
  := pr1 h.

Definition rep_fiber_mor_ax {a : SIG} {M N : model a} 
            (h:rep_fiber_mor  M N ) :
  ∏ c, rep_τ M c · h c = (#a h)%ar c ·  rep_τ N c 
  := pr2 h.

Lemma rep_fiber_mor_eq_nt {a : SIG} (R S:model a)
      (u v: rep_fiber_mor R S) :
  ( u : nat_trans _ _) = v -> u = v.
Proof.
  intros.
  use (invmap (subtypeInjectivity _ _ _ _  )). 
  - intro g.
    apply isaprop_rep_fiber_mor_law.
  - use (invmap (Monad_Mor_equiv _ _  _  )).  
     +  apply homset_property.
     +  assumption.
Qed.

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

Lemma is_rep_fiber_id {a : SIG} (M : model a) : rep_fiber_mor_law M M (identity (C := MONAD) (M : Monad _)).
Proof.
  intro c.
  rewrite signature_id.
  etrans;[apply id_right|].
  apply pathsinv0.
  apply id_left.
Qed.

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

Definition rep_fiber_id {a : SIG} (M : model a) : rep_fiber_mor M M :=
    tpair _ _ (is_rep_fiber_id M).

Definition rep_fiber_comp {a : SIG} {M N O: model a}
      (f : rep_fiber_mor M N) (g : rep_fiber_mor N O) : rep_fiber_mor M O :=
  tpair _ _ (is_rep_fiber_comp f g).

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

Definition rep_fiber_precategory (S : SIG) : precategory :=
  tpair (fun C => is_precategory C)
        (rep_fiber_precategory_data S)
        (is_precategory_rep_fiber_precategory_data S).

Lemma rep_fiber_category_has_homsets (S : SIG) : has_homsets (rep_fiber_precategory S).
Proof.
  intros F G.
  apply isaset_rep_fiber_mor.
Qed.


Definition rep_fiber_category (S : SIG) : category.
Proof.
  exists (rep_fiber_precategory S).
  apply rep_fiber_category_has_homsets.
Defined.

(** Proof that it is isomorphic to the fiber category definition *)

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