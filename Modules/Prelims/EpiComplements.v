(** * Complements about epis

Main definitions:
- Pointwise epimorphic natural transformation [epis_are_pointwise]
- Products preserve epis [products_preserves_Epis]
- Functor preserving epis [preserves_Epi]

and related proofs

Note that a lot of statment (if not all) could be rephrased as preservation
of epis by some functors (for example the fact that products preserve epi
could be rephrased as the preservation of epis of some bifunctor).

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
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.coproducts.

Open Scope cat.

Definition epis_are_pointwise (B : precategory) (C : category) :=
  ∏ (F F': functor B C) (α : nat_trans F F'), isEpi (C := [B,C]) α -> ∏ b, isEpi (α b).


(** Epimorphic natural transformation between Set valued functors are pointwise epimorphic
 *)
Lemma epi_nt_SET_pw (C : precategory) : epis_are_pointwise C SET.
Proof.
  intros F F' α .
  apply Pushouts_pw_epi.
  apply PushoutsHSET_from_Colims.
Qed.

(** products of epis are epis
          This is true of regular epis in a regular category such as Set.
            (e.g. in a topos, pullbacks of epis are epis)
       *)
Definition products_preserves_Epis {C : precategory} (bpC : BinProducts C) :=
  ∏ (a b : C)  (f : C ⟦a , b⟧) (a' b' : C)(f' : C ⟦a' , b'⟧),
    isEpi  f ->
  isEpi  f' ->
  isEpi (BinProductOfArrows C (bpC _ _) (bpC _ _) f f').


(** Products of epis are epis (this is true of pullbacks) *)
Lemma productEpisSET : products_preserves_Epis BinProductsHSET.
Proof.
  intros a b f a' b' g epif epig.
  set (fg := BinProductOfArrows _ _ _ _ _).
  apply EpisAreSurjective_HSET in epif.
  apply EpisAreSurjective_HSET in epig.
  intros Y u v eq.
  apply funextfun.
  use (surjectionisepitosets  fg); revgoals.
  - apply toforallpaths.
    exact eq.
  - apply setproperty.
  - intro xx'.
    induction xx' as [x x'].
    specialize (epif x).
    specialize (epig x').
    revert epif epig.
    apply hinhfun2.
    intros y y'.
    use (hfiberpair fg ).
    + exact (hfiberpr1 _ _ y ,, hfiberpr1 _ _ y').
    + apply total2_paths2; use hfiberpr2.
Qed.

Lemma productEpisFunc {B C : category} bpC
      (prEpi : products_preserves_Epis (C := C) bpC )
      (pwEpi : epis_are_pointwise B C)
  :
  products_preserves_Epis
    (BinProducts_functor_precat B C bpC (homset_property C) )
                                                          .
Proof.
  red.
  intros a b f a' b' f' epif epif'.
  apply is_nat_trans_epi_from_pointwise_epis. 
  intro X. 
  apply prEpi; apply pwEpi;[exact epif| exact epif'].
Qed.

                                                          

(** Coproducts of epis are epis
A general argument (not formalized here): colimits commute with
colimits and epimorphisms are characterized by a pushout diagram
 *)
Lemma coproduct_Epis {C : precategory} {I : UU}(cp : Coproducts I C) 
      {a b : I -> C} (f : ∏ i, C ⟦a i , b i⟧)(epif : ∏ i, isEpi (f i)) :
  isEpi (CoproductOfArrows I _ (cp a) (cp b) f).
Proof.
  intros c u v eq.
  etrans;[apply CoproductArrowEta|apply pathsinv0; apply CoproductArrowUnique].
  intro i.
  apply pathsinv0.
  apply epif.
  do 2 rewrite assoc.
  rewrite <- (CoproductOfArrowsIn _ _ (cp  _)).
  do 2 rewrite <- assoc.
  apply cancel_precomposition.
  exact eq.
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



(** * Functor preserving of epis
 *)

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

(** The composition of two epi-preserving functors preserves epis *)
Definition composite_preserves_Epi {B C D : precategory} (F : functor B C) (G : functor C D) :
  preserves_Epi F -> preserves_Epi G -> preserves_Epi (F ∙ G).
Proof.
  intros hF hG a b f epif.
  apply hG, hF, epif.
Qed.

(** let a : F -> G be a pointwise epimorphic natural transformation.
  If F preserves epimorphisms, then G also does *)
Lemma epi_nt_preserves_Epi {B C : precategory} {F G : functor B C} (a : nat_trans F G)
      (epia : ∏ b, isEpi (a b))  (epiF : preserves_Epi F) : preserves_Epi G.
Proof.
  intros X Y f epif Z g h eq.
  unshelve eapply (_ : isEpi (a _ · # G f)).
  - rewrite <- (nat_trans_ax a).
    apply isEpi_comp.
    + apply epiF; assumption.
    + apply epia.
  - do 2 rewrite <- assoc.
    apply cancel_precomposition.
    exact eq.
Qed.

Definition id_preserves_Epi (B : precategory) : preserves_Epi (functor_identity B) :=
  fun a b f h => h.

Definition const_preserves_Epi {B C : precategory} (c : C) : preserves_Epi (constant_functor B C c) :=
  fun a b f h => identity_isEpi _.

Lemma preserveEpi_binProdFunc {B C : precategory} {bpC}
      (product_epis : products_preserves_Epis bpC)
      (F F' : functor B C) :
  preserves_Epi F -> preserves_Epi F' -> preserves_Epi (BinProduct_of_functors _ _ bpC F F').
Proof.
  intros epiF epiG M N f epif .
  cbn.
  apply product_epis; [apply epiF|apply epiG]; exact epif.
Qed.

Definition preserveEpi_binProdFuncSET {B  : precategory} 
      (F F' : functor B SET) :
  preserves_Epi F -> preserves_Epi F' -> preserves_Epi (BinProduct_of_functors _ _ _ F F') :=
  preserveEpi_binProdFunc productEpisSET F F'.

Lemma preserveEpi_sumFuncs {B C : precategory} {I : UU}(cp : Coproducts I C) 
      Fs (epiFs : ∏ i, preserves_Epi (Fs i)) :
    preserves_Epi (coproduct_of_functors  I B C cp Fs).
Proof.
    intros M N f epif.
    apply coproduct_Epis.
    intro i.
    apply epiFs.
    exact epif.
Qed.

Lemma preserveEpi_precomp {B : precategory} (C D : category) (F : functor B C)
      (pwEpi : epis_are_pointwise C D)
  :
  preserves_Epi (pre_composition_functor B C D (homset_property _)(homset_property _) F).
Proof.
  intros M N f epif.
  apply is_nat_trans_epi_from_pointwise_epis.
  intro X.
  use pwEpi.
  exact epif.
Qed.

(** The option functor preserves epis (same idea as coproduct_Epis *)
Lemma preserves_Epi_option {B : precategory} (bcp : BinCoproducts B) (T : Terminal B) :
      preserves_Epi (option_functor bcp T).
Proof.
  intros R S f epif.
  intros c u v eq.
  apply BinCoproductArrowsEq; [apply (identity_isEpi _ (x := T))| apply epif]; 
    do 2 rewrite assoc;
    [erewrite <- BinCoproductOfArrowsIn1|erewrite <- BinCoproductOfArrowsIn2];
    do 2 rewrite <- assoc;
    apply cancel_precomposition;
    exact eq.
Qed.
