(** * Modularity in a fibration setting

The main result of this file is described here.

Let D be a fibration (ie, a cleaving in the displayed category setting)
over a category C such that the projection functor is faithful.

Then the projection functor creates equalizers.

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.initial.


Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.equalizers.

Require Import Modules.Prelims.eqdiag.


(** All the stuff equalizer.v work only for a diagram built out of Equalizer_diagram

TODO: move to equalizer.v
 *)
Definition equalizer_diagram_to_canonical {C} (F : diagram Equalizer_graph C) : diagram Equalizer_graph C :=
  Equalizer_diagram C
                    (dmor (a := One) (b := Two) F (inl tt))
                    (dmor (a := One) (b := Two)F (inr tt)).

Lemma canonical_equalizer_diagram_eq {C : category}(F : diagram Equalizer_graph C)
  : eq_diag F (equalizer_diagram_to_canonical F).
Proof.
    intros.
    use tpair.
    use StandardFiniteSets.two_rec_dep; apply idpath.
    use StandardFiniteSets.two_rec_dep;  use StandardFiniteSets.two_rec_dep;
      try exact (empty_rect _ );
    use coprod_rect;
    use unit_rect;
    exact (idpath _).
Defined.

Lemma map_Equalizer_diagram {C: category} {D : category}
      {a b} (f g : C⟦a, b⟧) (F : functor C D) :
  eq_diag (mapdiagram F (Equalizer_diagram _ f g) ) (Equalizer_diagram _ (#F f)(#F g) ).
Proof.
    use tpair.
    use StandardFiniteSets.two_rec_dep; apply idpath.
    use StandardFiniteSets.two_rec_dep;  use StandardFiniteSets.two_rec_dep;
      try exact (empty_rect _ );
    use coprod_rect;
    use unit_rect;
    exact (idpath _).
Defined.

(** I don't know to which extent the previous lemmas are useful (the idea would be to lift cones using eq_diag). *)

Section pr.
  Context {C : category} (D : disp_cat C).

  (** missing definition in DisplayedCategorie.Limits ?
      this is like creates_limits but parametrized by the graph
   *)
  Definition creates_a_limit   (J : graph) : UU
    :=
      ∏  (F : diagram J (total_category D))
        {x : C} (L : cone (mapdiagram (pr1_category D) F)  x)
        (isL : isLimCone _ x L),
      creates_limit _ _ _ isL.


  (** This is a fibration *)
  Context   (cl : cleaving D).
  (** The fibration is faithful
This can be reformulated as [faithful pr1_category) as in [faithful_pr1_category]
   *)
  Hypothesis (faithful_fibration : faithful (pr1_category D)).
  (** Yet another formulation *)
  Lemma faithful_reformulated {x y} (f g : total_category D ⟦ x, y ⟧) : pr1 f = pr1 g -> f = g.
  Proof.
    eapply invmaponpathsincl.
    eapply faithful_fibration.
  Qed.

  Lemma faithful_fibration_equalizer {a b} (f g : total_category D⟦a, b⟧)
        (F :=  Equalizer_diagram _ f g )
         :
    ∏ (x : C) (L : cone (mapdiagram (pr1_category D) F) x) (isL : isLimCone (mapdiagram (pr1_category D) F) x L),
    creates_limit D F L isL.
  Proof.
    assert (e := map_Equalizer_diagram f g (pr1_category D)).
    set (F' := mapdiagram _ _).
    set (e' := eq_diag_is_eq F' _ e).
    intros x L isL.
    red.
    set (equalizer := eq_diag_liftlimcone _ e (mk_LimCone  _ _ _ isL)).
    use tpair.
    - use unique_exists.
      + eapply (cleaving_ob cl ).
        * exact (EqualizerArrow _ equalizer).
        * cbn.
          apply pr2.
      + cbn beta.
        * use tpair.
  Admitted.
  (*
          shelve.
          {
            cbn beta.
            admit.


          -- use StandardFiniteSets.two_rec_dep; simpl.
  Admitted.
*)


  Lemma faithful_fibration_creates_equalizers : creates_a_limit Equalizer_graph.
  Proof.
    intro F.
    (* this won't compute properly I think, but using equality makes things easier *)
    rewrite (eq_diag_is_eq _ _ (canonical_equalizer_diagram_eq F)).
    apply faithful_fibration_equalizer.
  Qed.

End pr.

