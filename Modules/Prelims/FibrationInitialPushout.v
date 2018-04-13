(** Modularity in a fibration setting





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

Section pr.
  Context {C : category} (dC : disp_cat C).

  Definition disp_mor_to_total_mor {x y : C} {xx : dC x} {yy : dC y}
             {f : C ⟦ x, y ⟧}(ff : xx -->[f]  yy) : total_category dC ⟦ _ ,, xx, _ ,,yy ⟧
                                                                 := _ ,, ff.


  Local Notation TT := disp_mor_to_total_mor.

  Context   (cl : cleaving dC).

  Definition disp_InitialArrow {x y : C} {xx : dC x} {yy : dC y}
        (init : isInitial  (fiber_category _ _) xx)
        (f : C ⟦ x, y ⟧) := 
                                            transportf _ (id_left f)
                                            (iscontrpr1 (init _);; (cl _ _ f yy ))%mor_disp.


  Lemma disp_InitialArrowUnique {x y : C} {xx : dC x} {yy : dC y}
        (init : isInitial  (fiber_category _ _) xx)
        {f : C ⟦ x, y ⟧}(ff : xx -->[f] yy) : ff =
                                            disp_InitialArrow init f.
  Proof.
    revert ff.
    unfold disp_InitialArrow.
    destruct (id_left f).
    cbn.
    intro ff.
    unfold idfun.
    cbn.
    etrans; [eapply pathsinv0; use cartesian_factorisation_commutes; revgoals|].
    - set (gg := cl _ _ f yy).
      exact ( cartesian_lift_is_cartesian _ _ gg).
    - cbn.
      apply (maponpaths (fun x => (x;; _)%mor_disp)) .
      apply iscontr_uniqueness.
  Qed.
  (*
    revert ff ff'.
    rewrite <- (id_left f).
    intros ff ff'.
    set (gg := cl _ _ f yy).
    assert (hgg := cartesian_lift_is_cartesian _ _ gg).
    etrans; [| use cartesian_factorisation_commutes; [ | |  exact hgg]].
    assert (h : ff = (iscontrpr1 (init _) ;; gg)%mor_disp).
    set (z := cl _ _ f yy).
    etrans; [eapply pathsinv0; use cartesian_factorisation_commutes; [ | |  exact hgg]|].
    apply (maponpaths (fun x => (x;; gg)%mor_disp)) .
    apply proofirrelevancecontr.
    apply init.
  Qed.
*)

  Context

          {c0 c1 c2 c' : C}
          {f1 : C ⟦ c0, c1 ⟧}{f2 : C ⟦ c0, c2 ⟧}
          {g1 : C ⟦ c1, c' ⟧}{g2 : C ⟦ c2, c' ⟧}
          {heq : f1 · g1 = f2 · g2}
          (poC : isPushout f1 f2 g1 g2 heq).

  Let PO := mk_Pushout _ _ _ _ _ _ poC.

  Context {d0 :  dC c0} {d1 : dC c1} {d2 : dC c2} {d' : dC c'}.
  Context (ff1 : d0 -->[f1] d1)(ff2 : d0 -->[f2] d2)
          (gg1 : d1 -->[g1] d')(gg2 : d2 -->[g2] d').

  Context (init_d1 : isInitial  (fiber_category _ _) d1)
          (init_d2 : isInitial  (fiber_category _ _) d2)
          (init_d' : isInitial  (fiber_category _ _) d') .

             

  Context (eq_ff : TT ff1 · TT gg1 = TT ff2 · TT gg2).

  Lemma pushout_total : isPushout (TT ff1)(TT ff2)(TT gg1)(TT gg2) eq_ff.
  Proof.
    use mk_isPushout.
    intros [x xx] [h1 hh1] [h2 hh2] heq_hh.
    cbn in h1, hh1, h2, hh2.

    assert (eq2 := fiber_paths  heq_hh).
    set (eq1 := (base_paths _ _ heq_hh)) in eq2.

    cbn in eq1,eq2.
    use unique_exists.
    - use TT.
      + apply (PushoutArrow PO _ h1 h2).
        exact eq1.
        (* exact (base_paths _ _ heq_hh). *)
      + apply disp_InitialArrow.
        assumption.
    - cbn beta.
      split.
      + use total2_paths2_b.
        * apply (PushoutArrow_PushoutIn1 PO).
        * etrans; [apply (disp_InitialArrowUnique init_d1)|].
          apply pathsinv0.
          apply (disp_InitialArrowUnique init_d1).
      + use total2_paths2_b.
        * apply (PushoutArrow_PushoutIn2 PO).
        * etrans; [apply (disp_InitialArrowUnique init_d2)|].
          apply pathsinv0.
          apply (disp_InitialArrowUnique init_d2).
    - intros y.
      apply isapropdirprod; apply homset_property.
    - intros [k kk] [eqkk1 eqkk2].
      cbn in k,kk.
      use total2_paths2_b.
      + apply PushoutArrowUnique.
        * apply (base_paths _ _ eqkk1).
        * apply (base_paths _ _ eqkk2).
      +  etrans; [apply (disp_InitialArrowUnique init_d')|].
         apply pathsinv0.
         apply (disp_InitialArrowUnique init_d').
  Qed.

