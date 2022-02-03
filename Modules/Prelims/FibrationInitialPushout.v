(** * Modularity in a fibration setting

The main result of this file is described here.

Let D be a fibration (ie, a cleaving in the displayed category setting)
over a category C.

 Suppose we have the following commuting diagram in the total category:

<<<
                  f1, ff1
       c0 , d0 ------------>  c1 , d1
          |                      |
          |                      |
f2 , ff2  |                      | g2 , gg2
          |                      |
          |                      |
          |                      |
          V                      V
       c2 , d2 ------------>  c' , d'
                 g1 , gg1
>>>

such that
- the restricting diagram in the category C is a pushout
- d1, d2, d' are initial in their respective fiber categories D[{c1}], D[{c2}], D[{d'}]
   (this implies that gg1 and gg2 are uniquely determined : see [disp_InitialArrowUnique])

Then the previous diagram is a pushout in the total category [pushout_total].
We also prove a simplified statment when d0 is initial [pushout_total_initial].


As an auxiliary lemma, we show [disp_InitialArrowUnique] that if xx is initial
in the fiber category over an object x of C, then there exists a unique displayed
morphism over any C-morphism f with codomain x.

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.initial.


Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Open Scope cat.

Section pr.
  Context {C : category} (dC : disp_cat C).

  Definition disp_mor_to_total_mor {x y : C} {xx : dC x} {yy : dC y}
             {f : C ⟦ x, y ⟧}(ff : xx -->[f]  yy) : total_category dC ⟦ _ ,, xx, _ ,,yy ⟧
                                                                 := _ ,, ff.


  Local Notation TT := disp_mor_to_total_mor.

  Context   (cl : cleaving dC).

  (**
Let xx be initial in the fiber category over x ∈ C.
If there is a morphism f : x → y  in C, then there is a unique morphism over f
*)
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
  

  Context
          {c0 c1 c2 c' : C}
          {f1 : C ⟦ c0, c1 ⟧}{f2 : C ⟦ c0, c2 ⟧}
          {g1 : C ⟦ c1, c' ⟧}{g2 : C ⟦ c2, c' ⟧}

          {d0 :  dC c0} {d1 : dC c1} {d2 : dC c2} {d' : dC c'}

          (init_d1 : isInitial  (fiber_category _ _) d1)
          (init_d2 : isInitial  (fiber_category _ _) d2)
          (init_d' : isInitial  (fiber_category _ _) d') .



  Lemma pushout_total
          (ff1 : d0 -->[f1] d1)(ff2 : d0 -->[f2] d2)
          (gg1 := disp_InitialArrow (yy := d') init_d1 g1)
          (gg2 := disp_InitialArrow init_d2 g2)
         (* Require commuting diagram in the total category *)
        {eq_ff : TT ff1 · TT gg1 = TT ff2 · TT gg2}
        (poC : isPushout f1 f2 g1 g2 (base_paths _ _ eq_ff))
     : isPushout  (TT ff1)(TT ff2)(TT gg1)(TT gg2) eq_ff.
  Proof.
    set (PO := make_Pushout _ _ _ _ _ _ poC).
    use make_isPushout.
    intros [x xx] [h1 hh1] [h2 hh2] heq_hh.
    cbn in h1, hh1, h2, hh2.
    use unique_exists.
    - use TT.
      + apply (PushoutArrow PO _ h1 h2).
        exact (base_paths _ _ heq_hh).
      + apply disp_InitialArrow.
        assumption.
    - split.
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

  (** If d0 is initial, then the requirements are fulfilled *)
  Context (init_d0 : isInitial  (fiber_category _ _) d0).
  Local Notation "##" := (disp_InitialArrow ).
  Let ff1 : d0 -->[f1] d1 :=  ## init_d0 f1.
  Let ff2 : d0 -->[f2] d2 :=  ## init_d0 f2.
  Let gg1 : d1 -->[g1] d' :=  ## init_d1 g1.
  Let gg2 : d2 -->[g2] d' :=  ## init_d2 g2.

  Context {heq :  f1 · g1 = f2 · g2}.

  Lemma initial_cl_lift_square_eq : TT ff1 · TT gg1 = TT ff2 · TT gg2.
  Proof.
    use total2_paths2_b.
    - exact heq.
    - etrans; [ apply (disp_InitialArrowUnique init_d0) | ].
      apply pathsinv0.
      apply (disp_InitialArrowUnique init_d0).
  Qed.

  Lemma pushout_total_initial
      (poC : isPushout f1 f2 g1 g2 heq)
     : isPushout (TT ff1)(TT ff2)(TT gg1)(TT gg2) initial_cl_lift_square_eq.
  Proof.
    apply pushout_total.
    exact poC.
  Qed.

End pr.

