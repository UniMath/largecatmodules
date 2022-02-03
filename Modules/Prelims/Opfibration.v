(** * Opfibrations

-largely copied and past from UniMath fibrations (but not all the UniMath file was readapted to the opfibration def)
- some complements that should be moved to Displayedcats.Core (Cf 2 lemmas at the beginning
of this file)
 *)

(** Definitions of various kinds of _fibraitions_, using displayed categories. *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.

Local Open Scope cat.
Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

(* COpied from Core *)
(** Note: closely analogous to [idtoiso_precompose].  We name it differently to fit the convention of naming equalities according to their LHS, for reference during calculation. *)
Lemma transportf_postcompose_disp {C} {D : disp_cat C}
    {c d : C} (f : d --> c )
    {cc cc' : D c} (e : cc' = cc) {dd} (ff : dd -->[f] cc')
  : transportf (λ xx : D c, dd -->[f] xx) e ff
  = transportf _ (id_right _)
    (ff ;; ( (idtoiso_disp (idpath _) e) )).
Proof.
  destruct e; cbn; unfold idfun; cbn.
  rewrite id_right_disp.
  apply pathsinv0, transportfbinv.
Qed.
Definition postcomp_with_iso_disp_is_inj
    {C : category} {D : disp_cat C}
    {a b c : C} {i : iso c a} {f : b --> c}
    {aa : D a} {bb} {cc} (ii : iso_disp i cc aa) {ff ff' : bb -->[f] cc}
  : ( ff ;; ii = ff' ;; ii) -> ff = ff'.
Proof.
  intros e.
  use pathscomp0.
  - use (transportf _ _ (ff ;; ( ii ;; iso_inv_from_iso_disp ii) )).
    etrans; [ apply cancel_precomposition, iso_inv_after_iso | apply id_right ].
  - apply pathsinv0.
    etrans. eapply transportf_bind.
      eapply cancel_precomposition_disp, (inv_mor_after_iso_disp ii).
    rewrite id_right_disp.
    etrans. apply transport_f_f.
    use (@maponpaths_2 _ _ _ _ _ (idpath _)).
    apply homset_property.
  - etrans. eapply transportf_bind, assoc_disp.
    rewrite e.
    etrans. eapply transportf_bind, assoc_disp_var.
    etrans. eapply transportf_bind.
      eapply cancel_precomposition_disp, (inv_mor_after_iso_disp ii).
    rewrite id_right_disp.
    etrans. apply transport_f_f.
    use (@maponpaths_2 _ _ _ _ _ (idpath _)).
    apply homset_property.
Qed.

(* copied from fibrations *)
(** * Opfibrations *)
Section Opfibrations.

Definition is_cocartesian {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : UU
:= forall c'' (g : c --> c'') (d'' : D c'') (hh : d' -->[f·g] d''),
  ∃! (gg : d -->[g] d''), ff ;; gg = hh.

(** See also [cocartesian_factorisation'] below, for when the map one wishes to factor is not judgementally over [g;;f], but over some equal map. *)
Definition cocartesian_factorisation {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cocartesian ff)
    {c''} (g : c --> c'') {d'' : D c''} (hh : d' -->[f·g] d'')
  : d -->[g] d''
:= pr1 (pr1 (H _ g _ hh)).

Definition cocartesian_factorisation_commutes
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cocartesian ff)
    {c''} (g : c --> c'') {d'' : D c''} (hh : d' -->[f·g] d'')
  : ff ;; cocartesian_factorisation H g hh = hh
:= pr2 (pr1 (H _ g _ hh)).

(** This is essentially the third access function for [is_cocartesian], but given in a more usable form than [pr2 (H …)] would be. *)
Definition cocartesian_factorisation_unique
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cocartesian ff)
    {c''} {g : c --> c''} {d'' : D c''} (gg gg' : d -->[g] d'')
  : (ff ;; gg = ff ;; gg') -> gg = gg'.
Proof.
  revert gg gg'.
  assert (goal' : forall gg : d -->[g] d'',
                    gg = cocartesian_factorisation H g (ff ;; gg)).
  {
    intros gg.
    exact (maponpaths pr1
      (pr2 (H _ g _ (ff ;; gg)) (gg,,idpath _))).
  }
  intros gg gg' Hggff.
  eapply pathscomp0. apply goal'.
  eapply pathscomp0. apply maponpaths, Hggff.
  apply pathsinv0, goal'.
Qed.

Definition cocartesian_factorisation' {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cocartesian ff)
    {c''} (g : c --> c'')
    {h : c' --> c''} {d'' : D c''} (hh : d' -->[h] d'')
    (e : (f · g = h))
  : d -->[g] d''.
Proof.
  use (cocartesian_factorisation H g).
  exact (transportb _ e hh).
Defined.

Definition cocartesian_factorisation_commutes'
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cocartesian ff)
    {c''} (g : c --> c'')
    {h : c' --> c''} {d'' : D c''} (hh : d' -->[h] d'')
    (e : (f · g = h))
  : ff ;; (cocartesian_factorisation' H g hh e)
  = transportb _ e hh.
Proof.
  apply cocartesian_factorisation_commutes.
Qed.

Definition cocartesian_lift {C : category} {D : disp_cat C}
    {c'} (d' : D c') {c : C} (f : c' --> c)
  : UU
:= ∑ (d : D c) (ff : d' -->[f] d), is_cocartesian ff.

Definition object_of_cocartesian_lift  {C : category} {D : disp_cat C}
    {c'} (d' : D c') {c : C} (f : c' --> c)
    (fd : cocartesian_lift d' f)
  : D c
:= pr1 fd.
Coercion object_of_cocartesian_lift : cocartesian_lift >-> ob_disp.

Definition mor_disp_of_cocartesian_lift  {C : category} {D : disp_cat C}
    {c'} (d' : D c') {c : C} (f : c' --> c)
    (fd : cocartesian_lift d' f)
  : d'  -->[f] (fd : D c)
:= pr1 (pr2 fd).
Coercion mor_disp_of_cocartesian_lift : cocartesian_lift >-> mor_disp.

Definition cocartesian_lift_is_cocartesian {C : category} {D : disp_cat C}
    {c'} (d' : D c') {c : C} (f : c' --> c)
    (fd : cocartesian_lift d' f)
  : is_cocartesian fd
:= pr2 (pr2 fd).
Coercion cocartesian_lift_is_cocartesian : cocartesian_lift >-> is_cocartesian.

Definition is_cocartesian_disp_functor
  {C C' : category} {F : functor C C'}
  {D : disp_cat C} {D' : disp_cat C'} (FF : disp_functor F D D') : UU
:= ∏  (c c' : C) (f : c' --> c)
      (d : D c) (d' : D c') (ff : d' -->[f] d),
   is_cocartesian ff -> is_cocartesian (#FF ff).

Lemma isaprop_is_cocartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : isaprop (is_cocartesian ff).
Proof.
  repeat (apply impred_isaprop; intro).
  apply isapropiscontr.
Defined.

(* TODO: should the arguments be re-ordered as in [cocartesian_lift]? If so, reorder in [isoopfibration] etc as well, for consistency. *)
(* TODO: consider renaming to e.g. [cleaving] to follow convention that [is_] is reserved for hprops. *)
Definition opcleaving {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (f : c' --> c) (d' : D c'), cocartesian_lift d' f.

(** ** (Cloven) opfibration *)

Definition opfibration (C : category) : UU
:=
  ∑ D : disp_cat C, cleaving D.


(** ** Weak opfibration *)

(* TODO: give access functions! *)

Definition is_opcleaving {C : category} (D : disp_cat C) : UU
:=
  forall (c c' : C) (f : c' --> c) (d' : D c'), ∥ cocartesian_lift d' f ∥.

Definition weak_opfibration (C : category) : UU
:= ∑ D : disp_cat C, is_opcleaving D.

(*
(** ** Connection with isoopfibrations *)

Lemma is_iso_from_is_cocartesian {C : category} {D : disp_cat C}
    {c c' : C} (i : iso c' c) {d : D c} {d'} (ff : d' -->[i] d)
  : is_cocartesian ff -> is_iso_disp i ff.
Proof.
  intros Hff.
  use (_,,_); try split.
  - use
      (cocartesian_factorisation' Hff (inv_from_iso i) (id_disp _)).
    apply iso_after_iso_inv.
  - apply cocartesian_factorisation_commutes'.
  - apply (cocartesian_factorisation_unique Hff).
    etrans. apply assoc_disp_var.
    rewrite cocartesian_factorisation_commutes'.
    etrans. eapply transportf_bind.
      etrans. apply mor_disp_transportf_prewhisker.
      eapply transportf_bind, id_right_disp.
    apply pathsinv0.
    etrans. apply mor_disp_transportf_postwhisker.
    etrans. eapply transportf_bind, id_left_disp.
    apply maponpaths_2, homset_property.
Qed.

Lemma is_isoopfibration_from_is_opfibration {C : category} {D : disp_cat C}
  : cleaving D -> iso_cleaving D.
Proof.
  intros D_fib c c' f d.
  assert (fd := D_fib _ _ f d).
  exists (fd : D _).
  exists (fd : _ -->[_] _).
  apply is_iso_from_is_cocartesian; exact fd.
Defined.
*)

(** ** Uniqueness of cocartesian lifts *)

Lemma transportf_bind {X : UU} {P : X → UU}
  {x x' x'' : X} (e : x' = x) (e' : x = x'')
  y y'
: y = transportf P e y' -> transportf _ e' y = transportf _ (e @ e') y'.
Proof.
  intro H; destruct e, e'; exact H.
Defined.
(* TODO: show that when [D] is _univalent_, cocartesian lifts are literally unique, and so any uncloven opfibration (isoopfibration, etc) is in fact cloven. *)
Definition cocartesian_lifts_iso {C : category} {D : disp_cat C}
    {c'} {d' : D c'} {c : C} {f : c' --> c} (fd fd' : cocartesian_lift d' f)
  : iso_disp (identity_iso c) fd fd'.
Proof.
  use (_,,(_,,_)).
  - exact (cocartesian_factorisation' fd (identity _) fd' (id_right _)).
  - exact (cocartesian_factorisation' fd' (identity _) fd (id_right _)).
  - cbn; split.
    + apply (cocartesian_factorisation_unique fd').
      etrans. apply assoc_disp.
      rewrite cocartesian_factorisation_commutes'.
      etrans. eapply transportf_bind,  mor_disp_transportf_postwhisker.
      rewrite cocartesian_factorisation_commutes'.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_prewhisker.
      rewrite id_right_disp.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
    + apply (cocartesian_factorisation_unique fd).
      etrans. apply assoc_disp.
      rewrite cocartesian_factorisation_commutes'.
      etrans. eapply transportf_bind, mor_disp_transportf_postwhisker.
      rewrite cocartesian_factorisation_commutes'.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_prewhisker.
      rewrite id_right_disp.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
Defined.

Definition cocartesian_lifts_iso_commutes {C : category} {D : disp_cat C}
    {c'} {d' : D c'} {c : C} {f : c' --> c} (fd fd' : cocartesian_lift d' f)
  : fd ;; (cocartesian_lifts_iso fd fd') 
  = transportb _ (id_right _) (fd' : _ -->[_] _).
Proof.
  cbn. apply cocartesian_factorisation_commutes'.
Qed.


(** In a displayed _category_ (i.e. _univalent_), cocartesian lifts are literally unique, if they exist; that is, the type of cocartesian lifts is always a proposition. *)
Definition isaprop_cocartesian_lifts
    {C : category} {D : disp_cat C} (D_cat : is_univalent_disp D)
    {c'} (d' : D c') {c : C} (f : c' --> c)
  : isaprop (cocartesian_lift d' f).
Proof.
  apply invproofirrelevance; intros fd fd'.
  use total2_paths_f.
  { apply (isotoid_disp D_cat (idpath _)); cbn.
    apply cocartesian_lifts_iso. }
  apply subtypePath.
  { intros ff. repeat (apply impred; intro).
    apply isapropiscontr. }
  etrans.
    use ( ! (@transport_map (D c) _ _ (λ x, pr1) _ _ _ _ )).
  cbn. etrans. apply transportf_postcompose_disp.
  rewrite idtoiso_isotoid_disp.
  use (pathscomp0 (maponpaths _ _) (transportfbinv _ _ _)).
  apply (postcomp_with_iso_disp_is_inj (iso_inv_from_iso_disp (cocartesian_lifts_iso fd fd'))).
  etrans. apply assoc_disp_var.
  etrans. eapply transportf_bind, cancel_precomposition_disp.
    use (inv_mor_after_iso_disp (pr2 (cocartesian_lifts_iso fd fd')))  .
  etrans. eapply transportf_bind, id_right_disp.
  apply pathsinv0.
  etrans. apply mor_disp_transportf_postwhisker.
  etrans. eapply transportf_bind, cocartesian_lifts_iso_commutes.
  apply maponpaths_2, homset_property.
Defined.

Definition univalent_opfibration_is_cloven
    {C : category} {D : disp_cat C} (D_cat : is_univalent_disp D)
  : is_opcleaving D -> opcleaving D.
Proof.
  intros D_fib c c' f d.
  apply (squash_to_prop (D_fib c c' f d)).
  apply isaprop_cocartesian_lifts; assumption.
  auto.
Defined.

End Opfibrations.





(** Copied from Fibration in UniMath *)
Section Discrete_OpFibrations.

Definition is_discrete_opfibration {C : category} (D : disp_cat C) : UU
:=
  (forall (c c' : C) (f : c' --> c) (d' : D c'),
          ∃! d : D c, d' -->[f] d)
  ×
  (forall c, isaset (D c)).

Definition discrete_opfibration C : UU
  := ∑ D : disp_cat C, is_discrete_opfibration D.

Coercion disp_cat_from_discrete_opfibration C (D : discrete_opfibration C)
  : disp_cat C := pr1 D.
Definition unique_lift_op {C} {D : discrete_opfibration C} {c c'}
           (f : c' --> c) (d' : D c')
  : ∃! d : D c, d' -->[f] d
  := pr1 (pr2 D) c c' f d'.

Definition isaset_fiber_discrete_opfibration {C} (D : discrete_opfibration C)
           (c : C) : isaset (D c) := pr2 (pr2 D) c.


Lemma disp_mor_unique_disc_opfib C (D : discrete_opfibration C)
  : ∏ (c c' : C) (f : c --> c') (d : D c) (d' : D c')
      (ff ff' : d -->[f] d'), ff = ff'.
Proof.
  intros.
  assert (XR := unique_lift_op f d).
  assert (foo : ((d',,ff) : ∑ d0, d -->[f] d0) = (d',,ff')).
  { apply proofirrelevance.
    apply isapropifcontr. apply XR.
  }
  apply (pair_inj (isaset_fiber_discrete_opfibration _ _ ) foo).
Defined.

Lemma isaprop_disc_opfib_hom C (D : discrete_opfibration C)
  : ∏ (c c' : C) (f : c --> c') (d : D c) (d' : D c'),
    isaprop (d -->[f] d').
Proof.
  intros.
  apply invproofirrelevance.
  intros x x'. apply disp_mor_unique_disc_opfib.
Qed.


Definition opfibration_from_discrete_opfibration C (D : discrete_opfibration C)
  : opcleaving D.
Proof.
  intros c c' f d.
  use tpair.
  - exact (pr1 (iscontrpr1 (unique_lift_op f d))).
  - use tpair.
    + exact (pr2 (iscontrpr1 (unique_lift_op f d))).
    + intros c'' g db hh.
      set (ff := pr2 (iscontrpr1 (unique_lift_op f d))  ). cbn in ff.
      set (d' := pr1 (iscontrpr1 (unique_lift_op f d))) in *.
      set (ggff := pr2 (iscontrpr1 (unique_lift_op (f·g) d))  ). cbn in ggff.
      set (d'' := pr1 (iscontrpr1 (unique_lift_op (f·g) d))) in *.
      set (gg := pr2 (iscontrpr1 (unique_lift_op g d'))). cbn in gg.
      set (d3 := pr1 (iscontrpr1 (unique_lift_op g d'))) in *.
      assert (XR : ((d'',, ggff) : ∑ r, d -->[f·g] r) = (db,,hh)).
      { apply proofirrelevance. apply isapropifcontr. apply (pr2 D). }
      assert (XR1 : ((d'',, ggff) : ∑ r, d -->[f·g] r) = (d3 ,,ff;;gg)).
      { apply proofirrelevance. apply isapropifcontr. apply (pr2 D). }
      assert (XT := maponpaths pr1 XR). cbn in XT.
      assert (XT1 := maponpaths pr1 XR1). cbn in XT1.
      generalize XR.
      generalize XR1; clear XR1.
      destruct XT.
      generalize gg; clear gg.
      destruct XT1.
      intros gg XR1 XR0.
      apply iscontraprop1.
      * apply invproofirrelevance.
        intros x x'. apply subtypePath.
        { intro. apply homsets_disp. }
        apply disp_mor_unique_disc_opfib.
      * exists gg.
        cbn.
        assert (XX := pair_inj (isaset_fiber_discrete_opfibration _ _ ) XR1).
        assert (YY := pair_inj (isaset_fiber_discrete_opfibration _ _ ) XR0).
        etrans. apply (!XX). apply YY.
Defined.

End Discrete_OpFibrations.


(** * Split fibrations *)

Definition opcleaving_ob {C : category} {D : disp_cat C}
           (X : opcleaving D) {c c' : C} (f : c' --> c) (d : D c')
  : D c := X _ _ f d.

Definition opcleaving_mor {C : category} {D : disp_cat C}
           (X : opcleaving D) {c c' : C} (f : c' --> c) (d' : D c')
  : d' -->[f] opcleaving_ob X f d' := X _ _ f d'.

