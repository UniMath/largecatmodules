(**
TODO: update le eqdiag de UniMath

- Custom notion of equality between diagrams (eq_diag) over the same graph
- Transports of cones and cocones between equal diagrams.
- Limits/Colimits are the same for equal diagrams.

This notion of equality is useful to make the link between standard
diagrams (pushouts, coequalizers, ...) in a functor category and
the induced pointwise diagram given an object of the source category

Example of the binary product :

Let
- C,D be two categories,
- A and B two functors from C to D
- x an object of C

Let J := binproduct_diagram  (A x) (B x)
Let J' := diagram_pointwise (binproduct_diagram A B) x.

J and J' are not definitionnally equal.

Let co a cone of J based on c.

Using a (not too stupid) proof (e : eq_diag J J'), we can transport the cone co
with eq_diag_mkcone to get a cone co' of J' based on c that satisfies the
definitional equalities :
  coneOut co' true  ≡ coneOut co true
  coneOut co' false ≡ coneOut co false

(true and false are the two vertices of the binproduct graph).

This equality would not be needed if functional extensionality computed.

 *)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Open Scope cat.

(* TODO: upstream into definition of cone in UniMath. *)
Definition forms_cone
    {C : precategory} {g : graph} {d : diagram g C}
    {c : C} (f : ∏ (v : vertex g), C⟦c, dob d v⟧)
  : UU
  := ∏ (u v : vertex g) (e : edge u v),
     f u · dmor d e = f v.

Definition forms_cocone
    {C : precategory} {g : graph} {d : diagram g C}
    {c : C} (f : ∏ (v : vertex g), C⟦dob d v, c⟧)
  : UU
  := ∏ (u v : vertex g) (e : edge u v),
     dmor d e  · f v = f u.

Lemma is_exists_unique {A : UU} {B : A → UU} (H : ∃! a : A, B a) :
  B ( pr1 (iscontrpr1 H)).
Proof.
  exact(pr2 (pr1 H)).
Qed.


Lemma transport_swap: ∏ {X Y : UU} (P : X -> Y → UU) {x x':X} {y  y' : Y}
                        (e : x = x') (e' : y = y') (p : P x y),
                  transportf (λ a, P _ a) e' (transportf (λ a, P a _) e p) =
                  transportf (λ a, P a _) e (transportf (λ a, P _ a) e' p) .
Proof.
  intros.
  induction e.
  induction e'.
  apply idpath.
Qed.

Lemma transportf2_comp  {X  : UU} (P : X -> X → UU) (x x'  : X)
      (ex : x = x')  (t:P x x) :
  transportf (λ y, P y y) ex t = transportf (λ y, P y x') ex
                                             (transportf (λ y, P x y) ex t).
Proof.
  now induction ex.
Qed.

Definition eq_diag  {C : category} {g : graph} (d d' : diagram g C) :=
  ∑ (eq_v : ∏ v: vertex g, dob d v = dob d' v), ∏ (v v':vertex g) (f:edge v v'),
  transportf (λ obj, C⟦obj, dob d v'⟧)  (eq_v v) (dmor d f) =
  transportb (λ obj, C⟦_, obj⟧) (eq_v v') (dmor d' f).

Lemma eq_is_eq_diag {C : category} {g : graph} (d d' : diagram g C)  :
  d = d' -> eq_diag d d'.
Proof.
  intro e.
  induction e.
  exists (λ x, idpath _).
  exact (λ x y z, idpath _).
Qed.

Lemma eq_diag_is_eq {C : category} {g : graph} (d d' : diagram g C) :
  eq_diag d d' -> d = d'.
Proof.
  intros [eqv autreq].
  use total2_paths_f.
  - apply funextfun.
    intro v.
    apply eqv.
  - rewrite (transportf2_comp
               (λ x y : vertex g → C, ∏ a b : vertex g, edge a b →
                                                        C ⟦ y a, x b ⟧)).
    match goal with |- transportf ?Pf ?x1 (transportf ?Pf2 ?s1 ?s2 )  = _ =>
                    set (e := x1);
                      set (P := Pf);
                      set (P2 := Pf2);
                      set (tp2:=transportf P2 s1 s2);
                      set (trp := transportf P x1 tp2)
    end.
    change (trp = pr2 d').
    unfold trp.
    apply funextsec.
    intro v; apply funextsec; intro v'.
    apply funextsec; intro ed.
    specialize (autreq v v' ed).
    rewrite  <- (pathsinv0inv0 (eqv v)) in autreq.
    apply pathsinv0 in autreq.
    apply transportf_transpose in autreq.
    unfold dmor in autreq.
    rewrite autreq.
    rewrite pathsinv0inv0.
    etrans.
    eapply pathsinv0.
    apply (  transport_map (P:=P) (Q:=_) (λ x tp, tp  v v' ed)).
    etrans.
    apply (transportf_funextfun (λ x, C⟦ pr1 d' v,x⟧)).
    apply maponpaths.
    etrans.
    eapply pathsinv0.
    apply (  transport_map (P:=P2) (Q:=_) (λ x tp, tp  v v' ed)).
    apply (transportf_funextfun (λ x, C⟦ x,pr1 d v'⟧)).
Qed.

(* We don't want to use the equivalence with bare identity to show the
apply pathsinv0 because we want computation (Defined)
 *)
Lemma sym_eq_diag  {C : category} {g : graph} (d d' : diagram g C) :
  eq_diag d d' -> eq_diag d' d.
Proof.
  intros eq_d.
  set (eq_d1 := pr1 eq_d).
  set (eq_d2 := pr2 eq_d).
  use tpair.
  - intro v.
    apply (! (eq_d1 v)).
  - (* here we use equality *)
    unfold eq_d1.
    assert (heqdag:eq_diag d' d).
    + apply eq_is_eq_diag.
      apply pathsinv0.
      apply eq_diag_is_eq.
      assumption.
    +
(* Proof without using equality *)
    abstract (cbn;
    intros v v' f;
    specialize (eq_d2 v v' f);
    apply pathsinv0;
    unfold transportb;
    rewrite pathsinv0inv0;
    apply (transportf_transpose (P:=(λ obj : C, C ⟦ obj, dob d' v' ⟧)));
    assert (eq_d2':=transportf_transpose (P:=(precategory_morphisms (dob d' v)))
                                         _ _ _ (! eq_d2));
    rewrite eq_d2';
    unfold transportb; rewrite pathsinv0inv0;
    apply (transport_swap (λ a b, C⟦b,a⟧))).

Defined.

Definition eq_diag_cocone_data 
   {C : category} {g : graph} {d : diagram g C}
    {d' : diagram g C}
    (heq_d: eq_diag d d')
    {c : C} (cc:cocone d c):
  ∏ (v : vertex g), C ⟦ dob d' v, c ⟧ :=
  fun v =>
  transportf (λ obj : C, C ⟦ obj, c ⟧) (pr1 heq_d v) (coconeIn cc v).

Lemma eq_diag_form_cocones
   {C : category} {g : graph} {d : diagram g C}
    {d' : diagram g C}
    (heq_d: eq_diag d d')
    {c : C} (cc:cocone d c): forms_cocone (eq_diag_cocone_data heq_d cc).
Proof.
  intros u v e.
  unfold eq_diag_cocone_data.
  rewrite <- (coconeInCommutes cc u v e).
      apply (pathscomp0 (b:=transportb (precategory_morphisms (dob d' u)) (pr1 heq_d v)
                                       (dmor d' e) · (coconeIn cc v)));
      [
        unfold transportb; (set (z:= ! (pr1 heq_d) v));
        rewrite <- (pathsinv0inv0 (pr1 heq_d v));
        apply pathsinv0;
        apply transport_compose|];
      etrans; [
        apply cancel_postcomposition;
        eapply pathsinv0; apply (pr2 heq_d)|];
      clear;
      now destruct (pr1 heq_d u).
Qed.

Definition eq_diag_mkcocone 
    {C : category} {g : graph} {d : diagram g C}
    (d' : diagram g C)
    (heq_d: eq_diag d d')
    {c : C} (cc:cocone d c) :
  cocone d' c := mk_cocone _ (eq_diag_form_cocones heq_d cc).


(** The dual proof *)
Definition eq_diag_cone_data 
   {C : category} {g : graph} {d : diagram g C}
    {d' : diagram g C}
    (heq_d: eq_diag d d')
    {c : C} (cc:cone d c):
  ∏ (v : vertex g), C ⟦ c, dob d' v ⟧ :=
  fun v =>
  transportf (λ obj : C, C ⟦ c, obj ⟧) (pr1 heq_d v) (coneOut cc v).

Lemma eq_diag_form_cones
   {C : category} {g : graph} {d : diagram g C}
    {d' : diagram g C}
    (heq_d: eq_diag d d')
    {c : C} (cc:cone d c): forms_cone (eq_diag_cone_data heq_d cc).
Proof.
  set (heq := pr1 heq_d).
  set (heq2 := pr2 heq_d).
  unfold eq_diag_cone_data.
  intros u v e; simpl;
      rewrite <- ( coneOutCommutes cc u v e);
      etrans;[
        apply transport_compose|];
      rewrite transport_target_postcompose;
      apply cancel_precomposition;
      apply transportf_transpose;
      etrans;[
        apply (transport_swap (λ a b, C⟦a,b⟧))|];
      etrans;[
        apply maponpaths;
        eapply pathsinv0;
        apply heq2|];
      unfold heq;
      induction (pr1 heq_d u);
      apply idpath.
Qed.

Definition eq_diag_mkcone 
   {C : category} {g : graph} {d : diagram g C}
    (d' : diagram g C)
    (heq_d: eq_diag d d')
    {c : C} (cc:cone d c):
  cone d' c := mk_cone _ (eq_diag_form_cones heq_d cc).

Lemma eq_diag_islimcone:
  ∏ {C : category} {g : graph} {d : diagram g C}
    (d' : diagram g C)
    (eq_d : eq_diag d d')
    {c : C} {cc:cone d c}
    (islimcone : isLimCone _ _ cc) ,
  isLimCone _ _ (eq_diag_mkcone d' eq_d cc).
Proof.

  intros.
  set (eq_d1 := pr1 eq_d);
    set (eq_d2 := pr1 eq_d).
  set (eq_d' := sym_eq_diag _ _ eq_d).
  set (eq_d1' := pr1 eq_d').
  set (eq_d2' := pr2 eq_d').
    red.
  intros c' cc'.
  set (cc'2 := eq_diag_mkcone _ eq_d' cc').
  specialize (islimcone c' cc'2).
  apply (unique_exists (pr1 (pr1 islimcone))).
  - intro v.
    assert (islim := is_exists_unique islimcone v).
    cbn in islim.
    cbn.
    etrans.
    eapply pathsinv0.
    apply transport_target_postcompose.
    etrans.
    apply maponpaths.
    apply islim.
    apply transportfbinv.
  - intro y.
    apply impred_isaprop.
    intro t.
    apply homset_property.
  - intros y hy.
    apply (path_to_ctr _ _ islimcone).
    intro v; specialize (hy v).
    cbn.
    apply transportf_transpose.
    rewrite <- hy.
    etrans.
    unfold transportb.
    simpl.
    rewrite pathsinv0inv0.

    apply transport_target_postcompose.
    apply idpath.
Qed.

(** The dual proof .
This proof could be deduced from the previous if there was a lemma
stating that colimits are limits in the dual category.
 *)
Lemma eq_diag_iscolimcocone:
  ∏ {C : category} {g : graph} {d : diagram g C}
    (d' : diagram g C)
    (eq_d : eq_diag d d')
    {c : C} {cc:cocone d c}
    (islimcone : isColimCocone _ _ cc) ,
  isColimCocone _ _ (eq_diag_mkcocone d' eq_d cc).
Proof.
  intros.
  destruct eq_d as [eq_d1 eq_d2].
  set (eq_d := eq_d1,,eq_d2).
  set (eq_d'' := sym_eq_diag _ _ eq_d).
  set (eq_d1' := pr1 eq_d'').
  set (eq_d2' := pr2 eq_d'').
  set (eq_d'  := (eq_d1',,eq_d2'):eq_diag d' d).
  red.
  intros c' cc'.
  set (cc'2 := eq_diag_mkcocone _ eq_d' cc').
  specialize (islimcone c' cc'2).
  apply (unique_exists (pr1 (pr1 islimcone))).
  - intro v.
    assert (islim := is_exists_unique islimcone v).
    cbn in islim.
    cbn.
    unfold eq_diag_cocone_data.
    cbn.
    etrans.
    rewrite <- (pathsinv0inv0 (eq_d1 v)).
    eapply pathsinv0.
    apply transport_source_precompose.
    etrans.
    apply maponpaths.
    apply islim.
    cbn.
    now apply (transportbfinv ( (λ x' : C, C ⟦ x', c' ⟧) )).
  - intro y.
    apply impred_isaprop.
    intro t.
    apply homset_property.
  - intros y hy.
    apply (path_to_ctr _ _ islimcone).
    intro v; specialize (hy v).
    revert hy.
    cbn.
    intro hy.
    apply (transportf_transpose (P:=(λ obj : C, C ⟦ obj, c' ⟧))).
    etrans.
    apply transport_source_precompose.
    cbn.
    rewrite pathsinv0inv0.
    apply hy.
Qed.


Definition eq_diag_liftcolimcocone
           {C : category} {g : graph} {d : diagram g C}
           (d' : diagram g C)
           (eq_d : eq_diag d d')
           (cc:ColimCocone d ) : ColimCocone d'
  := mk_ColimCocone _ _ _ (eq_diag_iscolimcocone _ eq_d
                                                 (isColimCocone_ColimCocone cc)).

Definition eq_diag_liftlimcone
           {C : category} {g : graph} {d : diagram g C}
           (d' : diagram g C)
           (eq_d : eq_diag d d')
           (cc:LimCone d ) : LimCone d'
  := mk_LimCone _ _ _ (eq_diag_islimcone _ eq_d
                                         (isLimCone_LimCone cc)).