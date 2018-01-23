(**
Tautological half arity

A raw signature is a signature consisting of raw arities (ie the codomain is the tautological
module).

In other words, a raw signature is just a family of half arities

In this file, we show that the category of representation of a raw signature
is isomorphic to the category of representation of the coproduct of all the half-arities

- def of Tautological half arity
- def of raw signature
- half arity to arity
- Raw signature to signature
- Raw signature to half arity
- Isomorphisms between the two categories of representations.
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.coproducts.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Arities.HArityCoproduct.
Require Import Modules.Arities.Signatures.
Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.HssToArity.
Require  Modules.Arities.FullArities.
Module FAr := FullArities.

Section Raw.

Context {C : category} .


Local Notation hsC := (homset_property C).


Local Notation HalfArity := (arity C).
Local Notation FullArity := (FAr.FullArity C).
Local Notation MOD R := (category_LModule R C).

Local Notation Θ := tautological_LModule.


Definition half_arity_to_arity (a : HalfArity) : FullArity :=
  a ,, tautological_harity.

Local Notation toAr := half_arity_to_arity.

(** The representations are strictly the same *)
Check ((fun a => idpath _):  ∏ a, (rep_ar C a) = (FAr.rep_ar C (toAr a))).

(* TODO vérifier que c'es tutile *)
(* Let a_sig_rep := precategory_rep_sig a_sig. *)
(* Let a_har_rep := (rep_disp C)[{a_har}]. *)



(* useless *)
Lemma half_arity_to_arity_is_rep_weq (a : HalfArity) (M N : rep_ar C a) f : 
  FAr.rep_ar_mor_law C (a := toAr a) (b:=toAr a) M N (identity _) f
                     ≃
  rep_ar_mor_law C (a :=  a) (b:= a) M N (identity (C := arity_category) _) f.
Proof.
  apply weqiff.
  split.
  - intros  h x.
    etrans; [apply h|].
    apply id_right.
  - intros h x.
    etrans; [apply h|].
    cbn.
    apply pathsinv0.
    apply id_right.
  - apply FAr.isaprop_rep_ar_mor_law.
  - apply isaprop_rep_ar_mor_law.
Defined.

Definition rawSig := ∑ (O : UU), O -> HalfArity.

Definition base_of_rawSig (a : rawSig) : UU := pr1 a.
Definition ar_of_rawSig (a : rawSig) : base_of_rawSig a -> HalfArity := pr2 a.

(* Local Notation O := base_of_rawSig. *)
(* Local Notation α := ar_of_rawSig. *)

Definition rawSigToSig (a : rawSig) : signature C :=
  tpair  (fun z => z -> FullArity)
  (base_of_rawSig a)  (fun (o : base_of_rawSig a) => half_arity_to_arity (ar_of_rawSig a o)).

Local Notation TOSIG := rawSigToSig.

Context {O : UU}.
Context (cpC : Coproducts O C).
Let cpHA  := harity_Coproducts cpC.
Let cpLM (R : Monad C) := LModule_Coproducts C R cpC.

Definition rawSigToHAr (a : O -> HalfArity) : HalfArity :=
  CoproductObject _ _ (cpHA a).

Variable (a : O -> HalfArity).
Let aS : rawSig := _ ,, a.

Let a_sig := rawSigToSig aS.
Let a_har := rawSigToHAr a.

Let a_sig_rep := precategory_rep_sig a_sig.
Let a_har_rep := (rep_disp C)[{a_har}].

Definition sig_to_har_rep_weq : a_sig_rep ≃ a_har_rep.
Proof.
  apply weqfibtototal.
  intro R.
  cbn.
  apply (from_Coproducts_weq (C := MOD R) (cpLM R)).
Defined.

Local Notation Fob := sig_to_har_rep_weq.

Definition sig_to_har_rep_on_mor_weq (R S : a_sig_rep) : a_sig_rep ⟦ R , S ⟧ ≃ a_har_rep ⟦ Fob R , Fob S ⟧.
  apply weq_subtypes_iff.
  - intro x.
    apply impred_isaprop.
    intros ?.
    apply FAr.isaprop_rep_ar_mor_law.
  - intros ?.
    apply isaprop_rep_ar_mor_law.
  - intro f.
    split.
    + intro  h .
      intro x.
      
      cbn.
      unfold coproduct_nat_trans_data.
      repeat rewrite id_right.
      etrans;[apply postcompWithCoproductArrow|].
      apply pathsinv0.
      etrans;[apply postcompWithCoproductArrow|].
      apply maponpaths.
      apply funextsec.
      intro i.
      cbn.




      unfold coproduct_nat_trans_in_data.
      specialize (h i x).
      cbn in h.
      etrans.
      {
        rewrite <- assoc.
        apply maponpaths.
        set (CC := cpC _).
        apply (CoproductInCommutes _ _ _ CC).
      }
      repeat rewrite id_right in h.
      exact (!h).
    + intro h.
      intros o x.
      specialize (h x).
      cbn.
      cbn in h.
      unfold coproduct_nat_trans_data in h.
      repeat rewrite id_right in h.
      repeat rewrite id_right.
      cbn in o.
      set (CC := cpC _) in h.
      assert (h' := maponpaths (compose (CoproductIn _ _ CC o )) h).
      rewrite assoc in h'.
      rewrite (CoproductInCommutes _ _ _ CC) in h'.
      cbn in h'.
      unfold rep_sig_τ.
      etrans; [exact h'|].
      rewrite assoc.
      rewrite (CoproductInCommutes _ _ _ CC).
      rewrite <- assoc.
      apply maponpaths.
      set (CC' := cpC _).
      apply (CoproductInCommutes _ _ _ CC').
Defined.

Local Notation Fmor := sig_to_har_rep_on_mor_weq.


Definition sig_to_har_rep_functor_data : functor_data a_sig_rep a_har_rep :=
  functor_data_constr _ _  Fob  Fmor.

Lemma sig_to_har_rep_is_functor : is_functor sig_to_har_rep_functor_data.
Proof.
  split.
  - intro R.
    apply rep_ar_mor_mor_equiv.
    intro; apply idpath.
  - intros R S T f g.
    apply rep_ar_mor_mor_equiv.
    intro c.
    cbn.
    apply pathsinv0.
    etrans.
    set (e := id_right _).
    assert (h := (transport_arity_mor _ _ _ _ _ e)).
    match goal with
      |- context zdf [transportf (mor_disp ?xx ?yy) e ] => set (xx' := xx); set (yy' := yy)
    end.
    etrans;[|eapply (h xx'  yy' _ c)].
    apply idpath.
    cbn.
    apply idpath.
Qed.

Definition sig_to_har_rep_functor : functor a_sig_rep a_har_rep := _ ,, sig_to_har_rep_is_functor.
Local Notation F := sig_to_har_rep_functor.

Definition iso_a_sig_har_rep : catiso a_sig_rep a_har_rep
   := F,, (λ x y : a_sig_rep, weqproperty (Fmor x y)),, weqproperty Fob.


End Raw.
