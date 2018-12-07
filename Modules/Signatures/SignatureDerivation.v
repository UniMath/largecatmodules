(**
Derivation of a  signature (in order to build the signature Θ^(n) as we like it)
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Monads.Derivative.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesCoproducts.
Require Import Modules.Prelims.DerivationIsFunctorial.
Require Import Modules.Signatures.Signature.

Section DAr.

  Context {C : category}
          (bcpC : limits.bincoproducts.BinCoproducts C)
          (CT : limits.terminal.Terminal C).
Local Notation "∂" := (LModule_deriv_functor (TerminalObject CT) bcpC
                                             (homset_property _) _).

Local Notation Signature := (signature C).
Local Notation MOD R := (precategory_LModule R C).

Variable (a : signature C).

  Definition signature_deriv_on_objects (R : Monad C) : LModule R C :=
    ∂ (a R).

  Definition signature_deriv_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (signature_deriv_on_objects R)
                                               (pb_LModule f (signature_deriv_on_objects S)) :=
    (# ∂ (# a f)%ar ) · (inv_from_iso (pb_LModule_deriv_iso _ bcpC  f _ )).

  Definition signature_deriv_data : @signature_data C
    := signature_deriv_on_objects ,, signature_deriv_on_morphisms.

  Lemma signature_deriv_is_signature : is_signature signature_deriv_data.
  Proof.
    split.
    - intros R c.
      cbn -[LModule_deriv_functor identity].
      repeat rewrite id_right.
      etrans.
      {
        set (f := ((#a)%ar _)).
        eapply (maponpaths  (fun (z : LModule_Mor _ _ _) => (# ∂ z : LModule_Mor _ _ _) c )(t1 := f)
                            (t2 := morphism_from_iso _ _ _ (pb_LModule_id_iso _ ))
               ).
        apply LModule_Mor_equiv;[apply homset_property|].
        apply nat_trans_eq;[apply homset_property|].
        apply signature_id.
      }
      apply idpath.
    - intros R S T f g.
      etrans.
      {
      apply (cancel_postcomposition (C := MOD R)).
      rewrite signature_comp.
      apply functor_comp.
      }
      apply LModule_Mor_equiv;[apply homset_property|].
      apply nat_trans_eq;[apply homset_property|].
      intro x.
      cbn.
      repeat rewrite id_right.
      apply idpath.
  Qed.

  Definition signature_deriv : Signature := _ ,, signature_deriv_is_signature.

  Lemma signature_to_deriv_laws : is_signature_Mor a signature_deriv
                                                        (fun R => LModule_to_deriv CT bcpC (homset_property _) R (a R)).
  Proof.
    intros R S f.
    apply (nat_trans_eq (homset_property _)).
    intro c.
    cbn.
    repeat rewrite id_left.
    rewrite id_right.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition signature_to_deriv : signature_Mor a signature_deriv := _ ,, signature_to_deriv_laws.

End DAr.

Fixpoint signature_deriv_n {C : category} bcp T a (n :nat) : signature C :=
  match n with
    0 => a
  | S m => @signature_deriv C bcp T (@signature_deriv_n C bcp T a m)
  end.
