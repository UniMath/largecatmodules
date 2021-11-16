(**
Derivation of an over  signature
(copied from SignatureDerivation)
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

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
Require Import Modules.Signatures.ModelCat.
Require Import Modules.SoftEquations.SignatureOver.

Section DAr.

  Context {C : category}
          (bcpC : limits.bincoproducts.BinCoproducts C)
          (CT : limits.terminal.Terminal C).
Local Notation "∂" := (LModule_deriv_functor (TerminalObject CT) bcpC
                                             _).

Local Notation Signature := (signature C).
Local Notation MOD R := (category_LModule R C).

Context { Sig : signature C}.
Local Notation MODEL := (model Sig).
Local Notation MODEL_MOR := rep_fiber_mor.
Local Notation OSIG := (signature_over Sig).
Variable (a : OSIG).

  Definition signature_over_deriv_on_objects (R : MODEL)  : LModule R C :=
    ∂ (a R).

  Definition signature_over_deriv_on_morphisms (R S : MODEL)
             (f : MODEL_MOR R S) : LModule_Mor _ (signature_over_deriv_on_objects R)
                                               (pb_LModule f (signature_over_deriv_on_objects S)) :=
    (# ∂ (# a f)%sigo ) · (inv_from_iso (pb_LModule_deriv_iso _ bcpC  f _ )).

  Definition signature_over_deriv_data : signature_over_data Sig
    := signature_over_deriv_on_objects ,, signature_over_deriv_on_morphisms.

  Lemma signature_over_deriv_is_signature_over : is_signature_over _ signature_over_deriv_data.
  Proof.
    split.
    - intros R c.
      cbn -[LModule_deriv_functor identity].
      repeat rewrite id_right.
      etrans.
      {
        set (f := ((#a)%sigo _)).
        eapply (maponpaths  (fun (z : LModule_Mor _ _ _) => (# ∂ z : LModule_Mor _ _ _) c )(t1 := f)
                            (t2 := morphism_from_iso (pb_LModule_id_iso _) )
               ).
        apply LModule_Mor_equiv;[apply homset_property|].
        apply nat_trans_eq;[apply homset_property|].
        apply signature_over_id.
      }
      apply idpath.
    - intros R S T f g.
      etrans.
      {
      apply (cancel_postcomposition (C := MOD R)).
      rewrite signature_over_comp.
      apply functor_comp.
      }
      apply LModule_Mor_equiv;[apply homset_property|].
      apply nat_trans_eq;[apply homset_property|].
      intro x.
      cbn.
      repeat rewrite id_right.
      apply idpath.
  Qed.

  Definition signature_over_deriv : signature_over Sig := _ ,, signature_over_deriv_is_signature_over.

End DAr.

Fixpoint signature_over_deriv_n {C : category} (S : signature C) bcp T a (n :nat) : signature_over S :=
  match n with
    0 => a
  | S m => @signature_over_deriv C bcp T S (@signature_over_deriv_n C S bcp T a m)
  end.
