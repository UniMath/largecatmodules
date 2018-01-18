(**
Derivation of a half arity (in order to build the arity Θ^(n) as we like it)
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
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.LModPbCommute.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Prelims.DerivationIsFunctorial.
Require Import Modules.Arities.aritiesalt.

Section DAr.

  Context {C : category}
          (bcpC : limits.bincoproducts.BinCoproducts C)
          (CT : limits.terminal.Terminal C).
Local Notation "∂" := (LModule_deriv_functor (TerminalObject CT) bcpC
                                             (homset_property _) _).

Local Notation HalfArity := (arity C).
Local Notation MOD R := (precategory_LModule R C).

Variable (a : arity C).

  Definition harity_deriv_on_objects (R : Monad C) : LModule R C :=
    ∂ (a R).

  Definition harity_deriv_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (harity_deriv_on_objects R)
                                               (pb_LModule f (harity_deriv_on_objects S)) :=
    (# ∂ (# a f)%ar ) · (inv_from_iso (pb_deriv_to_deriv_pb_iso _ bcpC  f _ )).

  Definition harity_deriv_data : @arity_data C
    := harity_deriv_on_objects ,, harity_deriv_on_morphisms.

  Lemma harity_deriv_is_arity : is_arity harity_deriv_data.
  Proof.
    split.
    - intros R c.
      cbn -[LModule_deriv_functor identity].
      repeat rewrite id_right.
      etrans.
      {
        set (f := ((#a)%ar _)).
        eapply (maponpaths  (fun (z : LModule_Mor _ _ _) => (# ∂ z : LModule_Mor _ _ _) c )(t1 := f)
                            (t2 := pbm_id)
               ).
        apply LModule_Mor_equiv;[apply homset_property|].
        apply nat_trans_eq;[apply homset_property|].
        apply arity_id.
      }
      apply idpath.
    - intros R S T f g.
      etrans.
      {
      apply (cancel_postcomposition (C := MOD R)).
      rewrite arity_comp.
      apply functor_comp.
      }
      apply LModule_Mor_equiv;[apply homset_property|].
      apply nat_trans_eq;[apply homset_property|].
      intro x.
      cbn.
      now repeat rewrite id_right.
  Qed.

  Definition harity_deriv : HalfArity := _ ,, harity_deriv_is_arity.

End DAr.

Fixpoint harity_deriv_n {C : category} bcp T a (n :nat) : arity C :=
  match n with
    0 => a
  | S m => @harity_deriv C bcp T (@harity_deriv_n C bcp T a m)
  end.
