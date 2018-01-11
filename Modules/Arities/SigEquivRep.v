(**
Let Σ = (O,α) and Σ' = (O,α') be two signatures with the same base.
if foreach o there is an isomorphism of category Rep (α o) ≃ Rep (α' o) that
preserves the underlying monad, then there is isomorphism of category
Rep Σ ≃ Rep Σ' (preserving the underlying monad)
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.

Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.FullArities.
Require Import Modules.Arities.Signatures.
Require Import UniMath.CategoryTheory.catiso.


Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Open Scope cat.

Section SigEquiv.


  Context {C : category}.
  Context {O : UU} (α α' : O -> FullArity C).
  Context (Fmod : ∏ (o : O) R,
                 LModule_Mor R (dom (α o) R)(codom (α o) R) ≃
                             LModule_Mor R (dom (α' o) R)(codom (α' o) R)).
  Let a_rep a := (rep_disp C)[{a}].

  Let Fob {o} (R : a_rep (α o)) : a_rep (α' o) :=
     (pr1 R) ,, (Fmod o _ (pr2 R)).

  (* Context (Fmor : ∏ o (R S : a_rep (α o)), a_rep (α o) ⟦R , S ⟧ ≃ a_rep (α' o) ⟦ Fob R, Fob S⟧). *)
  Context (Fmor_law : ∏ o (R S : rep_ar _ (α o)) (f : Monad_Mor R S),
                      rep_ar_mor_law _ R S (identity _) f ≃
                                     rep_ar_mor_law _ (Fob R) (Fob S) (identity _) f
                      ).
  Let  Fmor o (R S : a_rep (α o)) : a_rep (α o) ⟦R , S ⟧ ≃ a_rep (α' o) ⟦ Fob R, Fob S⟧.
    apply weqfibtototal.
    apply Fmor_law.
  Defined.
  Context (F_is_functor : ∏ o, is_functor (functor_data_constr _ _ (@Fob o) (Fmor o))).

  Let sig_rep S := precategory_rep_sig (C := C) S.
  Let F o : functor (a_rep (α o)) (a_rep (α' o)) := _ ,, F_is_functor o.

  Let Σ : signature C := _ ,, α.
  Let Σ' : signature C := _ ,, α'.

  (* inspiré de rawsigtohar *)
  Definition sig_to_sig_rep_weq : sig_rep Σ ≃ sig_rep Σ'. 
  Proof.
    apply weqfibtototal.
    intro R.
    apply weqonsecfibers.
    intro o.
    apply Fmod.
  Defined.

  Local Notation FSob := sig_to_sig_rep_weq.

  Definition sig_to_sig_rep_on_mor_weq (R S : sig_rep Σ) :
    sig_rep Σ ⟦ R , S ⟧ ≃ sig_rep Σ' ⟦ FSob R , FSob S ⟧.
  Proof.
    apply weqfibtototal.
    intro f.
    apply weqonsecfibers.
    intro o.
    apply Fmor_law.
  Defined.
  Local Notation FSmor := sig_to_sig_rep_on_mor_weq.

  Definition sig_to_sig_rep_functor_data : functor_data (sig_rep Σ) (sig_rep Σ') :=
    functor_data_constr _ _  FSob  FSmor.

  Lemma sig_to_sig_rep_is_functor : is_functor sig_to_sig_rep_functor_data.
  Proof.
    split.
    - intro R.
      now apply rep_sig_mor_mor_equiv.
    - intros R S T f g.
      now apply rep_sig_mor_mor_equiv.
  Defined.

  Definition sig_to_sig_rep_functor : functor (sig_rep Σ) (sig_rep Σ') :=
    _ ,, sig_to_sig_rep_is_functor.
  Local Notation FS := sig_to_sig_rep_functor.

  Definition iso_sig_sig_rep : catiso (sig_rep Σ) (sig_rep Σ')
    := FS,, (λ x y : sig_rep Σ, weqproperty (FSmor x y)),, weqproperty FSob.
End SigEquiv.

