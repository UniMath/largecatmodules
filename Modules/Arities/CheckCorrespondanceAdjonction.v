
(* Let (a, Θ^(n)) be an arity
Then the category of representation is isomorphic to
(a × Θ^n, 1) in the sense required by SigEquivRep
 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.

Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.FullArities.
Require Import Modules.Arities.HssToArity.
Require Import Modules.Arities.HArityBinproducts.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Prelims.LModPbCommute.
Require Import Modules.Prelims.DerivationIsFunctorial.
Require Import Modules.Prelims.deriveadj.
Require Import Modules.Prelims.LModuleBinProduct.

Require Import Modules.Arities.HArityDerivation.

Module HAr := aritiesalt.

(* (* deja defini dans signatureExamples *) *)
(* Fixpoint iter_functor {C : precategory} (G: functor C C) (n : nat) : functor C C := match n with *)
(*   | O => G *)
(*   | S n' => functor_composite (iter_functor G n') G *)
(*   end. *)




Section check.

  Context {C : category}
          (bpC: BinProducts C)
          (bcpC : limits.bincoproducts.BinCoproducts C)
          (CT : limits.terminal.Terminal C).

  Let MOD (R : Monad C) := (precategory_LModule R C).

(* Definition nat_deriv_hss_sig  := *)
(*   precomp_option_iter_Signature (homset_property C) bcpC CT. *)
  (* Arity_to_Signature (homset_property C) bpC bcpC CT  (Lists.cons n Lists.nil). *)

(* Definition nat_deriv_lmodule (n : nat) := *)
(*   (ModulesFromSignatures.lift_lmodule (nat_deriv_hss_sig n)). *)

Fixpoint nat_deriv_HAr (n :nat) : arity C :=
  match n with
    0 => tautological_harity
  | S m => harity_deriv bcpC CT (nat_deriv_HAr m)
  end.
  (* hss_to_ar (nat_deriv_hss_sig n). *)
(* Definition nat_deriv_HAr (n :nat) := *)
(*   hss_to_ar (nat_deriv_hss_sig n). *)

  Let prodHAr  :=
    (functor_fix_snd_arg _ _ _  (binproduct_functor  (harity_BinProducts bpC ))
                         (tautological_harity)).
  Definition nat_prod_HAr (n :nat) : arity C :=
    iter_functor prodHAr n tautological_harity.

Local Notation "∂" := (LModule_deriv_functor (TerminalObject CT) bcpC
                                             (homset_property _) _).

  Local Notation LMOD_bp R := (LModule_BinProducts R bpC (homset_property C)).
  Let prodR (R : Monad C) :=
    (functor_fix_snd_arg _ _ _  (binproduct_functor  (LMOD_bp R))
                         (tautological_LModule R)).
  Local Notation halfArity := (arity C).
  Let q1 (R : Monad C) (a : halfArity) : LModule R C :=
    (BinProductObject  _ (harity_BinProducts bpC a (nat_prod_HAr 0)) : halfArity)
      R.

  Let q2 (R : Monad C) (a : halfArity) : LModule R C := prodR R (a R).
  Local Notation "×ℜ" := prodR.

  (* Let p1n n R := nat_deriv_lmodule n R (tautological_LModule R). *)
  Let p1n n  := nat_deriv_HAr n.

  Let p1 := p1n 1.
  Let p2 R := (∂ (tautological_LModule R) : LModule _ _).

  Definition LMod_deriv12_iso (R : Monad C) :
    iso (C := MOD R) (p1 R)  (p2 R) := idtoiso (idpath _).


  Check ((fun R n => idpath _) :
           ∏ R n, (p1n (S n) R : LModule _ _) = (∂ (p1n n R) : LModule _ _)). 

  Check ((fun R n => idpath _) :
           ∏ R n, (nat_prod_HAr (S n) R : LModule _ _) = (prodR R (nat_prod_HAr n R))).


End  check.
(* obsolete *)

(* Peut être utile à un autre moment *)
Module Z.
Definition nat_deriv_bindingSig (n :nat) : BindingSig :=
  mkBindingSig isasetunit (fun _ => Lists.cons n Lists.nil).

Definition nat_prod_bindingSig (n :nat) : BindingSig :=
  mkBindingSig isasetunit (fun _ => Lists.functionToList n (fun _ => 0)).

(* Axiom myadmit : forall A, A. *)


Section check.

  Context {C : category}
          (bpC: BinProducts C)
          (bcpC : limits.bincoproducts.BinCoproducts C)
          (CT : limits.terminal.Terminal C).

  Let MOD (R : Monad C) := (precategory_LModule R C).


Definition nat_deriv_hss_sig (n : nat) :=
  BindingSigToSignature (C := C) (homset_property C) bpC bcpC CT
                        (nat_deriv_bindingSig n) Coproducts_Unit.

Definition nat_prod_hss_sig (n : nat) :=
  BindingSigToSignature (C := C) (homset_property C) bpC bcpC CT
                        (nat_prod_bindingSig n) Coproducts_Unit.

Definition nat_deriv_HAr (n :nat) :=
  hss_to_ar (nat_deriv_hss_sig n).

Definition nat_prod_HAr (n :nat) :=
  hss_to_ar (nat_prod_hss_sig n).

Local Notation "∂" := (LModule_deriv_functor (TerminalObject CT) bcpC
                                             (homset_property _) _).

  Local Notation LMOD_bp R := (LModule_BinProducts R bpC (homset_property C)).
  Let prodR (R : Monad C) :=
    (functor_fix_snd_arg _ _ _  (binproduct_functor  (LMOD_bp R))
                         (tautological_LModule R)).
  Local Notation halfArity := (arity C).
  Let q1 (R : Monad C) (a : halfArity) : LModule R C :=
    (BinProductObject  _ (harity_BinProducts bpC a (nat_prod_HAr 1)) : halfArity)
      R.

  Let q2 (R : Monad C) (a : halfArity) : LModule R C := prodR R (a R).
  Local Notation "×ℜ" := prodR.

(** no definitional eqality as a functor *)
(** nor as functors  *)
Fail Definition eq_as_functor (R : Monad C) :
   ((nat_deriv_HAr 1) R : functor _ _) = (∂ (tautological_LModule R) : LModule _ _) 
    := idpath _.

Fail Definition eq_as_functor (R : Monad C) M :
   (q1 R M : functor _ _) = (q2 R M : LModule _ _) 
    := idpath _.

(** but on objects they are equal *)
Local Definition eq_deriv_functor_on_ob (R : Monad C)  :
  functor_on_objects ((nat_deriv_HAr 1) R : functor _ _)  =
  functor_on_objects (∂ (tautological_LModule R) : LModule _ _)  := idpath _.

Local Definition eq_prod_functor_on_ob (R : Monad C) M :
  functor_on_objects (q1 R M : functor _ _)  =
  functor_on_objects (q2 R M  ) := idpath _.

(** Not on morphisms though *)
Fail Definition eq_functor_on_mor (R : Monad C) a b f :
  @functor_on_morphisms _ _ ((nat_deriv_HAr 1) R : functor _ _) a b f  =
  @functor_on_morphisms _ _ (∂ (tautological_LModule R) : LModule _ _) a b f := idpath _.

Fail Definition eq_functor_on_mor (R : Monad C) M  a b f :
  @functor_on_morphisms _ _ (q1 R M) a b f  =
  @functor_on_morphisms _ _ (q2 R M) a b f := idpath _.

Local Definition eq_deriv_functor_on_mor (R : Monad C) a b f :
  @functor_on_morphisms _ _ ((nat_deriv_HAr 1) R : functor _ _) a b f  =
  @functor_on_morphisms _ _ (∂ (tautological_LModule R) : LModule _ _) a b f := id_right _.

Local Definition eq_prod_functor_on_mor (R : Monad C) M  a b f :
  @functor_on_morphisms _ _ (q1 R M) a b f  =
  @functor_on_morphisms _ _ (q2 R M) a b f := maponpaths _ (id_right _).

Let p1 := (nat_deriv_HAr 1).
Let p2 R := (∂ (tautological_LModule R) : LModule _ _).
(* Local Notation "∂_2 R" := (∂ (tautological_LModule R) : LModule _ _). *)

Lemma LMod_deriv12_is_nat_trans R : is_nat_trans (p1 R) (p2 R) (λ x : C, identity ((p2 R) x)).
Proof.
  intros x x' f.
  etrans;[apply id_right|].
  etrans;[apply id_right|].
  apply pathsinv0.
  apply id_left.
Defined.

Lemma LMod_prod12_is_nat_trans R M : is_nat_trans (q1 R M) (q2 R M) (λ x : C, identity ((q2 R M) x)).
Proof.
  intros x x' f.
  etrans;[apply id_right|].
  apply pathsinv0.
  etrans;[apply id_left|].
  apply pathsinv0.
  cbn.
  unfold BinProduct_of_functors_mor; cbn.
  apply maponpaths,id_right.
Defined.

Definition LMod_deriv12_nat_trans R : nat_trans (p1 R) (p2 R) :=
  mk_nat_trans _ _ _  (LMod_deriv12_is_nat_trans R).

Definition LMod_prod12_nat_trans R M : nat_trans (q1 R M) (q2 R M) :=
  mk_nat_trans _ _ _  (LMod_prod12_is_nat_trans R M).

Lemma LMod_deriv12_nat_trans_is_iso R : is_iso (C := [C,C]) (LMod_deriv12_nat_trans R).
Proof.
  apply functor_iso_if_pointwise_iso .
  intro a.
  apply identity_is_iso.
Defined.
Lemma LMod_prod12_nat_trans_is_iso R M : is_iso (C := [C,C]) (LMod_prod12_nat_trans R M).
Proof.
  apply functor_iso_if_pointwise_iso .
  intro a.
  apply identity_is_iso.
Defined.

Definition LMod_deriv12_nat_trans_iso R : iso (C := [C,C])
                                              (p1 R : functor _ _) (p2 R : functor _ _) :=
  isopair  _ (LMod_deriv12_nat_trans_is_iso R).

Definition LMod_prod12_nat_trans_iso R M : iso (C := [C,C])
                                              (q1 R M : functor _ _) (q2 R M : functor _ _) :=
  isopair  _ (LMod_prod12_nat_trans_is_iso R M).

Lemma  LModule_deriv12_Mod_laws R : LModule_Mor_laws R (LMod_deriv12_nat_trans R).
Proof.
  intro c.
  cbn.
  now repeat (rewrite id_left || rewrite id_right).
Qed.

Lemma  LModule_prod12_Mod_laws R M : LModule_Mor_laws R (LMod_prod12_nat_trans R M).
Proof.
  intro c.
  cbn.
  now repeat (rewrite id_left || rewrite id_right).
Qed.

Lemma  LModule_deriv12_inv_Mod_laws R
  : LModule_Mor_laws R (inv_from_iso (LMod_deriv12_nat_trans_iso R)).
Proof.
  intro c.
  cbn.
  now repeat (rewrite id_left || rewrite id_right).
Qed.

Lemma  LModule_prod12_inv_Mod_laws R M
  : LModule_Mor_laws R (inv_from_iso (LMod_prod12_nat_trans_iso R M)).
Proof.
  intro c.
  cbn.
  now repeat (rewrite id_left || rewrite id_right).
Qed.
(* TODO : déplace r_a dans lib *)
(* Definition nat_trans_comp_compose {D : precategory}{C' : category} {F G H : functor D C'} *)
(*            (u : nat_trans F G) (v : nat_trans G H) : nat_trans_comp u v = compose (C := [D,C']) u v := *)
(*   idpath _. *)

Definition LMod_deriv12_mor R : LModule_Mor R (p1 R) (p2 R) := _ ,, LModule_deriv12_Mod_laws R.
Definition LMod_prod12_mor R M : LModule_Mor R (q1 R M) (q2 R M) :=
  _ ,, LModule_prod12_Mod_laws R M.

Definition LMod_deriv12_inv_mor R : LModule_Mor R (p2 R) (p1 R) := _ ,, LModule_deriv12_inv_Mod_laws R.

Definition LMod_prod12_inv_mor R M : LModule_Mor R (q2 R M) (q1 R M) :=
  _ ,, LModule_prod12_inv_Mod_laws R M.

  Lemma  LMod_deriv12_is_inverse R : 
    is_inverse_in_precat (C := precategory_LModule R _)
                         (LMod_deriv12_mor R) (LMod_deriv12_inv_mor R).
  Proof.
    use mk_is_inverse_in_precat.
    - apply LModule_Mor_equiv;[apply homset_property|].
      (* maybe not necessary to go pointwise but easier *)
      apply nat_trans_eq;[apply homset_property|].
      intro; cbn.
      now repeat rewrite id_left.
    - apply LModule_Mor_equiv;[apply homset_property|].
      (* maybe not necessary to go pointwise but easier *)
      apply nat_trans_eq;[apply homset_property|].
      intro; cbn.
      now repeat rewrite id_left.
  Defined.
  Lemma  LMod_prod12_is_inverse R M : 
    is_inverse_in_precat (C := precategory_LModule R _)
                         (LMod_prod12_mor R M) (LMod_prod12_inv_mor R M).
  Proof.
    use mk_is_inverse_in_precat.
    - apply LModule_Mor_equiv;[apply homset_property|].
      (* maybe not necessary to go pointwise but easier *)
      apply nat_trans_eq;[apply homset_property|].
      intro; cbn.
      now repeat rewrite id_left.
    - apply LModule_Mor_equiv;[apply homset_property|].
      (* maybe not necessary to go pointwise but easier *)
      apply nat_trans_eq;[apply homset_property|].
      intro; cbn.
      now repeat rewrite id_left.
  Defined.


  Definition LMod_deriv12_iso (R : Monad C) :
    iso (C := MOD R) (p1 R)  (p2 R) .
  Proof.
    eapply isopair.
    apply is_iso_from_is_z_iso.
    eapply mk_is_z_isomorphism.
    apply LMod_deriv12_is_inverse.
  Defined.

  Definition LMod_prod12_iso (R : Monad C) M :
    iso (C := MOD R) (q1 R M)  (q2 R M) .
  Proof.
    eapply isopair.
    apply is_iso_from_is_z_iso.
    eapply mk_is_z_isomorphism.
    apply LMod_prod12_is_inverse.
  Defined.


End  check.
End Z.