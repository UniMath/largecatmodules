(* We show that coproducts of presentable (half-)arities are presentable

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.

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
Require Import Modules.Arities.HssToArity.
Require Import Modules.Arities.BindingSig.
Require Import Modules.Arities.PresentableArity.
Require Import Modules.Arities.HArityCoproduct.
Require Import Modules.Arities.HssArityCommutation.

Require Import Modules.Prelims.LModPbCommute.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Open Scope cat.


Section CoprodPresentable.

  Context {C : category} {bp : BinProducts C} {bcp : BinCoproducts C} {T : Terminal C}
          {cp : ∏ (I : hSet), Coproducts I C}.

  
  Let toSig sig :=
    (BindingSigToSignature (homset_property _) bp bcp T
                           sig (cp (BindingSigIndexhSet sig))).


  Context {O : hSet} {α : O -> arity C} (pres_α : ∏ o, isPresentable bp bcp T cp (α o)).
  Local Notation CPO := (CoproductObject  _ _).

  Let bind_α (o : O) : BindingSig := p_sig (pres_α o).

  Let cpHAr := harity_Coproducts (C := C) (cp O).

  Definition coprod_ρ_mor :
    arity_precategory ⟦(hss_to_ar( C:=C) (toSig (coprod_BindingSig bind_α))),
                       (CPO (cpHAr α) : arity _)⟧.
  Proof.
    eapply compose.
    {
      eapply (# hss_to_ar_functor).
      eapply morphism_from_iso.
      use (binding_Sig_iso bp bcp T (fun x y => cp (hSetpair _ y))).
    }
    eapply compose.
    {
      eapply morphism_from_iso.
      use coprod_sigs_har_iso.
    }
    apply CoproductOfArrows.
    intro o.
    use (p_mor (pres_α o)).
  Defined.
  Lemma coprod_epi_p_mor :
    (* ∏ R : Monad SET, isEpi (C := [SET,SET])(((coprod_ρ_mor : arity_Mor _ _) R) : nat_trans _ _). *)
    ∏ R : Monad C, isEpi (C := [C,C])(((coprod_ρ_mor : arity_Mor _ _) R) : nat_trans _ _).
  Proof.
    intro R.
    use isEpi_comp;[| use isEpi_comp].
    - 
      unfold coprod_ρ_mor.
      (* TODO utiliser is_iso_pw *)
      (* use Pushouts_pw_epi. *)
      apply is_iso_isEpi.
      apply is_z_iso_from_is_iso.
      apply is_functor_iso_pointwise_if_iso.
      set (F := SignatureForgetfulFunctor _ _).
      set (f := binding_Sig_iso _ _ _ _ _).
      apply is_iso_from_is_z_iso.
      use (functor_on_is_z_isomorphism F (f := f)).
      apply is_z_iso_from_is_iso.
      apply iso_is_iso.
    - apply identity_isEpi.
    - use CoproductOfArrows_isEpi.
      intro i.
      cbn.
      use epi_p_mor.


  Qed.


  Definition coprod_isPresentable : isPresentable bp bcp T cp (CoproductObject _ _ (cpHAr α)).
     use tpair.
     - eapply coprod_BindingSig.
       exact bind_α.
     - use tpair.
       + exact coprod_ρ_mor.
       + cbn beta.
         apply coprod_epi_p_mor.
  Defined.
End CoprodPresentable.


