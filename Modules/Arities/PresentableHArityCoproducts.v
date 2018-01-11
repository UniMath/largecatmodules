(* We show that coproducts of presentable (half-)arities are presentable

-coprod of binding sig
- iso between signature of coproducts of binding sig and coproduct of signautes of binding
sigs
- iso between arity of coproducts of signatures and coproduct of arities of signatures.
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

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Open Scope cat.

Section CoprodBindingSig.
  Definition BindingSigIndexhSet : BindingSig -> hSet :=
    fun S => hSetpair _ (BindingSigIsaset S).

  Definition BindingSigIndexhSet_coprod  {O : hSet} (sigs : O -> BindingSig)
                                                     : hSet :=
    (∑ (o : O), BindingSigIndexhSet (sigs o))%set.

  Definition coprod_BindingSig {O : hSet} (sigs : O -> BindingSig) : BindingSig.
  Proof.
    apply (mkBindingSig (I := BindingSigIndexhSet_coprod sigs)).
    - apply setproperty.
    - intro x.
      exact (BindingSigMap (sigs (pr1 x)) (pr2 x)).
  Defined.

  Context {C : category} (bpC : BinProducts C) (bcpC : BinCoproducts C) (TC : Terminal C)
          (cpC : ∏ (X : UU) (setX : isaset X), Coproducts X C).

  Let toSig sig :=
    (BindingSigToSignature (homset_property C) bpC
                           bcpC TC sig (cpC _ (BindingSigIsaset sig))).
  Local Notation SIG := (Signature_precategory C C).
  Let hsSig := has_homsets_Signature_precategory C C.
  Let cpSig (I : hSet) : Coproducts (pr1 I) SIG
    := Coproducts_Signature_precategory _ C _ (cpC _ (setproperty I)).
  Let ArToSig := Arity_to_Signature (homset_property C) bpC bcpC TC.
  Let CP_from_BindingSig (S : BindingSig) := (cpSig  _ (fun (o : BindingSigIndexhSet S)
                                                        => ArToSig (BindingSigMap _ o))).

  Definition binding_Sig_iso {O : hSet} (sigs : O -> BindingSig) : iso (C := SIG)
                               (toSig (coprod_BindingSig sigs))
                               (CoproductObject _ _ (cpSig O (fun o => toSig (sigs o)))).
  Proof.
    set (binds := fun o => (sigs o)).
    set (cpSigs := coprod_BindingSig sigs).
    set (CC' := CP_from_BindingSig cpSigs).
    set (cp1 := fun o =>
                  CP_from_BindingSig (binds o)).
    apply (sigma_coprod_iso (C := SIG ,, hsSig)
                            (B := fun o a => ArToSig (BindingSigMap (binds o) a)) CC' cp1).
  Defined.
End CoprodBindingSig.

Section CoprodAr.
  Context {C : category}  .
  Local Notation SIG := (Signature_precategory C C).
  Context {I : UU}
          (cpC :  Coproducts I C).
  Let cpSig  : Coproducts I SIG
    := Coproducts_Signature_precategory _ C _ cpC.
  Let cpHAr := harity_Coproducts (C := C) cpC.

  Variable (sigs : I -> SIG).
  Let ars : I -> arity C := fun i => hss_to_ar (sigs i).
  Local Notation CPO := (CoproductObject _ _).

  Lemma coprod_sigs_har_mod_laws R :
    LModule_Mor_laws R (T := hss_to_ar (CPO (cpSig sigs)) R)
                     (T' := (CPO (cpHAr ars) : arity _ ) R)
                     (nat_trans_id _).
  Proof.
    intro c.
    simpl.
    rewrite id_left,id_right.
    cbn.
    unfold SumOfSignatures.θ_ob_fun.
    unfold coproducts.coproduct_nat_trans_data.
    apply pathsinv0.
    etrans;[apply precompWithCoproductArrow|].
    unfold LModuleCoproducts.LModule_coproduct_mult_data.
    unfold CoproductOfArrows.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply  assoc.
  Qed.
  Lemma coprod_har_sigs_mod_laws R :
    LModule_Mor_laws R (T := (CPO (cpHAr ars) : arity _ ) R)
                     (T' := hss_to_ar (CPO (cpSig sigs)) R)
                     (nat_trans_id _).
  Proof.
    intro c.
    simpl.
    rewrite id_left,id_right.
    cbn.
    unfold SumOfSignatures.θ_ob_fun.
    unfold coproducts.coproduct_nat_trans_data.
    etrans;[apply precompWithCoproductArrow|].
    unfold LModuleCoproducts.LModule_coproduct_mult_data.
    unfold CoproductOfArrows.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply  assoc.
  Qed.
  Definition coprod_har_sigs_mod R :
    LModule_Mor R 
                ((CPO (cpHAr ars) : arity _ ) R)(hss_to_ar (CPO (cpSig sigs)) R) :=
    _ ,, coprod_har_sigs_mod_laws R.

  Definition coprod_sigs_har_mod R :
    LModule_Mor R 
                (hss_to_ar (CPO (cpSig sigs)) R)
                ((CPO (cpHAr ars) : arity _ ) R) :=
    _ ,, coprod_sigs_har_mod_laws R.

  Lemma  coprod_sigs_har_mod_is_inverse R : 
    is_inverse_in_precat (C := precategory_LModule R _)
                         (coprod_sigs_har_mod R) (coprod_har_sigs_mod R).
  Proof.
    use mk_is_inverse_in_precat.
    - apply LModule_Mor_equiv;[apply homset_property|].
      apply (id_right (C := [C,C])).
    - apply LModule_Mor_equiv;[apply homset_property|].
      apply (id_right (C := [C,C])).
  Defined.

  Lemma coprod_sigs_har_arity_laws : is_arity_Mor  (hss_to_ar (CPO (cpSig sigs)))
                                       (CPO (cpHAr ars) : arity _) coprod_sigs_har_mod.
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    unfold coproducts.coproduct_nat_trans_data.
    cbn.
    repeat rewrite id_right.
    rewrite id_left.
    apply maponpaths.
    apply funextsec.
    intro i.
    now rewrite id_right.
  Qed.
  Lemma coprod_har_sigs_arity_laws : is_arity_Mor  
                                       (CPO (cpHAr ars) : arity _)
                                       (hss_to_ar (CPO (cpSig sigs)))
                                       coprod_har_sigs_mod.
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    unfold coproducts.coproduct_nat_trans_data.
    cbn.
    repeat rewrite id_right.
    rewrite id_left.
    apply maponpaths.
    apply funextsec.
    intro i.
    now rewrite id_right.
  Qed.

  Definition coprod_sigs_har_mor :  arity_precategory ⟦ (hss_to_ar (CPO (cpSig sigs))),
                                                        (CPO (cpHAr ars))⟧ :=
    _ ,, coprod_sigs_har_arity_laws.

  Definition coprod_har_sigs_mor :  arity_precategory ⟦ 
                                                        (CPO (cpHAr ars)),
                                                        (hss_to_ar (CPO (cpSig sigs)))⟧ :=
    _ ,, coprod_har_sigs_arity_laws.


  Lemma coprod_sigs_har_is_inverse :
    is_inverse_in_precat coprod_sigs_har_mor coprod_har_sigs_mor.
  Proof.
    use mk_is_inverse_in_precat.
    - apply arity_Mor_eq.
      intro X.
      apply (is_inverse_in_precat1 (coprod_sigs_har_mod_is_inverse X)).
    - apply arity_Mor_eq.
      intro X.
      apply (is_inverse_in_precat2 (coprod_sigs_har_mod_is_inverse X)).
  Defined.

  Definition coprod_sigs_har_mor_is_iso : is_iso coprod_sigs_har_mor :=
    is_iso_from_is_z_iso
      coprod_sigs_har_mor
      (mk_is_z_isomorphism coprod_sigs_har_mor coprod_har_sigs_mor coprod_sigs_har_is_inverse).

  Definition coprod_sigs_har_iso : iso (C := arity_precategory) (hss_to_ar (CPO (cpSig sigs)))
                                       (CPO (cpHAr ars)) :=
    isopair _ coprod_sigs_har_mor_is_iso.


End CoprodAr.

Section CoprodPresentable.


  Local Notation hom_SET := has_homsets_HSET.
  Local Notation Sig := (Signature SET has_homsets_HSET hset_precategory has_homsets_HSET).
  Local Notation EndSet := [hset_category, hset_category].

  Local Notation toSig sig :=
    (BindingSigToSignature has_homsets_HSET BinProductsHSET
                           BinCoproductsHSET TerminalHSET sig
                           (CoproductsHSET (BindingSigIndex sig) (BindingSigIsaset sig))).


  Context {O : hSet} {α : O -> arity SET} (pres_α : ∏ o, isPresentable (α o)).
  Local Notation CPO := (CoproductObject  _ _).

  Let bind_α (o : O) : BindingSig := p_sig (pres_α o).

  Let cpS := CoproductsHSET O (setproperty O).
  Let cpHAr := harity_Coproducts (C := SET) cpS.

  Definition coprod_ρ_mor :
    arity_precategory ⟦(hss_to_ar( C:=SET) (toSig (coprod_BindingSig bind_α))),
                       (CPO (cpHAr α) : arity _)⟧.
  Proof.
    eapply compose.
    {
      eapply (# hss_to_ar_functor).
      eapply morphism_from_iso.
      use binding_Sig_iso.
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
    ∏ R : Monad SET, isEpi (C := [SET,SET])(((coprod_ρ_mor : arity_Mor _ _) R) : nat_trans _ _).
  Proof.
    intro R.
    use isEpi_comp;[| use isEpi_comp].
    - 
      unfold coprod_ρ_mor.
      (* TODO utiliser is_iso_pw *)
      (* use Pushouts_pw_epi. *)
      apply is_iso_isEpi.
      apply is_z_iso_from_is_iso.
      apply nat_trans_is_iso_to_pw.
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

  (*   arity_Mor (hss_to_ar( C:=SET) (toSig (coprod_BindingSig bind_α))) (CPO (cpHAr α) : arity _). *)
  (*   eapply compose. *)
  (* apply CoproductIn. *)

  Definition coprod_isPresentable : isPresentable (CoproductObject _ _ (cpHAr α)).
     use tpair.
     - eapply coprod_BindingSig.
       exact bind_α.
     - use tpair.
       + exact coprod_ρ_mor.
       + cbn beta.
         apply coprod_epi_p_mor.
  Defined.
End CoprodPresentable.


