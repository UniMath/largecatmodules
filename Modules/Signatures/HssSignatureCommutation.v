
(**
Commutation of  the functor from hss signature to arities:
- preservation of binproducts
- preservation of coproducts
- coproducts of binding signatures and preservation
- preservation of tautological arities

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.HssToSignature.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.Signatures.PresentableSignature.
Require Import Modules.Signatures.SignatureBinproducts.
Require Import Modules.Signatures.SignatureCoproduct.

Require Import Modules.Prelims.LModPbCommute.
Require Import Modules.Prelims.BinProductComplements.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Open Scope cat.

Section commuteBinProdSig.
  Context {C : category}  .
  Local Notation SIG := (Signature_precategory C C).
  Context {I : UU}
          (bpC :  BinProducts C).
  Let bpSig  : BinProducts  SIG
    := BinProducts_Signature_precategory C C bpC.

  Let bpHAr := signature_BinProducts (C := C) bpC.

  Variable (a b : SIG).

  Let ar_a :=  hss_to_ar a.
  Let ar_b :=  hss_to_ar b.
  Local Notation BPO := (BinProductObject _ ).

  Lemma binprod_sigs_har_mod_eq_mult R c  :
    (ModulesFromSignatures.lift_lm_mult (BPO (bpSig a b)) R (tautological_LModule R) : nat_trans _ _) c =
    (LModuleBinProduct.LModule_binproduct_mult bpC (homset_property C) (ar_a R) (ar_b R) c).
  Proof.
    cbn.
    unfold BinProductOfSignatures.θ_ob_fun.
    unfold binproduct_nat_trans_data.
    etrans;[apply postcompWithBinProductArrow|].
    unfold BinProductOfArrows.
    repeat rewrite assoc.
    apply idpath.
  Defined.

  Lemma  binprod_sigs_har_mod_iso R :
    iso (C := precategory_LModule R _)
        ( hss_to_ar (BPO (bpSig a b)) R)
        ( (BPO (bpHAr ar_a ar_b) : signature _ ) R).
  Proof.
    apply LModule_M1_M2_iso.
    apply binprod_sigs_har_mod_eq_mult.
  Defined.

  Definition binprod_sigs_har_mod R : LModule_Mor _ _ _ :=
    (morphism_from_iso _ _ _ (binprod_sigs_har_mod_iso R)).

  Definition binprod_har_sigs_mod R : LModule_Mor _ _ _ :=
    (inv_from_iso  (binprod_sigs_har_mod_iso R)).


  Lemma binprod_sigs_har_signature_laws : is_signature_Mor ( hss_to_ar (BPO (bpSig a b)) ) 
                                                  ( (BPO (bpHAr ar_a ar_b) : signature _ ) )
                                        binprod_sigs_har_mod.
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    unfold binproduct_nat_trans_data.
    cbn.
    repeat rewrite id_right.
    rewrite id_left.
    apply idpath.
  Qed.
  Lemma binprod_har_sigs_signature_laws : is_signature_Mor  
                                                  ( (BPO (bpHAr ar_a ar_b) : signature _ ) )
                                                  ( hss_to_ar (BPO (bpSig a b)) )
                                        binprod_har_sigs_mod.
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    unfold binproduct_nat_trans_data.
    cbn.
    repeat rewrite id_right.
    rewrite id_left.
    apply idpath.
  Qed.

  (* Definition coprod_sigs_har_mor :  signature_precategory ⟦ (hss_to_ar (CPO (cpSig sigs))), *)
  (*                                                       (CPO (cpHAr ars))⟧  *)
  Definition binprod_sigs_har_mor : signature_precategory ⟦ ( hss_to_ar (BPO (bpSig a b)) ) ,
                                                  ( (BPO (bpHAr ar_a ar_b) : signature _ ) ) ⟧
                                                  :=
    _ ,, binprod_sigs_har_signature_laws.

  Definition binprod_har_sigs_mor : signature_precategory ⟦( (BPO (bpHAr ar_a ar_b) : signature _ ) )
                                                       ,( hss_to_ar (BPO (bpSig a b)) )⟧
                                                  :=
    _ ,, binprod_har_sigs_signature_laws.


  Lemma binprod_sigs_har_is_inverse :
    is_inverse_in_precat binprod_sigs_har_mor binprod_har_sigs_mor.
  Proof.
    use mk_is_inverse_in_precat.
    - apply signature_Mor_eq.
      intro X.
      apply (iso_inv_after_iso (binprod_sigs_har_mod_iso X)).
    - apply signature_Mor_eq.
      intro X.
      apply (iso_after_iso_inv (binprod_sigs_har_mod_iso X)).
  Defined.

  Definition binprod_sigs_har_mor_is_iso : is_iso binprod_sigs_har_mor :=
    is_iso_from_is_z_iso
      binprod_sigs_har_mor
      (mk_is_z_isomorphism binprod_sigs_har_mor binprod_har_sigs_mor binprod_sigs_har_is_inverse).


  Definition binprod_sigs_har_iso : iso (C := signature_precategory) 
                                        ( hss_to_ar (BPO (bpSig a b)) )
                                        ( (BPO (bpHAr ar_a ar_b) : signature _ ) )
                                        :=
    isopair _ binprod_sigs_har_mor_is_iso.
End commuteBinProdSig.

Section CoprodAr.
  Context {C : category}  .
  Local Notation SIG := (Signature_precategory C C).
  Context {I : UU}
          (cpC :  Coproducts I C).
  Let cpSig  : Coproducts I SIG
    := Coproducts_Signature_precategory _ C _ cpC.
  Let cpHAr := signature_Coproducts (C := C) cpC.

  Variable (sigs : I -> SIG).
  Let ars : I -> signature C := fun i => hss_to_ar (sigs i).
  Local Notation CPO := (CoproductObject _ _).

  Lemma coprod_sigs_har_mod_eq_mult R c  :
    (ModulesFromSignatures.lift_lm_mult (CPO (cpSig sigs)) R (tautological_LModule R) : nat_trans _ _) c =
    (LModuleCoproducts.LModule_coproduct_mult cpC (homset_property C) (λ o : I, (ars o) R)) c.
  Proof.
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

  Lemma  coprod_sigs_har_mod_iso R :
    iso (C := precategory_LModule R _)
        ( hss_to_ar (CPO (cpSig sigs)) R)
        ( (CPO (cpHAr ars) : signature _ ) R).
  Proof.
    apply LModule_M1_M2_iso.
    apply coprod_sigs_har_mod_eq_mult.
  Defined.

  Definition coprod_sigs_har_mod R : LModule_Mor _ _ _ :=
    (morphism_from_iso _ _ _ (coprod_sigs_har_mod_iso R)).

  Definition coprod_har_sigs_mod R : LModule_Mor _ _ _ :=
    (inv_from_iso  (coprod_sigs_har_mod_iso R)).




  Lemma coprod_sigs_har_signature_laws : is_signature_Mor  (hss_to_ar (CPO (cpSig sigs)))
                                       (CPO (cpHAr ars) : signature _) coprod_sigs_har_mod.
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
    rewrite id_right.
    apply idpath.
  Qed.
  Lemma coprod_har_sigs_signature_laws : is_signature_Mor  
                                       (CPO (cpHAr ars) : signature _)
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
    rewrite id_right.
    apply idpath.
  Qed.

  Definition coprod_sigs_har_mor :  signature_precategory ⟦ (hss_to_ar (CPO (cpSig sigs))),
                                                        (CPO (cpHAr ars))⟧ :=
    _ ,, coprod_sigs_har_signature_laws.

  Definition coprod_har_sigs_mor :  signature_precategory ⟦ 
                                                        (CPO (cpHAr ars)),
                                                        (hss_to_ar (CPO (cpSig sigs)))⟧ :=
    _ ,, coprod_har_sigs_signature_laws.


  Lemma coprod_sigs_har_is_inverse :
    is_inverse_in_precat coprod_sigs_har_mor coprod_har_sigs_mor.
  Proof.
    use mk_is_inverse_in_precat.
    - apply signature_Mor_eq.
      intro X.
      apply (iso_inv_after_iso (coprod_sigs_har_mod_iso X)).
    - apply signature_Mor_eq.
      intro X.
      apply (iso_after_iso_inv (coprod_sigs_har_mod_iso X)).
  Defined.

  Definition coprod_sigs_har_mor_is_iso : is_iso coprod_sigs_har_mor :=
    is_iso_from_is_z_iso
      coprod_sigs_har_mor
      (mk_is_z_isomorphism coprod_sigs_har_mor coprod_har_sigs_mor coprod_sigs_har_is_inverse).

  Definition coprod_sigs_har_iso : iso (C := signature_precategory) (hss_to_ar (CPO (cpSig sigs)))
                                       (CPO (cpHAr ars)) :=
    isopair _ coprod_sigs_har_mor_is_iso.


End CoprodAr.
Section TautologicalPreserve.
  Context {C : category}.
  Local Notation SIG := (Signature_precategory C C).
  Let a := (hss_to_ar (IdSignature C (homset_property C))).
  Let b := (tautological_signature (C:=C)).
                                        

  Lemma  tauto_sigs_har_mod_iso R :
    iso (C := precategory_LModule R _)
        ( a  R)
        ( b R).
  Proof.
    apply LModule_M1_M2_iso.
    intro c.
    apply id_left.
  Defined.

  Definition tauto_sigs_har_mod R : LModule_Mor _ _ _ :=
    (morphism_from_iso _ _ _ (tauto_sigs_har_mod_iso R)).

  Definition tauto_har_sigs_mod R : LModule_Mor _ _ _ :=
    (inv_from_iso  (tauto_sigs_har_mod_iso R)).


  Lemma tauto_sigs_har_signature_laws : is_signature_Mor  a b tauto_sigs_har_mod.
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    repeat rewrite id_right.
    repeat rewrite id_left.
    apply idpath.
  Qed.
  Lemma tauto_har_sigs_signature_laws : is_signature_Mor b a tauto_har_sigs_mod.
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    repeat rewrite id_right.
    repeat rewrite id_left.
    apply idpath.
  Qed.

  Definition tauto_sigs_har_mor :  signature_precategory ⟦ a, b⟧ :=
    _ ,, tauto_sigs_har_signature_laws.

  Definition tauto_har_sigs_mor :  signature_precategory ⟦b, a⟧ :=
    _ ,, tauto_har_sigs_signature_laws.


  Lemma tauto_sigs_har_is_inverse :
    is_inverse_in_precat tauto_sigs_har_mor tauto_har_sigs_mor.
  Proof.
    use mk_is_inverse_in_precat.
    - apply signature_Mor_eq.
      intro X.
      apply (iso_inv_after_iso (tauto_sigs_har_mod_iso X)).
    - apply signature_Mor_eq.
      intro X.
      apply (iso_after_iso_inv (tauto_sigs_har_mod_iso X)).
  Defined.

  Definition tauto_sigs_har_mor_is_iso : is_iso tauto_sigs_har_mor :=
    is_iso_from_is_z_iso
      tauto_sigs_har_mor
      (mk_is_z_isomorphism tauto_sigs_har_mor tauto_har_sigs_mor tauto_sigs_har_is_inverse).

  Definition tauto_sigs_har_iso : iso (C := signature_precategory) a
                                       b :=
    isopair _ tauto_sigs_har_mor_is_iso.

End TautologicalPreserve.