(* We show that binding signatures (or algebraic arities) are epi arities
and that they are presentable

- binding signatures preserves epimorphisms [BindingSigAreEpiSig]
- binding signatures preserves the preservations of epimorphisms [BindingSigAreEpiEpiSig]:
  if a functor preserves epimorphisms, then its image by a binding
  signature also preserves epimorphisms.

COmmutation coproducts of binding sigs and signature
hSet out of a binding signature

TODO: generalize to an arbitrary category (rather than focus on SET for isEpiSig)

- the initial model preserves epis

- coprod of binding sig
- iso between signature of coproducts of binding sig and coproduct of signautes of binding
sigs
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import Modules.Prelims.EpiComplements.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.CoproductsComplements.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import Modules.Signatures.SigWithStrengthToSignature.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.HssInitialModel.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Open Scope cat.

  (** Turn a binding signature into an algebraic 1-signature *)
Definition binding_to_one_sig {C : category} bpC bcpC
           (cpC : ∏ X, isaset X -> Coproducts X C ) TC S : signature C :=
  (sigWithStrength_to_sig (C := C) (BindingSigToSignature bpC bcpC TC
                                              S (cpC _ (BindingSigIsaset S)))).

  (** Turn an arity of a binding signature (i.e. a list of natural numbers
specifying an operation in the syntax) into an elementary 1-signature *)
Definition arity_to_one_sig {C : category} bpC bcpC  TC S : signature C :=
  (sigWithStrength_to_sig (C := C) (Arity_to_Signature  bpC bcpC TC S )).

(** specific definition for the hSet category *)
Definition binding_to_one_sigHSET S :=
  (sigWithStrength_to_sig (C := SET)
     (BindingSigToSignatureHSET S)). 

Definition Arity_to_SignatureHSET := 
  Arity_to_Signature BinProductsHSET BinCoproductsHSET TerminalHSET.

Definition arity_to_one_sigHSET S :=
  (sigWithStrength_to_sig (C := SET) (Arity_to_SignatureHSET  S )).

Section EpiSignatureSig.

  (* Local Notation H_SET := hset_category. *)
  Local Notation hom_SET := has_homsets_HSET.
  Local Notation Sig := (Signature SET SET SET).
  Local Notation EndSet := [hset_category, hset_category].
  Local Notation toSig := BindingSigToSignatureHSET .
  Local Notation Cset sig := (is_omega_cocont_BindingSigToSignatureHSET sig).

  (** The initial model of the algebraic signature *)
  Definition alg_initialR (sig : BindingSig) : (rep_disp SET) [{binding_to_one_sigHSET sig}] :=
    hss_initial_model (Cset sig).

       

  Theorem algebraic_sig_effective (sig : BindingSig)
    : isInitial _ (alg_initialR sig).
  Proof.
    use hss_sig_effective.
  Qed.




  Definition algebraic_sig_initial (sig : BindingSig)
    : Initial (rep_disp SET)[{binding_to_one_sigHSET sig}]  := make_Initial _ (algebraic_sig_effective sig).


  Let isEpiSig (S : Sig) := preserves_Epi (S : functor _ _).
  Let isEpiEpiFunc (S : functor [SET,SET] [SET,SET]) := ∏ R, preserves_Epi R -> preserves_Epi (S R).


  Local Notation ArToSig := Arity_to_SignatureHSET.

  Local Notation sumSig I Ihset  :=
      (SumOfSignatures.Sum_of_Signatures I HSET hom_SET HSET hom_SET
       (CoproductsHSET I Ihset)).

  Local Notation precompToFunc n :=
    (precomp_option_iter BinCoproductsHSET  TerminalHSET n).

  Local Notation precompToSig n :=
    (precomp_option_iter_Signature has_homsets_HSET BinCoproductsHSET  TerminalHSET n ).

  (* TODO: Si F préserve les épis, alors precomp_functor F aussi *)
  Local Notation precomp_functor  F :=

        (pre_composition_functor SET SET SET F).
  (* BinProductsHSET BinCoproductsHSET TerminalHSET ar. *)
  Local Notation binProdSig :=
    (BinProductOfSignatures.BinProduct_of_Signatures HSET
                                                     HSET
                                                     HSET
                                                     BinProductsHSET).

  Local Notation binProdFunc := 
      (binproducts.BinProduct_of_functors [HSET, HSET, hom_SET] [HSET, HSET, hom_SET]
       (binproducts.BinProducts_functor_precat HSET HSET BinProductsHSET hom_SET)).

  Local Notation sumFuncs I Ihset :=
    (coproducts.coproduct_of_functors I [HSET, HSET, hom_SET] [HSET, HSET, hom_SET]
       (coproducts.Coproducts_functor_precat I HSET HSET (CoproductsHSET I Ihset) hom_SET)
       ).


  
  Lemma isEpi_binProdSig S S' : isEpiSig S -> isEpiSig S' -> isEpiSig (binProdSig S S').
  Proof.
    use preserveEpi_binProdFunc.
    use (productEpisFunc (B := SET) (C := SET)).
    - apply productEpisSET.
    - apply epi_nt_SET_pw.
  Qed.


  Lemma precomp_func_preserveEpi F : preserves_Epi (precomp_functor F).
  Proof.
    apply preserveEpi_precomp.
    apply epi_nt_SET_pw.
  Qed.

  (** No need for an induction even though the functor is defined as such *)
  Lemma precompEpiFunc (n : nat) : preserves_Epi (precompToFunc n).
  Proof.
    destruct n as [|n ].
    - apply id_preserves_Epi.
    - apply precomp_func_preserveEpi.
  Qed.

  Lemma precompEpiEpiFuncSn (n : nat) : isEpiEpiFunc (precompToFunc (S n)).
  Proof.
    induction n as [|n ].
    - intros R fhR.
      apply composite_preserves_Epi.
      + apply preserves_Epi_option.
      + exact fhR.
    - intros R hR.
      apply composite_preserves_Epi.
      + apply IHn.
        apply preserves_Epi_option.
      + exact hR.
  Qed.
  Lemma precompEpiEpiFunc (n : nat) : isEpiEpiFunc (precompToFunc n).
  Proof.
    destruct n as [|n ].
    - exact (fun R hR => hR).
    - apply precompEpiEpiFuncSn.
  Qed.


  Lemma ArAreEpiSig (ar : list nat) : isEpiSig (ArToSig ar).
  Proof.
    pattern ar.
    apply list_ind; clear ar.
    - apply const_preserves_Epi.
    - intros n ar.
      revert n.
      pattern ar.
      apply list_ind; clear ar.
      + intros n epinil.
        cbn.
        apply precompEpiFunc.
      + intros n ar HI m epi_ar.
        intros M N f epif.
        unfold ArToSig,  Arity_to_Signature.
        rewrite 2!map_cons.
        rewrite foldr1_cons.
        apply isEpi_binProdSig.
        * apply precompEpiFunc.
        * exact epi_ar.
        * exact epif.
  Qed.
  Lemma ArAreEpiEpiSig (ar : list nat) : isEpiEpiFunc (ArToSig ar).
  Proof.
    pattern ar.
    apply list_ind; clear ar.
    - intros R _.
      apply const_preserves_Epi.
    - intros n ar.
      revert n.
      pattern ar.
      apply list_ind; clear ar.
      + intros n epinil.
        apply precompEpiEpiFunc.
      + intros n ar HI m epi_ar.
        intros R epiR.
        unfold ArToSig,  Arity_to_Signature.
        rewrite 2!map_cons.
        rewrite foldr1_cons.
        apply preserveEpi_binProdFunc.
        * apply productEpisSET.
        * apply precompEpiEpiFunc.
          exact epiR.
        * apply epi_ar; assumption.
  Qed.

  Lemma BindingSigAreEpiSig (S : BindingSig) : isEpiSig (toSig S).
  Proof.
    apply preserveEpi_sumFuncs.
    intro i.
    apply ArAreEpiSig.
  Qed.

  Lemma BindingSigAreEpiEpiSig (S : BindingSig) : isEpiEpiFunc (toSig S).
  Proof.
    intros R hR.
    apply preserveEpi_sumFuncs.
    intro i.
    apply ArAreEpiEpiSig.
    exact hR.
  Qed.

  Lemma algebraic_model_Epi (sig: BindingSig) : preserves_Epi (alg_initialR sig : model _).
  Proof.
    use Colim_Functor_Preserves_Epi.
    induction i.
    - simpl.
      intros X Y f epif.
      cbn.
      eapply (transportf (@isEpi SET _ _) (x := fun z => z) ).
      apply (InitialArrowEq (O := InitialHSET)).
      apply identity_isEpi.
    - use preserveEpi_binCoprodFunc ; [apply id_preserves_Epi|].
      apply BindingSigAreEpiEpiSig.
      apply IHi.
  Qed.

  Lemma BindingSig_on_model_isEpi (S : BindingSig) :
        preserves_Epi ((toSig S : functor _ _) ((alg_initialR S : model  _) : functor _ _)).
  Proof.
    apply BindingSigAreEpiEpiSig.
    apply algebraic_model_Epi.
  Qed.

End EpiSignatureSig.

Definition BindingSigIndexhSet : BindingSig -> hSet :=
  fun S => make_hSet _ (BindingSigIsaset S).

Section CoprodBindingSig.

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
    (BindingSigToSignature  bpC
                           bcpC TC sig (cpC _ (BindingSigIsaset sig))).
  Local Notation SIG := (Signature_category C C C).
  Let cpSig (I : hSet) : Coproducts (pr1 I) SIG
    := Coproducts_Signature_category _ C _ _ (cpC _ (setproperty I)).
  Let ArToSig := Arity_to_Signature bpC bcpC TC.
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
    apply (sigma_coprod_iso (C := SIG)
                            (B := fun o a => ArToSig (BindingSigMap (binds o) a)) CC' cp1).
  Defined.
End CoprodBindingSig.
