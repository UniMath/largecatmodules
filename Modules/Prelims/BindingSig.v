(* We show that binding signatures (or algebraic arities) are epi arities
and that they are presentable
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import Modules.Prelims.HssToArity.
Require Import Modules.Prelims.aritiesalt.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Open Scope cat.

(* TODO : déplacer ce lemme dans lib, et l'utiliser dans uniproofalt *)
Lemma epi_nt_SET_pw {C : precategory} {A B : C ⟶ SET} (a : A ⟹ B) :
    isEpi (C := [C , SET]) a → ∏ x : C, isEpi (a x).
Proof.
  apply Pushouts_pw_epi.
  apply PushoutsHSET_from_Colims.
Qed.

Section EpiAritySig.

  (* Local Notation H_SET := hset_category. *)
  Local Notation hom_SET := has_homsets_HSET.
  Local Notation Sig := (Signature SET has_homsets_HSET hset_precategory has_homsets_HSET).
  Local Notation EndSet := [hset_category, hset_category].
  Local Notation toSig sig :=
    (BindingSigToSignature has_homsets_HSET BinProductsHSET
                          BinCoproductsHSET TerminalHSET sig
                          (CoproductsHSET (BindingSigIndex sig) (BindingSigIsaset sig))).

  (** The initial representation of the algebraic signature *)
  Lemma alg_initialR (sig : BindingSig) : (rep_disp SET)[{hss_to_ar (C := SET) (toSig sig)}].
  Proof.
    mkpair.
    - apply (BindingSigToMonadHSET sig).
    - apply τ_lmodule_mor.
  Defined.

  Definition alg_initial_arrow_mon {sig : BindingSig} 
    (b : rep_ar SET (hss_to_ar (C := SET)(toSig sig))) :
      Monad_Mor  (pr1 (alg_initialR sig)) b.
  Proof.
    apply j_mon.
    apply (rep_τ _ b).
  Defined.

  (* j_mon is a morphism of representation *)
  Definition alg_initial_arrow_law {sig : BindingSig} 
    (b : rep_ar SET (hss_to_ar (C := SET)(toSig sig))) :
    rep_ar_mor_law SET (alg_initialR sig) b (arity_Mor_id (hss_to_ar_data (C:=SET) (toSig sig)))
      (alg_initial_arrow_mon b).
  Proof.
    intro c.
    apply j_mor_rep.
  Qed.

  Definition alg_initial_arrow {sig : BindingSig} 
    (b : rep_ar SET (hss_to_ar (C := SET)(toSig sig))) :
    (rep_disp SET)[{hss_to_ar (C := SET)(toSig sig)}] ⟦ alg_initialR sig, b ⟧
    := alg_initial_arrow_mon b,, alg_initial_arrow_law b.

  Local Notation EndAlg sig :=
    (FunctorAlg (Id_H HSET hom_SET BinCoproductsHSET (toSig sig))
          (functor_category_has_homsets HSET HSET hom_SET)).

  Local Notation M_alg := (ModulesFromSignatures.M_alg HSET hom_SET BinCoproductsHSET).
  (* Local Lemma omega_cont_to_sig CocontFunctors.is_omega_cocont (toSig sig) *)

  Local Notation iniHSS sig   := (InitialHSS SET (homset_property SET) BinCoproductsHSET InitialHSET
                                        (ColimsHSET_of_shape CocontFunctors.nat_graph)
                                        (toSig sig)
                                        (is_omega_cocont_BindingSigToSignatureHSET sig)).





  Lemma rep_mor_to_alg_is_alg_mor {sig : BindingSig}
             (b : rep_ar SET (hss_to_ar (C := SET)(toSig sig)))
             (t : (rep_disp SET)[{hss_to_ar (C := SET) (toSig sig)}] ⟦ alg_initialR sig, b ⟧) :
    is_algebra_mor (Id_H HSET hom_SET BinCoproductsHSET (toSig sig))
                   (pr1 (pr1 (iniHSS sig)))
                   (M_alg (toSig sig) b (rep_τ SET b))
                   (pr1 (pr1 t)).
  Proof.
    red.
    apply nat_trans_eq; [apply (homset_property SET)|].
    intro X.
    apply funextfun.
    intro x.
    (* x is in a coproduct. We check both cases *)
    destruct x as [x|x].
    - assert (ht := Monad_Mor_η (pr1 ( t)) X).
      apply toforallpaths in ht.
      specialize (ht x).
      apply ht.
    - assert (ht := rep_ar_mor_ax _  t X).
      apply toforallpaths in ht.
      specialize (ht x).
      apply ht.
  Qed.

    
    
  
  Definition rep_mor_to_alg_mor {sig : BindingSig}
             (b : rep_ar SET (hss_to_ar (C := SET)(toSig sig)))
             (t : (rep_disp SET)[{hss_to_ar (C := SET) (toSig sig)}] ⟦ alg_initialR sig, b ⟧) :
    EndAlg sig ⟦ (pr1 (pr1 (iniHSS sig))) , M_alg (toSig sig) b (rep_τ SET b) ⟧.
  Proof.
    mkpair.
    - apply t.
    - apply (rep_mor_to_alg_is_alg_mor b t).
  Defined.



  Lemma alg_initial_arrow_unique  {sig : BindingSig} 
    (b : rep_ar SET (hss_to_ar (C := SET)(toSig sig))) :
    ∏ t : (rep_disp SET)[{hss_to_ar (C := SET) (toSig sig)}] ⟦ alg_initialR sig, b ⟧,
          t = alg_initial_arrow b.
  Proof.
    intro t.

    (* TODO : mettre ce lemme d'unicité qui vient de la définition de j avec sa définition
 dans ModulesFromSignatures *)
    assert (h := (InitialArrowUnique
     (CocontFunctors.colimAlgInitial (functor_category_has_homsets HSET HSET hom_SET)
        (Initial_functor_precat HSET HSET InitialHSET hom_SET)
        (is_omega_cocont_Id_H HSET hom_SET BinCoproductsHSET (toSig sig)
           (is_omega_cocont_BindingSigToSignature hom_SET BinProductsHSET BinCoproductsHSET
              TerminalHSET (ColimsHSET_of_shape CocontFunctors.nat_graph)
              (λ F : hset_precategory_data ⟶ hset_precategory_data,
               CocontFunctors.is_omega_cocont_constprod_functor1
                 (binproducts.BinProducts_functor_precat HSET HSET BinProductsHSET hom_SET)
                 BindingSigToMonad.has_homsets_HSET2 (has_exponentials_functor_HSET HSET hom_SET) F)
              sig (CoproductsHSET (BindingSigIndex sig) (BindingSigIsaset sig))))
        (colimits.ColimsFunctorCategory_of_shape CocontFunctors.nat_graph 
           HSET HSET hom_SET (ColimsHSET_of_shape CocontFunctors.nat_graph)
           (CocontFunctors.initChain (Initial_functor_precat HSET HSET InitialHSET hom_SET)
              (Id_H HSET hom_SET BinCoproductsHSET (toSig sig)))))
     (ModulesFromSignatures.M_alg HSET hom_SET BinCoproductsHSET (toSig sig) b (rep_τ SET b)))).
    specialize (h (rep_mor_to_alg_mor b t)).
    apply rep_ar_mor_mor_equiv.
    apply algebra_mor_eq in h; [|apply (homset_property EndSet)].
    intro c.
    eapply nat_trans_eq_pointwise in h.
    apply h.
  Qed.
       
       

  Theorem algbraic_sig_representable (sig : BindingSig)
    : isInitial _ (alg_initialR sig).
  Proof.
    intro b.
    cbn in b.
    unshelve eapply iscontrpair.
    - apply alg_initial_arrow.
    - apply alg_initial_arrow_unique.
  Qed.


  Definition preserveEpi {C D : precategory} (F : functor C D) :=
    ∏ M N (f : C ⟦ M, N ⟧), isEpi f → isEpi (#F f).



  (* Definition isEpiFunc (F : functor _ _) := per *)
  (*   ∏ M N (f:EndSet ⟦M,N⟧), isEpi (C := [_ , _]) f → isEpi (C := [H_SET, H_SET, *)
  (*                                                            has_homsets_HSET]) (# F f). *)

  Definition isEpiSig (S : Sig) := preserveEpi (S : functor _ _).

  (* Lemma preserves_to_HSET_isEpi (ax_choice : AxiomOfChoice.AxiomOfChoice_surj) *)
  (*       (B := hset_category)  {C : category} *)
  (*       (G : functor B C) *)
  (*       { a b : B} *)
  (*       (f : (B ⟦ a, b⟧)%Cat) *)
  (*   : isEpi f *)
  (*     -> isEpi (#G f)%Cat. *)
  (* Proof. *)
  (*   intros epif. *)
  (*   apply isSplitEpi_isEpi; [ apply homset_property|]. *)
  (*   apply preserves_isSplitEpi. *)
  (*   apply SplitEpis_HSET; [|apply epif]. *)
  (*   apply ax_choice. *)
  (* Qed. *)
  (* Lemma SigAreEpis (ax_choice : AxiomOfChoice.AxiomOfChoice_surj) (S : Sig) : isEpiSig S. *)
  (* Proof. *)
  (*   intros M N f isepif. *)
  (*   apply is_nat_trans_epi_from_pointwise_epis. *)
  (*   intro a. *)
  (*   eapply preserves_to_HSET_isEpi. *)
  (* Qed. *)





  Local Notation ArToSig ar :=
     (Arity_to_Signature  has_homsets_HSET BinProductsHSET BinCoproductsHSET TerminalHSET ar).

  Local Notation sumSig I Ihset  :=
      (SumOfSignatures.Sum_of_Signatures I HSET hom_SET HSET hom_SET
       (CoproductsHSET I Ihset)).

  Local Notation precompToFunc n :=
    (precomp_option_iter has_homsets_HSET BinCoproductsHSET  TerminalHSET n).

  Local Notation precompToSig n :=
    (precomp_option_iter_Signature has_homsets_HSET BinCoproductsHSET  TerminalHSET n ).

  (* TODO: Si F préserve les épis, alors precomp_functor F aussi *)
  Local Notation precomp_functor  F :=

        (pre_composition_functor SET SET SET hom_SET hom_SET F).
  (* BinProductsHSET BinCoproductsHSET TerminalHSET ar. *)
  Local Notation binProdSig :=
    (BinProductOfSignatures.BinProduct_of_Signatures HSET hom_SET
                                                     HSET hom_SET BinProductsHSET).

  Local Notation binProdFunc := 
      (binproducts.BinProduct_of_functors [HSET, HSET, hom_SET] [HSET, HSET, hom_SET]
       (binproducts.BinProducts_functor_precat HSET HSET BinProductsHSET hom_SET)).

  Local Notation sumFuncs I Ihset :=
    (coproducts.coproduct_of_functors I [HSET, HSET, hom_SET] [HSET, HSET, hom_SET]
       (coproducts.Coproducts_functor_precat I HSET HSET (CoproductsHSET I Ihset) hom_SET)
       ).


  
  Lemma IdSigIsEpiSig : isEpiSig (SignatureExamples.IdSignature HSET has_homsets_HSET).
  Proof.
    intros M N f epif.
    exact epif.
  Qed.

  (* TODO : réfléchir à une généralisation de ce résultat *)
  Lemma preserveEpi_binProdFunc F F' : preserveEpi F -> preserveEpi F' ->
                                       preserveEpi (binProdFunc F F').
  Proof.
    intros epiF epiF'.
    intros M N f epif.
    apply is_nat_trans_epi_from_pointwise_epis.
    intro X.
    set (Ff := (# (binProdFunc F F') f : nat_trans _ _) X).
    cbn in Ff.
    intros Y g h eqfgh.
    (* We use the characterization of surjectivity (easier) *)
    apply funextfun.
    intro x.
    apply (surjectionisepitosets Ff).
    - intros [y y'].
      assert (hF : issurjective ((#F f : nat_trans _ _) X)).
      {
        apply EpisAreSurjective_HSET.
        apply epi_nt_SET_pw.
        apply epiF.
        apply epif.
      }
      assert (hF' : issurjective ((#F' f : nat_trans _ _) X)).
      {
        apply EpisAreSurjective_HSET.
        apply epi_nt_SET_pw.
        apply epiF'.
        apply epif.
      }
      generalize (hF y) (hF' y').
      apply hinhfun2.
      intros z z'.
      apply (hfiberpair _ (pr1 z ,, pr1 z')).
      apply total2_paths2.
      + apply (pr2 z).
      + apply (pr2 z').
    - apply setproperty.
    - apply toforallpaths in eqfgh.
      apply eqfgh.
  Qed.

  (* TODO réfléchir à une généralisation *)

  Lemma preserveEpi_sumFuncs I Ihset Fs (epiFs : ∏ i, preserveEpi (Fs i)) :
    preserveEpi (sumFuncs I Ihset Fs).
  Proof.
    intros M N f epif.
    apply is_nat_trans_epi_from_pointwise_epis.
    intros X Y g h.
    cbn in g,h.
    intros eqgh.
    apply funextfun.
    intros [i x].
    set (g' x := g (i ,, x)).
    set (h' x := h (i ,, x)).
    apply (toforallpaths _ g' h').
    specialize (epiFs i _ _ _ epif).
    eapply epi_nt_SET_pw in epiFs.
    apply epiFs.
    apply funextfun.
    intro y.
    apply toforallpaths in eqgh.
    apply (eqgh (i ,, y)).
  Qed.

  Lemma isEpi_binProdSig S S' : isEpiSig S -> isEpiSig S' -> isEpiSig (binProdSig S S').
  Proof.
    apply (preserveEpi_binProdFunc S S').
  Qed.

  Lemma isEpiSumSigs I Ihset sigs (episigs : ∏ i, isEpiSig  (sigs i)) :
      isEpiSig (sumSig I Ihset sigs).
  Proof.
    apply (preserveEpi_sumFuncs I Ihset sigs episigs).
  Qed.
    

  Lemma precomp_func_preserveEpi F : preserveEpi (precomp_functor F).
  Proof.
    intros M N f epif.
    apply is_nat_trans_epi_from_pointwise_epis.
    intro X.
    apply (epi_nt_SET_pw f epif).
  Qed.

  (** No need for an induction even though the functor is defined as such *)
  Lemma precompEpiFunc (n : nat) : preserveEpi (precompToFunc n).
  Proof.
    destruct n as [|n ].
    - apply IdSigIsEpiSig.
    - apply precomp_func_preserveEpi.
  Qed.

  Lemma precompEpiSig (n : nat) : isEpiSig (precompToSig n).
  Proof.
    apply precompEpiFunc.
  Qed.



  Lemma ArAreEpiSig (ar : list nat) : isEpiSig (ArToSig ar).
  Proof.
    pattern ar.
    apply list_ind; clear ar.
    - exact IdSigIsEpiSig.
    - intros n ar.
      revert n.
      pattern ar.
      apply list_ind; clear ar.
      + intros n epinil.
        cbn.
        apply precompEpiSig.
      + intros n ar HI m epi_ar.
        intros M N f epif.
        unfold ArToSig,  Arity_to_Signature.
        rewrite 2!map_cons.
        rewrite foldr1_cons.
        apply isEpi_binProdSig.
        * apply precompEpiSig.
        * exact epi_ar.
        * exact epif.
  Qed.

  Lemma BindingSigAreEpiSig (S : BindingSig) : isEpiSig (toSig S).
  Proof.
    apply isEpiSumSigs.
    intro i.
    apply ArAreEpiSig.
  Qed.

End EpiAritySig.