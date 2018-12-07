(* We show that the bin product of a presentable  signature with the tautological  signature
is presentable (actually it is also true of any bin products of presentable  arities)

- if a category is distributive, then the functor category  also, the
Left module category also and the ()-signature category as well.
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.

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
Require Import Modules.Signatures.SignaturesColims.
Require Import Modules.Signatures.PresentableSignatureCoproducts.
Require Import Modules.Signatures.HssSignatureCommutation.


Require Import Modules.Prelims.LModulesBinProducts.
Require Import Modules.Prelims.LModulesCoproducts.
Require Import Modules.Prelims.BinProductComplements.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
(* Require Import Modules.Signatures.FullArToRaw. *)
Open Scope cat.


(* inspiré de PresentableSignatureCoproducts pour les coproduits *)
(* TODO faire une section à part *)

Section CoprodAr.
  Context {C : category} (bp : BinProducts C) (bcp : BinCoproducts C)
          (T : Terminal C) (cp : ∏ (I:hSet), Coproducts I C).

  Local Notation PO := (BinProductObject _). Local Notation CPO := (CoproductObject _ _).
  Let MOD R  := precategory_LModule (B:= C) R C.
  Let Sig_bp := signature_BinProducts  bp.
  Let Sig_cp I := signature_Coproducts  (cp I).

  Let bpFunct :=
    (BinProducts_functor_precat C C bp (homset_property C)).
  Let cpFunct (Z : hSet) :=
    (Coproducts_functor_precat Z C C (cp Z) (homset_property C)).

  Let bpMOD (R : Monad C) :=
    (LModule_BinProducts R bp (homset_property C)).

  Let cpMOD (R : Monad C) (Z : hSet) :=
    (LModule_Coproducts C R (cp Z) ).



  Let toSig sig :=
    (BindingSigToSignature (homset_property _) bp
                           bcp T sig
                           (cp ((BindingSigIndexhSet sig)) )).


  (** * distributivity lifts to functor categories, left modules categories, signature category

TODO move these lemmas in a different file
   *)
Hypothesis (isDistC : ∏ (I : hSet) , bp_coprod_isDistributive bp
                                         (cp I)).
(* TODO déplacer ces lemms qq part *)
Lemma functor_cat_isDistributive (Z : hSet) (R : Monad C) :
  bp_coprod_isDistributive
    (C :=  [C,C])
    (bpFunct)
    (cpFunct Z)  .
Proof.
  intros B X.
  apply functor_iso_if_pointwise_iso.
  intro c.
  apply isDistC.
Defined.

Lemma LMod_isDistributive_inv_laws (Z :hSet) (R : Monad C) B (X : LModule _ _) :
  LModule_Mor_laws R (T := PO (bpMOD R (CPO (cpMOD R Z B)) X) : LModule _ _)
                   (T' := CPO (cpMOD R Z (fun o => PO (bpMOD R _ _) )):LModule _ _)
                   (inv_from_iso
                           (iso_from_isDistributive _ _
                                                    (functor_cat_isDistributive Z R )
                                                    (fun z => (B z : LModule _ _) : functor _ _)
                                                    (X : functor _ _))).
Proof.
  intro c.
  cbn.
  repeat rewrite id_right.
  unfold LModule_coproduct_mult_data; cbn.
  apply iso_inv_on_right.
  rewrite assoc.
  apply iso_inv_on_left.
  set (i :=   bp_coprod_mor (cpMOD R _ B)
                            (fun o => bpMOD R _ _) (bpMOD R _ X) (cpMOD R _ _)).
  apply  ( LModule_Mor_σ R i).
Qed.

Definition LMod_isDistributive_inv (Z :hSet) (R : Monad C) B (X : LModule _ _) :
  LModule_Mor R
              (PO (bpMOD R (CPO (cpMOD R Z B)) X) : LModule _ _)
              (CPO (cpMOD R Z (fun o => PO (bpMOD R _ _) )):LModule _ _) :=
  _ ,, LMod_isDistributive_inv_laws Z R B X.

Lemma LMod_isDistributive_is_inverse (Z : hSet) R B X :
  is_inverse_in_precat
    (bp_coprod_mor (LModule_Coproducts C R (cp Z) B)
       (λ o : Z, LModule_BinProducts R bp (homset_property C) (B o) X)
       (LModule_BinProducts R bp (homset_property C) (CPO (LModule_Coproducts C R (cp Z) B)) X)
       (LModule_Coproducts C R (cp Z)
          (λ o : Z, PO (LModule_BinProducts R bp (homset_property C) (B o) X))))
    (LMod_isDistributive_inv Z R B X).
Proof.
    set (h := (iso_from_isDistributive _ _
                                          (functor_cat_isDistributive Z R)
                                          ((B : Z -> LModule _ _) : Z -> functor _ _)
                                          ((X : LModule _ _) : functor _ _)
                 )).
    split; apply LModule_Mor_equiv; try apply homset_property.
    + cbn; apply (iso_inv_after_iso h).
    + cbn; apply (iso_after_iso_inv h).
Qed.

Lemma LMod_isDistributive (Z : hSet) (R : Monad C) :
  bp_coprod_isDistributive
    (C :=  MOD R)
    (LModule_BinProducts R bp (homset_property C))
    (LModule_Coproducts C R (cp Z) )  .
Proof.
  intros B X.
  eapply is_iso_qinv.
  apply LMod_isDistributive_is_inverse.
Defined.

(* TODO : déplacer ce lemme qq part *)
Lemma Sig_isDistributive_inv_law (Z :hSet) (X : signature C) (B : Z -> signature C) :
  is_signature_Mor  (PO (Sig_bp  (CPO (Sig_cp  Z B)) X) : signature _ )
                   ( CPO (Sig_cp  Z (fun o => PO (Sig_bp  _ _) )):signature _)
                   (fun R => LMod_isDistributive_inv Z R (fun z => B z R) (X R)).
Proof.
  intros R S f.
    set (h := fun R => (iso_from_isDistributive _ _
                                          (functor_cat_isDistributive Z R)
                                          (fun z => B z R : functor _ _)
                                          ((X R : LModule _ _) : functor _ _)
                 )).
    apply pathsinv0.
  apply (iso_inv_on_right  _ _ _ _ (h R)).
  rewrite assoc.
  apply (iso_inv_on_left _ _ _ _ _ (h S)).
  set  (i :=   bp_coprod_mor (Sig_cp _ B)
                            (fun o => Sig_bp _ _) (Sig_bp _ X) (Sig_cp  _ _)).
  apply pathsinv0.
  apply (signature_Mor_ax i f) .
Qed.

Definition Sig_isDistributive_inv (Z :hSet) (X : signature C) (B : Z -> signature C) :
  signature_Mor  (PO (Sig_bp  (CPO (Sig_cp  Z B)) X) : signature _ )
             ( CPO (Sig_cp  Z (fun o => PO (Sig_bp  _ _) )):signature _) :=
  _ ,, Sig_isDistributive_inv_law Z X B.

Lemma Sig_isDistributive_is_inverse (Z : hSet) (B : Z -> signature C) (X :signature C) :
  is_inverse_in_precat
    (bp_coprod_mor (Sig_cp Z B)
       (λ o : Z, Sig_bp (B o) X)
       (Sig_bp (CPO (Sig_cp ( Z) B)) X)
       (Sig_cp Z (λ o : Z, PO (Sig_bp  (B o) X))))
    (Sig_isDistributive_inv Z X B).
Proof.
    set (h := fun R => (iso_from_isDistributive _ _
                                          (LMod_isDistributive Z R)
                                          (fun z => B z R  )
                                          ((X R : LModule _ _) )
                 )).
    set (h' := fun R => (iso_from_isDistributive _ _
                                          (functor_cat_isDistributive Z R)
                                          (fun z => B z R : functor _ _)
                                          ((X R : LModule _ _) : functor _ _)
                 )).
    split; apply signature_Mor_eq;   intro R; apply LModule_Mor_equiv;
    try apply homset_property.
    + cbn; apply (iso_inv_after_iso (h' R)).
    + cbn; apply (iso_after_iso_inv (h' R)).
Qed.

Lemma Sig_isDistributive (Z : hSet)  :
  bp_coprod_isDistributive
    (C :=  signature_precategory )
    Sig_bp
    (Sig_cp  Z).
Proof.
  intros B X.
  eapply is_iso_qinv.
  apply Sig_isDistributive_is_inverse.
Defined.
  (** * The product of a presentable signature with the tautological signature is presentable 

It requires that the base category is distributive and that bin products
of epimorphisms are epimorphisms in the functor category.

*)
Definition isEpiBinProd :=
   ∏ (X X' Y Y' : functor C C) (f : nat_trans X X') (g : nat_trans Y Y')
                        (epif : isEpi (C :=  [C,C]) f)(epig : isEpi (C :=  [C,C]) g),
                      isEpi (C:=[C,C]) (BinProductOfArrows _ (bpFunct _ _)
                                                           (bpFunct _ _) f g).

Hypothesis
  (epiBinProd : isEpiBinProd).


  Context {a : signature C} .
  Context (pres_a : isPresentable bp bcp T cp a).
  Let Ba : BindingSig := p_sig pres_a.
  Let I : hSet := BindingSigIndexhSet Ba.
  Let Sa' : I -> list nat := BindingSigMap Ba.

  Let Fa :  signature_Mor (hss_to_ar (C:= C) (toSig Ba)) a := p_mor pres_a.
  Let epiFa : ∏ (R : Monad C), (isEpi (C := [_, _]) (pr1 (Fa R))) :=
    epi_p_mor pres_a.


  Local Notation SIG := (Signature_precategory C C).


  (**
[[ a_1, a_2,.. ] , [b_1, b_2, ...], ..]
becomes
[[0 , a_1, a_2,.. ] , [0 , b_1, b_2, ...], ..]
*)
  Let b : signature _ := PO (Sig_bp a tautological_signature).
  Definition har_binprodR_p_sig : BindingSig :=
    mkBindingSig (BindingSigIsaset (p_sig pres_a))
                 (λ i : BindingSigIndex (p_sig pres_a), cons 0 (BindingSigMap (p_sig pres_a) i)).

  Let p_alg_ar' := hss_to_ar (C:=C) (toSig har_binprodR_p_sig).


  Let FuncCP :=
    Coproducts_functor_precat  (BindingSigIndex (p_sig pres_a))
                               C C (cp (BindingSigIndexhSet (p_sig pres_a)))
                               (homset_property _).

  Let FuncBP :=
    BinProducts_functor_precat  
                               C C bp
                               (homset_property _).



  Let cpSig  : Coproducts I SIG
    := Coproducts_Signature_precategory _ C _ (cp I).
  Let bpSig  : BinProducts  SIG
    := BinProducts_Signature_precategory _ C  bp.

  (* TODO : move this somewhere else *)
  Lemma Const1Sig_isTerminal : isTerminal SIG (SignatureExamples.ConstConstSignature C C T).
  Proof.
    intro S.
    use iscontrpair.
    - use tpair.
      {
      use mk_nat_trans.
      + intro x.
        use mk_nat_trans.
        * intro c.
          apply TerminalArrow.
        * intros z z' f.
          etrans;[apply TerminalArrowUnique|]; apply pathsinv0; apply TerminalArrowUnique.
      + intros c c' f.
        apply nat_trans_eq; [  apply homset_property|]. 
        intro z.
          etrans;[apply TerminalArrowUnique|]; apply pathsinv0; apply TerminalArrowUnique.
      }
      cbn.
      intros X Y .
      apply nat_trans_eq; [  apply homset_property|]. 
      intro z.
      etrans;[apply TerminalArrowUnique|]; apply pathsinv0; apply TerminalArrowUnique. 
    - intros f.
      apply SignatureMor_eq.
      apply nat_trans_eq; [  apply (homset_property [C,C])|]. 
      intro z.
      apply nat_trans_eq; [  apply homset_property|]. 
      intro z'.
      apply TerminalArrowUnique.
  Defined.

  Definition TerminalSignature : Terminal SIG := mk_Terminal _ Const1Sig_isTerminal.




  Lemma Signature_to_signature_cons_iso n ar :
    iso (C := SIG) ( (Arity_to_Signature (homset_property C) bp bcp T (cons n ar)))
        (BinProductObject _ (bpSig 
                               (precomp_option_iter_Signature (homset_property C) bcp T n)
                               (Arity_to_Signature (homset_property C) bp bcp T ar)
        )).
  Proof.
    apply iso_inv_from_iso.
    revert  n.
    pattern ar.
    apply list_ind; clear ar.
    - intro n.
      cbn -[bpSig].
      apply (BinProductWith1_iso  (TerminalSignature) (bpSig _ _)).
    - intros n ar .
      (* revert n. *)
      intros HI n2.
      apply identity_iso.
  Defined.

  



Definition har_binprodR_commute_mor_mod 
  :  iso (C := signature_category)  (p_alg_ar' )
                ((PO (Sig_bp (hss_to_ar (C := C) (toSig Ba)) tautological_signature) : signature C)
                ) .
Proof.
  unfold p_alg_ar'.
  eapply iso_comp.
  {
    (* apply morphism_from_iso. *)
    eapply iso_comp;[ apply coprod_sigs_har_iso|].
    eapply iso_comp.
    {
      eapply (coprod_pw_iso (C:=signature_category) _ (Sig_cp  I _)).
      intro o.
      eapply iso_comp.
      {
        eapply (functor_on_iso (hss_to_ar_functor)).
        apply Signature_to_signature_cons_iso.
      }
      eapply (iso_comp (C := signature_category)).
      - apply binprod_sigs_har_iso.
      - apply BinProduct_commutative_iso.
      (* - apply binprod_sigs_har_iso. *)
      (* - apply binprod_sigs_har_iso. *)
      (* (* eapply iso_comp. *) *)
      (* - apply binprod_sigs_har_iso. *)
      (* - apply BinProduct_commutative_iso. *)
    }

    apply (iso_from_isDistributive (C:=signature_category)).
    apply Sig_isDistributive.
  }
  apply BinProduct_pw_iso.
  - apply iso_inv_from_iso.
    (* eapply iso_comp. *)
    (* + eapply (functor_on_iso hss_to_ar_functor). *)
    (*   apply Signature_to_signature_fold_iso. *)
    apply coprod_sigs_har_iso.
  - apply tauto_sigs_har_iso.
Defined.

  Definition har_binprodR_p_mor  : signature_Mor p_alg_ar' b.
    eapply (compose (C := signature_precategory)).
    - apply har_binprodR_commute_mor_mod.
    - apply BinProductOfArrows.
      + apply Fa.
      + apply identity.
  Defined.

  Lemma har_binprodR_epi_p_mor
        (R : Monad C) : isEpi (C := [_,_])
                                                     (har_binprodR_p_mor R : nat_trans _ _).
  Proof.
    apply (isEpi_comp ([C,C]) ((morphism_from_iso _ _ _ har_binprodR_commute_mor_mod
                        : signature_Mor _ _) R : nat_trans _ _)).
    - apply is_iso_isEpi.
      apply is_z_iso_from_is_iso.
      set (i := functor_on_iso (forget_Sig R) har_binprodR_commute_mor_mod).
       apply ( (functor_on_iso_is_iso _ _ (LModule_forget_functor R C)) _ _ i).
    - apply epiBinProd.
      + apply epiFa.
      + apply identity_isEpi.
  Qed.

  Definition har_binprodR_isPresentable : isPresentable bp bcp T cp b :=
    _ ,, _ ,, har_binprodR_epi_p_mor.

End CoprodAr.
