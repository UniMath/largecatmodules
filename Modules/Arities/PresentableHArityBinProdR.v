(* We show that the bin product of a presentable half arity with the tautological half arity
is presentable (actually it is also true of any bin products of presentable half arities)

- if a category is distributive, then the functor category  also, the
Left module category also and the (half)-arity category as well.
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
Require Import Modules.Prelims.modules.


Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.HssToArity.
Require Import Modules.Arities.BindingSig.
Require Import Modules.Arities.PresentableArity.
Require Import Modules.Arities.HArityBinproducts.
Require Import Modules.Arities.HArityCoproduct.
Require Import Modules.Arities.PresentableHArityCoproducts.
Require Import Modules.Arities.HssArityCommutation.

Require Import Modules.Prelims.LModPbCommute.
Require Import Modules.Prelims.LModuleBinProduct.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Prelims.BinProductComplements.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Open Scope cat.


(* inspiré de PresentableHArityCoproducts pour les coproduits *)
(* TODO faire une section à part *)

Section CoprodAr.
  Context {C : category} (bp : BinProducts C) (bcp : BinCoproducts C)
          (T : Terminal C) (cp : ∏ (I:hSet), Coproducts I C).

  Local Notation PO := (BinProductObject _).
  Local Notation CPO := (CoproductObject _ _).
  Let MOD R  := precategory_LModule (B:= C) R C.
  Let HAr_bp := harity_BinProducts  bp.
  Let HAr_cp I := harity_Coproducts  (cp I).

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


  (** * distributivity lifts to functor categories, left modules categories, arity category

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
    + cbn;now apply (iso_inv_after_iso h).
    + cbn;now apply (iso_after_iso_inv h).
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
Lemma HAr_isDistributive_inv_law (Z :hSet) (X : arity C) (B : Z -> arity C) :
  is_arity_Mor  (PO (HAr_bp  (CPO (HAr_cp  Z B)) X) : arity _ )
                   ( CPO (HAr_cp  Z (fun o => PO (HAr_bp  _ _) )):arity _)
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
  set  (i :=   bp_coprod_mor (HAr_cp _ B)
                            (fun o => HAr_bp _ _) (HAr_bp _ X) (HAr_cp  _ _)).
  apply pathsinv0.
  apply (arity_Mor_ax i f) .
Qed.

Definition HAr_isDistributive_inv (Z :hSet) (X : arity C) (B : Z -> arity C) :
  arity_Mor  (PO (HAr_bp  (CPO (HAr_cp  Z B)) X) : arity _ )
             ( CPO (HAr_cp  Z (fun o => PO (HAr_bp  _ _) )):arity _) :=
  _ ,, HAr_isDistributive_inv_law Z X B.

Lemma HAr_isDistributive_is_inverse (Z : hSet) (B : Z -> arity C) (X :arity C) :
  is_inverse_in_precat
    (bp_coprod_mor (HAr_cp Z B)
       (λ o : Z, HAr_bp (B o) X)
       (HAr_bp (CPO (HAr_cp ( Z) B)) X)
       (HAr_cp Z (λ o : Z, PO (HAr_bp  (B o) X))))
    (HAr_isDistributive_inv Z X B).
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
    split; apply arity_Mor_eq;   intro R; apply LModule_Mor_equiv;
    try apply homset_property.
    + cbn;now apply (iso_inv_after_iso (h' R)).
    + cbn;now apply (iso_after_iso_inv (h' R)).
Qed.

Lemma HAr_isDistributive (Z : hSet)  :
  bp_coprod_isDistributive
    (C :=  arity_precategory )
    HAr_bp
    (HAr_cp  Z).
Proof.
  intros B X.
  eapply is_iso_qinv.
  apply HAr_isDistributive_is_inverse.
Defined.
  (** * The product of a presentable arity with the tautological arity is presentable 

It requires that the base category is distributive and that bin products
of epimorphisms are epimorphisms in the functor category.

Let us redefine a hss bidning signature to be a list of pairs of a nat and a list (ie
a list of non empty lists !!

because otherwise [[] ]~ [[0]] which is ugly and not convenient

*)
Hypothesis
  (epiBinProd : ∏ (X X' Y Y' : functor C C) (f : nat_trans X X') (g : nat_trans Y Y')
                        (epif : isEpi (C :=  [C,C]) f)(epig : isEpi (C :=  [C,C]) g),
                      isEpi (C:=[C,C]) (BinProductOfArrows _ (bpFunct _ _)
                                                           (bpFunct _ _) f g)).


  Context {a : arity C} 
          {I : hSet}
          (Sa : I -> (nat × list nat)).
  Let Sa' := fun i => cons (pr1 (Sa i)) (pr2 (Sa i)).
  Let Ba : BindingSig := mkBindingSig (setproperty I) Sa'.

  

  Context (Fa :  arity_Mor (hss_to_ar (C:= C) (toSig Ba)) a)
          (epiFa : ∏ (R : Monad C), (isEpi (C := [_, _]) (pr1 (Fa R)))).

  Let pres_a : isPresentable bp bcp T cp a := Ba ,, Fa ,, epiFa.

  Local Notation SIG := (Signature_precategory C C).


  (**
[[ a_1, a_2,.. ] , [b_1, b_2, ...], ..]
becomes
[[0 , a_1, a_2,.. ] , [0 , b_1, b_2, ...], ..]
*)
  Let b : arity _ := PO (HAr_bp a tautological_harity).
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


Definition Arity_to_Signature_cons_cons_value x y l :=
  PO (BinProducts_Signature_precategory C C
                           bp
                           (precomp_option_iter_Signature (homset_property C) bcp T x)
                           (Arity_to_Signature (homset_property C) bp bcp T (cons y l))).

Definition Arity_to_Signature_cons_cons x y l :
  Arity_to_Signature (homset_property C) bp bcp T (cons x (cons y l)) =
  BinProduct_of_Signatures _ (homset_property C) C (homset_property C)
                           bp
                           (precomp_option_iter_Signature (homset_property C) bcp T x)
                           (Arity_to_Signature (homset_property C) bp bcp T (cons y l)) := idpath _.

Definition Arity_to_signature_cons_cons_value' o :=
  Arity_to_Signature_cons_cons_value 0 (pr1 (Sa o)) (pr2 (Sa o)).


Let ar1: arity _ := (CPO 
       (HAr_cp _
          (λ i : BindingSigIndex har_binprodR_p_sig,
           hss_to_ar
             (Arity_to_Signature_cons_cons_value 0 (pr1 (Sa i)) (pr2 (Sa i)))
        ))).
Let ar2 := (PO (HAr_bp (hss_to_ar (C := C) (toSig Ba)) tautological_harity) : arity C).

Let ar1i i :=
     (hss_to_ar (Arity_to_Signature_cons_cons_value 0 (pr1 (Sa i)) (pr2 (Sa i)))).

  Let cpSig  : Coproducts I SIG
    := Coproducts_Signature_precategory _ C _ (cp I).

  



Definition har_binprodR_commute_mor_mod 
  :  iso (C := arity_category)  (p_alg_ar' )
                ((PO (HAr_bp (hss_to_ar (C := C) (toSig Ba)) tautological_harity) : arity C)
                ) .
Proof.
  unfold p_alg_ar'.
  eapply iso_comp.
  {
    (* apply morphism_from_iso. *)
    eapply iso_comp;[ apply coprod_sigs_har_iso|].
    eapply iso_comp.
    {
      eapply (coprod_pw_iso (C:=arity_category) _ (HAr_cp  _ _)).
      intro o.
      set (aa := Arity_to_Signature _ _ _ _ _ ).
      change aa with (Arity_to_signature_cons_cons_value' o).
      eapply iso_comp.
      - apply binprod_sigs_har_iso.
      - apply BinProduct_commutative_iso.
    }

    apply (iso_from_isDistributive (C:=arity_category)).
    apply HAr_isDistributive.
  }
  apply BinProduct_pw_iso.
  - apply iso_inv_from_iso.
    apply coprod_sigs_har_iso.
  - apply tauto_sigs_har_iso.
Defined.

  Definition har_binprodR_p_mor  : arity_Mor p_alg_ar' b.
    eapply (compose (C := arity_precategory)).
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
                        : arity_Mor _ _) R : nat_trans _ _)).
    - apply is_iso_isEpi.
      apply is_z_iso_from_is_iso.
      set (i := functor_on_iso (forget_HAr R) har_binprodR_commute_mor_mod).
       apply ( (functor_on_iso_is_iso _ _ (forget_LMod R C)) _ _ i).
    - apply epiBinProd.
      + apply epiFa.
      + apply identity_isEpi.
  Qed.

  Definition har_binprodR_isPresentable : isPresentable bp bcp T cp b :=
    _ ,, _ ,, har_binprodR_epi_p_mor.

End CoprodAr.

