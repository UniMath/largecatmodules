(** The category of 2-signatures
The fibration of 2-models over 2-signatures 
- proof that 2-signatures is a opfibered over the 1-signatures [opfib_two_sig]
- proof that 2-signatures have coequalizers [TwoSignature_Coequalizers] if the base category has
- coproducts of 2-signatures [TwoSignature_Coproducts]
- pushouts of 2-signatures [TwoSignature_Pushouts]
 *)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.FaithfulFibrationEqualizer.
Require Import Modules.Signatures.Signature.
Require Import Modules.SoftEquations.ModelCat.
Require Import Modules.Prelims.modules.

Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.Opfibration.
Require Import Modules.Prelims.PushoutsFromCoeqBinCoproducts.
Require Import Modules.Prelims.BinCoproductComplements.
Require Import Modules.Signatures.SignaturesColims.
Require Import Modules.Signatures.SignatureCoproduct.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.

Section TwoSig.

  Context  {C : category} .


Lemma pb_rep_id {S : signature C} (R : model S) : pb_rep (signature_Mor_id S)  R = R.
Proof.
  apply pair_path_in2.
  apply (id_left (C := category_LModule _ _)).
Defined.

Lemma pb_rep_comp {F G H : signature C} (a : signature_Mor F G) (b : signature_Mor G H) (R : model H) :
   (pb_rep (compose (C := signature_category) a b) R) = pb_rep a (pb_rep b R).
Proof.
  apply pair_path_in2.
  cbn -[compose].
  apply pathsinv0.
  apply (assoc (C := category_LModule _ _)).
Defined.

Definition two_signature_disp_ob_mor : disp_cat_ob_mor (signature_category (C := C)) :=
  mk_disp_cat_ob_mor
    signature_category
    (fun (S : signature C) => ∑ (O : UU), O -> equation (Sig := S))
    (fun (S1 S2 : signature C) SS1 SS2 (f : signature_Mor S1 S2) =>
       (** forall for hprop *)
       ∀ (R : model_equations (pr2 SS2)) o ,
         satisfies_equation_hp (pr2 SS1 o) (pb_rep f R)).


(** The pullback model with equations *)
Definition pb_modeq {S1 S2 : signature C} {m : signature_Mor S1 S2}
           {SS1 : two_signature_disp_ob_mor S1}
           {SS2 : two_signature_disp_ob_mor S2}
           (mm: SS1 -->[ m ] SS2) (R : model_equations (pr2 SS2))
           : model_equations (pr2 SS1) :=
    pb_rep m R ,, mm R.


Lemma two_signature_identity_Mor (x : signature_category) (xx : two_signature_disp_ob_mor x)
      : xx -->[ identity x] xx.
Proof.
  intros R o.
  unfold identity; cbn.
  eapply (transportb (satisfies_equation _)).
  apply pb_rep_id.
  apply (model_equations_eq R o).
Qed.

Lemma two_signature_comp_Mor 
  (x y z : signature_category) (f : signature_category ⟦ x, y ⟧) (g : signature_category ⟦ y, z ⟧)
  (xx : two_signature_disp_ob_mor x) (yy : two_signature_disp_ob_mor y) (zz : two_signature_disp_ob_mor z) :
  xx -->[ f] yy → yy -->[ g] zz → xx -->[ f · g] zz.
Proof.
  intros hf hg.
  intros R .
  rewrite pb_rep_comp.
  apply (hf (pb_modeq hg R)).
Qed.


Definition two_signature_data : disp_cat_data (signature_category (C:= C)) :=
   two_signature_disp_ob_mor ,, (two_signature_identity_Mor ,, two_signature_comp_Mor).


Lemma two_signature_axioms : disp_cat_axioms _ two_signature_data.
Proof.
  repeat apply tpair; intros;  try apply Propositions.proofirrelevance_hProp.
  apply isasetaprop; apply propproperty.
Qed.

Definition two_signature_disp : disp_cat _ := two_signature_data ,, two_signature_axioms.

Definition opfib_two_sig : opcleaving two_signature_disp.
Proof.
  intros S S' f SS'.
  red.
  use tpair;[|use tpair].
  - eapply tpair.
    exact ( fun (o : pr1 SS') => po_equation f (pr2 SS' o)).
  - exact model_equations_eq.
  - red.
    intros S2 f2 e2 hf2.
    unshelve eapply unique_exists;
      [| | intros; eapply isapropifcontr,propproperty |
       intros; eapply proofirrelevance,propproperty].
    + intros R o.
      specialize (hf2 R o).
      rewrite pb_rep_comp in hf2.
      exact hf2.
    + apply proofirrelevance.
      apply propproperty.
Defined.


Definition TwoSignature_category : category :=  total_category  two_signature_disp.

Definition TwoSignature := ob TwoSignature_category.
Definition TwoSignature_Mor (S1 S2 : TwoSignature) := TwoSignature_category ⟦S1 , S2⟧.

Coercion OneSig_from_TwoSig (S : TwoSignature) : signature C := pr1 S.



Definition TwoSignature_index (S : TwoSignature) : UU := pr1 (pr2 S).
Definition TwoSignature_eqs (S : TwoSignature) : TwoSignature_index S -> equation := pr2 (pr2 S).

(** If thebase category has coequalizers, then the total two-sig category also *)
Lemma TwoSignature_Coequalizers
      (coeq : colimits.Colims_of_shape Coequalizer_graph  C)
  : Coequalizers TwoSignature_category.
Proof.
  red.
  intros S1 S2 f g.
  apply (faithful_opfibration_coequalizer _ opfib_two_sig).
  - apply faithful_pr1_category.
    intros; apply propproperty.
  - apply Sig_Colims_of_shape.
    exact coeq.
Defined.

Definition two_signature_coproduct
  {O : UU}
  (c : Coproducts O C)
  (sigs : O → TwoSignature_category) : TwoSignature.
Proof.
  use tpair.
  + apply (signature_Coproduct (cpC := c) ).
    apply sigs.
  + cbn.
    refine ((∑ (o : O), TwoSignature_index (sigs o)),, _).
    intros oo.
    eapply po_equation; revgoals.
    * apply (TwoSignature_eqs (sigs (pr1 oo)) (pr2 oo)).
    * exact ( CoproductIn  _ _ (signature_Coproduct (cpC := c) _) (pr1 oo)).
Defined.

Definition two_signature_coproduct_in
  {O : UU}
  (c : Coproducts O C)
  (sigs : O → TwoSignature_category) 
  (i : O) : 
  TwoSignature_category ⟦ sigs i, two_signature_coproduct c sigs ⟧.
Proof.
  use tpair.
  + exact ( CoproductIn  _ _ (signature_Coproduct (cpC := c) _) i).
  + cbn.
    intros R o.
    apply (model_equations_eq R (i ,, o)).
Defined.

Lemma two_signature_is_coproduct 
  {O : UU}
  (c : Coproducts O C)
  (sigs : O → TwoSignature_category)  :
  isCoproduct O TwoSignature_category sigs (two_signature_coproduct c sigs) (two_signature_coproduct_in c sigs).
Proof.
  intros S fS.
  use unique_exists.
  - use tpair.
    + use (CoproductArrow _ _  (signature_Coproduct (cpC := c) _)).
      apply fS.
    + cbn.
      intros R oo.
      hnf.
      cbn.
      set (he1 := halfeq1 _).
      set (he2 := halfeq2 _).
      set (r := pb_rep _ _).
      change ((fun z => he1 z  = he2 z ) r).
      eapply transportf.
      * etrans;[| apply pb_rep_comp].
        set (ff := compose _ _).
        pattern ff.
        eapply transportb.
        apply (CoproductInCommutes _ _ _  (signature_Coproduct (cpC := c) _) _ (fun i => pr1 (fS i))).
        apply idpath.
      * exact(  pr2 (fS (pr1 oo)) R (pr2 oo)).
  - intro i.
    apply subtypeEquality_prop.
    apply (CoproductInCommutes _ _ _  (signature_Coproduct (cpC := c) _) _ (fun i => pr1 (fS i))).
  - cbn beta .
    intro.
    apply impred_isaprop.
    intro.
    apply homset_property.
  - intros y hi.
    apply subtypeEquality_prop.
    apply (CoproductArrowUnique _ _ _  (signature_Coproduct (cpC := c) _) _ (fun i => pr1 (fS i))).
    intro i.
    specialize (hi i).
    apply (base_paths _ _ hi).
Defined.

Lemma TwoSignature_Coproducts {O : UU}
      (c : Coproducts O C)
  : Coproducts O TwoSignature_category.
Proof.
  intros sigs.
  use mk_Coproduct.
  - exact (two_signature_coproduct c sigs).
  - exact (two_signature_coproduct_in c sigs).
  - apply two_signature_is_coproduct.
Defined.

Lemma TwoSignature_Pushouts 
      (b : BinCoproducts C)
    (coeq : colimits.Colims_of_shape Coequalizer_graph  C)
  : Pushouts  TwoSignature_category.
Proof.
  apply pushouts_from_coeq_bincoprod; revgoals.
  - apply TwoSignature_Coequalizers.
    apply coeq.
  - apply BinCoproducts_from_CoproductsBool.
    apply TwoSignature_Coproducts.
    apply CoproductsBool;[apply homset_property|].
    exact b.
Defined.

Local Notation EQS := TwoSignature_eqs.

Local Notation  "R →→ S" := (TwoSignature_Mor R S) (at level 6).
Coercion OneSigMore_from_TwoSigMor {R S} (m : R →→ S) : signature_Mor R S := pr1 m.


Lemma TwoSignature_Mor_eq (F F' : TwoSignature)(a a' : TwoSignature_Mor F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro h.
  apply subtypeEquality_prop.
  apply signature_Mor_eq.
  exact h.
Qed.

    








(* now the cleaving *)






Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).
  

(* Signatures are display functors over the identity *)
Local Notation PRECAT_SIGNATURE  := (@signature_precategory C).

Notation signature  := (@signature C).


Local Notation Θ := tautological_LModule.


  (* We define the displayed category of models of a signature
We could also define it as a displayed category over the monads
and we have no idea what that would look like *)


(** A model is a monad with a module morphisme from its image by the signature
 to itself *)
Definition two_model (ar : TwoSignature) := model_equations  (EQS ar).
Identity Coercion  two_model_to_model_equations  : two_model  >-> model_equations .


(* Let rep_ar_mor_mor (a b : SIGNATURE) (M : rep_ar a) (N : rep_ar b) f := *)

Definition two_model_disp_ob_mor : disp_cat_ob_mor TwoSignature_category.
  exists two_model.
  refine ( fun (a b : TwoSignature) M N (f : a →→ b) => model_mor_mor a b M N f).
Defined.


Definition two_mod_data : disp_cat_data TwoSignature_category.
  exists two_model_disp_ob_mor.
  split.
  + intros; apply rep_id.
  + intros ????????.
    apply rep_comp.
Defined.

Lemma transport_signature_mor (x y : TwoSignature) (f g :  x →→ y)
      (e : f = g)
      (xx : two_model_disp_ob_mor x)
      (yy : two_model_disp_ob_mor y)
      (ff : xx -->[ f] yy)
      (c : C) :
  pr1 (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 (pr1 ff) c.
Proof.
  induction e.
  apply idpath.
Qed.



Lemma two_mod_axioms : disp_cat_axioms _ two_mod_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  - apply model_mor_mor_equiv.
    intros c.
    etrans. apply id_left.
    symmetry.
    apply transport_signature_mor.
  - apply model_mor_mor_equiv.
    intro c.
    etrans. apply id_right.
    symmetry.
    apply transport_signature_mor.
  - set (heqf:= assoc f g h).
    apply model_mor_mor_equiv.
    intros c.
    etrans. Focus 2.
      symmetry.
      apply transport_signature_mor.
      cbn.
      rewrite assoc.
      apply idpath.
  - apply isaset_model_mor_mor.
Qed.

Definition two_model_disp : disp_cat _ := two_mod_data ,, two_mod_axioms.



(** ** Now the cleaving *)

Lemma two_mod_cleaving : cleaving two_model_disp.
Proof.
  intros a a' f R.
  red.
  use tpair;[ |use tpair].
  - apply (pb_modeq (pr2 f) R).
  - apply pb_rep_to.
  - simpl in f,R.
    simpl.
    hnf.
    simpl.
    intros.
    use pb_rep_to_cartesian.
Defined.
     
End TwoSig.


(** Colimits in the specific case of SET.
In fact, from coequalizers and coproducts, we could construct any colimits *)
Definition TwoSignature_CoequalizersSET : Coequalizers (TwoSignature_category (C := SET)) :=
  TwoSignature_Coequalizers (C := SET) (ColimsHSET_of_shape _).

Definition TwoSignature_CoproductsSET (O : hSet) : Coproducts O (TwoSignature_category (C := SET)) :=
  TwoSignature_Coproducts (C := SET) (CoproductsHSET _ (setproperty O)).

Definition TwoSignature_PushoutsSET : Pushouts (TwoSignature_category (C := SET)) :=
  TwoSignature_Pushouts (C := SET) BinCoproductsHSET (ColimsHSET_of_shape _).
