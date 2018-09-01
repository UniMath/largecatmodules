(** The category of 2-signatures
The fibration of 2-models over 2-signatures
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

Require Import Modules.Prelims.lib.
Require Import Modules.Signatures.Signature.
Require Import Modules.SoftEquations.ModelCat.
Require Import Modules.Prelims.modules.

Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Section TwoSig.


  Context  {C : category} .
  Local Notation REP := (model (C:=C)).

  Definition TwoSignature := ∑ (S : signature C) (O : UU), O -> equation (Sig := S).

  Coercion OneSig_from_TwoSig (S : TwoSignature) : signature C := pr1 S.

  Definition TwoSignature_index (S : TwoSignature) : UU := pr1 (pr2 S).
  Definition TwoSignature_eqs (S : TwoSignature) : TwoSignature_index S -> equation := pr2 (pr2 S).

  Local Notation EQS := TwoSignature_eqs.

  (* Definition OneSig_Mor_preserves_eqs {S1 S2 : TwoSignature } (m : signature_Mor S1 S2) : UU := *)
  Let SIG_MOR_PRESERVES_EQS {S1 S2 : TwoSignature} (m : signature_Mor S1 S2) :=
    ∏ (R : model_equations (EQS S2)),
    ∏ o, satisfies_equation (EQS S1 o) (pb_rep m R).


  Definition TwoSignature_Mor (S1 S2 : TwoSignature) :=
    ∑ (m : signature_Mor S1 S2),
    SIG_MOR_PRESERVES_EQS m.


  Local Notation  "R →→ S" := (TwoSignature_Mor R S) (at level 6).
  Coercion OneSigMore_from_TwoSigMor {R S} (m : R →→ S) : signature_Mor R S := pr1 m.




  Definition TwoSigMor_preserves_eqs {S1 S2} (m : S1 →→ S2) : 
    SIG_MOR_PRESERVES_EQS m := pr2 m.
    (* ∏ (R : model_equations (EQS S2)), *)
    (* ∏ o, satisfies_equation (EQS S1 o) (pb_rep _ m R) *)
    (* := pr2 m. *)


Lemma TwoSignature_Mor_eq (F F' : TwoSignature)(a a' : TwoSignature_Mor F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  Admitted.

  Definition pb_modeq {S1 S2 : TwoSignature} (m : S1 →→ S2) (R : model_equations (EQS S2)) :
    model_equations (EQS S1) :=
    pb_rep m R ,, TwoSigMor_preserves_eqs m R.
    



  Lemma isaset_TwoSignature_Mor (F F' : TwoSignature) : isaset (F →→ F').
  Proof.
    apply (isofhleveltotal2 2).
    - apply isaset_signature_Mor.
    - intro m.
      apply impred  ; intro .
      apply impred  ; intro .
      apply isasetaprop.
      apply satisfies_equation_isaprop.
  Qed.

Definition TwoSignature_precategory_ob_mor  : precategory_ob_mor := precategory_ob_mor_pair
   TwoSignature (fun F F' => TwoSignature_Mor F F').

Lemma pb_rep_id {S : signature C} (R : model S) :(pb_rep (signature_Mor_id S ) R) = R.
Admitted.

Lemma is_TwoSignature_Mor_id (F : TwoSignature) : SIG_MOR_PRESERVES_EQS (signature_Mor_id F).
Proof.
  intros R .
  rewrite pb_rep_id.
  exact (model_equations_eq R).
Qed.

Definition TwoSignature_Mor_id (F : TwoSignature) : TwoSignature_Mor F F := _ ,, is_TwoSignature_Mor_id F.

Lemma pb_rep_comp {F G H : signature C} (a : signature_Mor F G) (b : signature_Mor G H) (R : REP H) :
   (pb_rep (signature_Mor_comp a b) R) = pb_rep a (pb_rep b R).
Admitted.

Lemma is_TwoSignature_Mor_comp {F G H : TwoSignature} (a : TwoSignature_Mor F G) (b : TwoSignature_Mor G H) 
  : SIG_MOR_PRESERVES_EQS (signature_Mor_comp  a b).
Proof.
  intros R .
  rewrite pb_rep_comp.
  apply (TwoSigMor_preserves_eqs a (pb_modeq b R)).
Qed.

Definition TwoSignature_Mor_comp {F G H : TwoSignature} (a : TwoSignature_Mor F G) (b : TwoSignature_Mor G H)
  : TwoSignature_Mor F H 
  := tpair _ _ (is_TwoSignature_Mor_comp a b).

Definition TwoSignature_precategory_data : precategory_data.
Proof.
  apply (precategory_data_pair (TwoSignature_precategory_ob_mor )).
  + intro a; simpl.
    apply (TwoSignature_Mor_id a).
  + intros a b c f g.
    apply (TwoSignature_Mor_comp f g).
Defined.

Lemma is_precategory_TwoSignature_precategory_data :
   is_precategory TwoSignature_precategory_data.
Proof.
  repeat split; simpl; intros.
  - unfold identity.
    simpl.
    apply TwoSignature_Mor_eq. 
    intro x; simpl.
    apply (id_left (C:=category_LModule _ _)).
  - apply TwoSignature_Mor_eq.
    intro x; simpl.
    apply (id_right (C:=category_LModule _ _)).
  - apply TwoSignature_Mor_eq.
    intro x; simpl.
    apply (assoc (C:=category_LModule _ _)).
Qed.

Definition TwoSignature_precategory : precategory :=
  tpair (fun C => is_precategory C)
        (TwoSignature_precategory_data)
        (is_precategory_TwoSignature_precategory_data).

Lemma TwoSignature_category_has_homsets : has_homsets TwoSignature_precategory.
Proof.
  intros F G.
  apply isaset_TwoSignature_Mor.
Qed.


Definition TwoSignature_category : category.
Proof.
  exists (TwoSignature_precategory).
  apply TwoSignature_category_has_homsets.
Defined.

  










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
  - apply (pb_modeq f R).
  - apply pb_rep_to.
  - simpl in f,R.
    simpl.
    hnf.
    simpl.
    intros.
    use pb_rep_to_cartesian.
Defined.
     
End TwoSig.

