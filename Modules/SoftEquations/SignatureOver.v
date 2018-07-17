(* =================================================================================== *)
(** * Soft Σ-modules

    Content:
    - Definition of a signature (aka soft Σ-module) over the category of another signature Σ

I am faced with a dilemna. Mathematically, a soft Σ-module is a functor from the category
of models of Σ to the total category of modules, preserving the underlying monad.
The source category is the fiber over Σ of the displayed category of representations.
Morphisms are displayed morphism over the identity signature morphism. Hence composition
does not work well, because the composition of two morphisms  x ->[id] y and y ->[id] z 
yield a morphism x ->[id ; id] z

Our solution: re-define directly the category of models of a signature (Cf ModelCat)

TODO : factor this definition and the standard definition of signatures ?
(a lot of stuff was indeed copied and pasted from Signature.v
*)
(* =================================================================================== *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.

Require Import Modules.Signatures.Signature.
Require Import Modules.SoftEquations.ModelCat.


Set Automatic Introduction.
Delimit Scope signature_over_scope with sigo.

Section OverSignatures.

Context {C : category}.

Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).
Local Notation SIG := (signature C).


Context (Sig : SIG).
Local Notation REP := (rep_ar C Sig).
Local Notation REP_CAT := (rep_fiber_category Sig).

Local Notation  "R →→ S" := (rep_fiber_mor  R S) (at level 6).

Let comp {R S T : REP} (f : R →→ S)(g : S →→ T) : R →→ T :=
  compose (C := REP_CAT) f g.

Local Infix  ";;" := comp.

(** We follow the definition of signature *)
Definition signature_over_data :=
  ∑ F : (∏ R : REP, LModule R C),
        ∏ (R S : REP) (f : R →→ S),
          LModule_Mor _ (F R) (pb_LModule f (F S)).

Definition signature_over_on_objects (a : signature_over_data) : ∏ (R : REP), LModule R C
  := pr1 a.

Coercion signature_over_on_objects : signature_over_data >-> Funclass.

Definition signature_over_on_morphisms  (F : signature_over_data) {R S : REP} 
  : ∏ (f:  R →→ S), LModule_Mor _ (F R) (pb_LModule f (F S)) 
  := pr2 F R S.

Notation "# F" := (signature_over_on_morphisms F) (at level 3) : signature_over_scope.

Definition signature_over_idax  (F : signature_over_data) :=
  ∏ (R : REP), ∏ x ,
  (# F (identity (C := REP_CAT) R))%sigo x  = identity  _.



Definition signature_over_compax  (F : signature_over_data) :=
  ∏ R S T  (f : R →→ S) (g : S →→ T) ,
    (#F  (f ;; g))%sigo 
      = 
      (((# F f)%sigo :(F R : bmod_disp C C (R : Monad _)) -->[(f : Monad_Mor  _ _)] F S) ;; (#F g)%sigo)%mor_disp.

Definition is_signature_over  (F : signature_over_data) : UU := signature_over_idax F × signature_over_compax F.

Lemma isaprop_is_signature_over (F : signature_over_data) : isaprop (is_signature_over F).
Proof.
  apply isofhleveldirprod.
  - repeat (apply impred; intro).
    apply homset_property.
  - repeat (apply impred; intro).
    apply (homset_property (category_LModule _ _)).
Qed.

Definition signature_over : UU := ∑ F : signature_over_data, is_signature_over F.

Definition signature_over_data_from_signature_over (F : signature_over) : signature_over_data := pr1 F.
Coercion signature_over_data_from_signature_over : signature_over >-> signature_over_data.

Notation Θ := tautological_LModule.

Definition tautological_signature_over_on_objects : ∏ (R : REP), LModule R C := Θ.
Definition tautological_signature_over_on_morphisms : 
  ∏ (R S : REP) (f : rep_fiber_mor R S), LModule_Mor _ (Θ R) (pb_LModule f (Θ S)) :=
  @monad_mor_to_lmodule C.


Definition tautological_signature_over_data : signature_over_data  :=
  tautological_signature_over_on_objects ,, tautological_signature_over_on_morphisms.

Lemma tautological_signature_over_is_signature_over :  is_signature_over tautological_signature_over_data.
Proof.
  split.
  - intros R x.
    apply idpath.
  - intros R S T f g.
    apply LModule_Mor_equiv.
    + apply homset_property.
    + apply nat_trans_eq.
      * apply homset_property.
      * intro x.
        cbn.
        rewrite id_right.
        apply idpath.
Qed.

Definition tautological_signature_over : signature_over := _ ,, tautological_signature_over_is_signature_over.

Definition signature_over_id (F : signature_over) :
  ∏ (R : REP), ∏ x ,
  ((# F (identity (C:= REP_CAT) R)))%sigo x  = identity  _
  := pr1 (pr2 F).
(* ((# F (identity (C:= PRE_MONAD) R): LModule_Mor _ _ _ ))%sigo x  = identity  _ *)

Definition signature_over_comp (F : signature_over) {R S T : REP} 
           (f : rep_fiber_mor R S) (g : rep_fiber_mor S T)
  : 
    (#F  (f ;; g))%sigo 
      = 
      (((# F f)%sigo :(F R : bmod_disp C C (R : Monad _)) -->[(f : Monad_Mor  _ _)] F S) ;; (#F g)%sigo)%mor_disp
  := pr2 (pr2 F) _ _ _ _ _ .

(**

This last piece is about morphisms and category of over-signatures

*)

(* Demander la version pointwise plutôt ? *)
Definition is_signature_over_Mor (F F' : signature_over_data)
           (t : ∏ R : REP, LModule_Mor R (F R)  (F' R)) 
  :=
    ∏ (R S : REP)(f : rep_fiber_mor R S),
    (((# F)%sigo f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                  (t S : nat_trans _ _) 
    =
    ((t R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%sigo f : nat_trans _ _).


Lemma isaprop_is_signature_over_Mor (F F' : signature_over_data) t :
  isaprop (is_signature_over_Mor F F' t).
Proof.
  repeat (apply impred; intro).
  apply homset_property.
Qed.

Definition signature_over_Mor  (F F' : signature_over_data) : UU := ∑ X, is_signature_over_Mor F F' X.
                            
Local Notation "F ⟹ G" := (signature_over_Mor F G) (at level 39) : signature_over_scope.

Lemma isaset_signature_over_Mor (F F' : signature_over) : isaset (signature_over_Mor F F').
Proof.
  apply (isofhleveltotal2 2).
  + apply impred ; intro t; apply (homset_property (category_LModule _ _)).
  + intro x; apply isasetaprop, isaprop_is_signature_over_Mor.
Qed.


Definition signature_over_Mor_data
 {F F' : signature_over_data}(a : signature_over_Mor F F') := pr1 a.
Coercion signature_over_Mor_data : signature_over_Mor >-> Funclass.

Definition signature_over_Mor_ax {F F' : signature_over} (a : signature_over_Mor F F') 
  : ∏ {R S : REP}(f : rep_fiber_mor R S),
    (((# F)%sigo f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                  (a S : nat_trans _ _) 
    =
    ((a R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%sigo f : nat_trans _ _)
  := pr2 a.

Lemma signature_over_Mor_ax_pw {F F' : signature_over} (a : signature_over_Mor F F') 
  : ∏ {R S : REP}(f : rep_fiber_mor R S) x,
    (((# F)%sigo f :   nat_trans _ _) x) ·
                                       ((a S : nat_trans _ _) x) 
    =
    ((a R : nat_trans _ _)  x) · (((#F')%sigo f : nat_trans _ _) x).
Proof.
  intros.
  assert (h := signature_over_Mor_ax a f).
  eapply nat_trans_eq_pointwise in h.
  apply h.
Qed.

(** Equality between two signature_over morphisms *)

Lemma signature_over_Mor_eq (F F' : signature_over)(a a' : signature_over_Mor F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { apply funextsec. intro; apply H. }
  apply (total2_paths_f H'), proofirrelevance, isaprop_is_signature_over_Mor.
Qed.

Lemma is_signature_over_Mor_comp {F G H : signature_over} (a : signature_over_Mor F G) (b : signature_over_Mor G H) 
  : is_signature_over_Mor F H (fun R  => (a R : category_LModule _ _ ⟦_,_⟧ ) · b R).
Proof.
  intros ? ? ?.
  etrans.
  apply (assoc (C:= [_,_])).
  etrans.
  apply ( cancel_postcomposition (C:= [_,_])).
  apply (signature_over_Mor_ax (F:=F) (F':=G) a f).
  rewrite <- (assoc (C:=[_,_])).
  etrans.
  apply (cancel_precomposition ([_,_])).
  apply signature_over_Mor_ax.
  rewrite assoc.
  apply idpath.
Qed.

Definition signature_over_precategory_ob_mor  : precategory_ob_mor := precategory_ob_mor_pair
   signature_over (fun F F' => signature_over_Mor F F').

Lemma is_signature_over_Mor_id (F : signature_over_data) : is_signature_over_Mor F F
     (fun R => identity (C:=category_LModule _ _) _).
Proof.
  intros ? ? ? .
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition signature_over_Mor_id (F : signature_over_data) : signature_over_Mor F F :=
    tpair _ _ (is_signature_over_Mor_id F).

Definition signature_over_Mor_comp {F G H : signature_over} (a : signature_over_Mor F G) (b : signature_over_Mor G H)
  : signature_over_Mor F H 
  := tpair _ _ (is_signature_over_Mor_comp a b).

Definition signature_over_precategory_data : precategory_data.
Proof.
  apply (precategory_data_pair (signature_over_precategory_ob_mor )).
  + intro a; simpl.
    apply (signature_over_Mor_id (pr1 a)).
  + intros a b c f g.
    apply (signature_over_Mor_comp f g).
Defined.

Lemma is_precategory_signature_over_precategory_data :
   is_precategory signature_over_precategory_data.
Proof.
  repeat split; simpl; intros.
  - unfold identity.
    simpl.
    apply signature_over_Mor_eq. 
    intro x; simpl.
    apply (id_left (C:=category_LModule _ _)).
  - apply signature_over_Mor_eq.
    intro x; simpl.
    apply (id_right (C:=category_LModule _ _)).
  - apply signature_over_Mor_eq.
    intro x; simpl.
    apply (assoc (C:=category_LModule _ _)).
Qed.

Definition signature_over_precategory : precategory :=
  tpair (fun C => is_precategory C)
        (signature_over_precategory_data)
        (is_precategory_signature_over_precategory_data).

Lemma signature_over_category_has_homsets : has_homsets signature_over_precategory.
Proof.
  intros F G.
  apply isaset_signature_over_Mor.
Qed.

Definition signature_over_category : category.
Proof.
  exists (signature_over_precategory).
  apply signature_over_category_has_homsets.
Defined.


End OverSignatures.

Notation "# F" := (signature_over_on_morphisms _ F) (at level 3) : signature_over_scope.