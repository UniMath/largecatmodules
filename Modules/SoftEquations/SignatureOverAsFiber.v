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

Inspired by Signature.v
*)
(* =================================================================================== *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesFibration.
Require Import Modules.Prelims.LModulesComplements.


Require Import Modules.Signatures.Signature.


Set Automatic Introduction.
Delimit Scope signature_over_scope with sigo.

Section Signatures.

Context {C : category}.

Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
(* Local Notation BMOD := (bmod_disp C C). *)
Local Notation SIG := (signature C).

Context (Sig : SIG).

Local Notation REP := (model Sig).

(* Let rep_ar_mor (R S : REP) := rep_ar_mor_mor _ Sig Sig R S (signature_Mor_id Sig). *)

Local Notation  "R →→ S" := (model_mor_mor Sig Sig R S (signature_Mor_id Sig))
    (at level 6).
Let comp {R S T : REP} (f : R →→ S)(g : S →→ T) : R →→ T :=
  transportf _ (id_left _) (comp_disp  (D := rep_disp _) f g  ).

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
  (# F (rep_id _ R))%sigo x  = identity  _.



(** Contrary to signature.v, we state the equality in the category of functors rather
    than in module because types would be incompatible because of the transport *)
Definition signature_over_compax  (F : signature_over_data) :=
  ∏ R S T  (f : R →→ S) (g : S →→ T) ,
  (#F  (f ;; g) :  nat_trans _ _)%sigo 
  = 
  (((# F f)%sigo :(F R : bmod_disp C C (R : Monad _)) -->[(f : Monad_Mor  _ _)] F S) ;; (#F g)%sigo :
     LModule_Mor _ _ _
  )%mor_disp.

Definition is_signature_over  (F : signature_over_data) : UU := signature_over_idax F × signature_over_compax F.

Lemma isaprop_is_signature_over (F : signature_over_data) : isaprop (is_signature_over F).
Proof.
  apply isofhleveldirprod.
  - repeat (apply impred; intro).
    apply homset_property.
  - repeat (apply impred; intro).
    apply (homset_property (functor_category C C)).
Qed.

Definition signature_over : UU := ∑ F : signature_over_data, is_signature_over F.

Definition signature_over_data_from_signature_over (F : signature_over) : signature_over_data := pr1 F.
Coercion signature_over_data_from_signature_over : signature_over >-> signature_over_data.

Notation Θ := tautological_LModule.

Definition tautological_signature_over_on_objects : ∏ (R : REP), LModule R C := Θ.
Definition tautological_signature_over_on_morphisms : 
  ∏ (R S : REP) (f : R →→ S), LModule_Mor _ (Θ R) (pb_LModule f (Θ S)) :=
  @monad_mor_to_lmodule C.


Definition tautological_signature_over_data : signature_over_data  :=
  tautological_signature_over_on_objects ,, tautological_signature_over_on_morphisms.

Lemma tautological_signature_over_is_signature_over :  is_signature_over tautological_signature_over_data.
Proof.
  split.
  - intros R x.
    apply idpath.
  - intros R S T f g.
    (* apply LModule_Mor_equiv. *)
    (* + apply homset_property. *)
    + apply nat_trans_eq.
      * apply homset_property.
      * intro x.
        cbn.
        rewrite id_right.
        unfold comp.
        (* this was not needed in Signature.v, and I don't know exactly why  *)
        destruct (id_left _).
        apply idpath.
Qed.

Definition tautological_signature_over : signature_over := _ ,, tautological_signature_over_is_signature_over.

Definition signature_over_id (F : signature_over) :
  ∏ (R : REP), ∏ x ,
  ((# F (rep_id _ R)))%sigo x  = identity  _
  := pr1 (pr2 F).

Definition signature_over_comp (F : signature_over) {R S T : REP} 
           (f : R →→ S) (g : S →→  T)
           :
  (#F  (f ;; g) :  nat_trans _ _)%sigo 
  = 
  (((# F f)%sigo :(F R : bmod_disp C C (R : Monad _)) -->[(f : Monad_Mor  _ _)] F S) ;; (#F g)%sigo :
     LModule_Mor _ _ _
  )%mor_disp
  := pr2 (pr2 F) _ _ _ _ _ .

(* We don't need morphisms of signatures_over *)

End Signatures.