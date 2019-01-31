(* =================================================================================== *)
(** * Σ-modules

    Content:
    - Definition of a signature (aka Σ-module) over the category of another signature Σ [signature_over]
    - Definition of the category Sig-modules (signature_over_category]
    - The action of 1-models yield signature over morphism [action_sig_over_mor]
    - Functor between 1-signatures and Σ-modules [sig_to_sig_over_functor]
    - starting from a 1-signature morphism f : S1 -> S2, a signature over S1 can be pushed out to
      a signature over S2. This actually induces a functor f* (and thus an opfibration)



TODO : factor this definition and the standard definition of signatures ?
(a lot of stuff was indeed copied and pasted from Signature.v)
*)
(* =================================================================================== *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
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


Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.ModelCat.


Set Automatic Introduction.
Delimit Scope signature_over_scope with sigo.

Section OverSignatures.

(** We work in an arbitrary category [C] *)
Context {C : category}.

Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
(* Local Notation BMOD := (bmod_disp C C). *)
Local Notation SIG := (signature C).


(** The 1-signature [Sig] is fixed in the following.
We will then consider Sig-modules in the following
 *)
Context (Sig : SIG).
Local Notation REP := (model Sig).
Local Notation REP_CAT := (rep_fiber_category Sig).

(** Notation for 1-model morphisms *)
Local Notation  "R →→ S" := (rep_fiber_mor  R S) (at level 6).

(** Notation for composition of 1-model morphisms *)
Let comp {R S T : REP} (f : R →→ S)(g : S →→ T) : R →→ T :=
  compose (C := REP_CAT) f g.

Local Infix  ";;" := comp.

(** Raw data for a [Sig]-module:
- each 1-model is assigned a module over itself
- 1-model morphisms are mapped to module morphisms *)
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

(** Notation for the map 1-model morphism -> module morphism *)
Notation "# F" := (signature_over_on_morphisms F) (at level 3) : signature_over_scope.

Definition signature_over_on_morphisms_cancel_pw (F : signature_over_data) {R S : REP} 
           {u v : R →→ S}  (e : u = v) x : (# F u)%sigo x = (#F v)%sigo x.
  induction e.
  apply idpath.
Defined.

(** Statment that the raw data preserves identity *)
Definition signature_over_idax  (F : signature_over_data) :=
  ∏ (R : REP), ∏ x ,
  (# F (identity (C := REP_CAT) R))%sigo x = identity  _.


(** Statment that the raw data preserves composition *)
Definition signature_over_compax  (F : signature_over_data) :=
  ∏ R S T  (f : R →→ S) (g : S →→ T) ,
    (#F  (f ;; g))%sigo 
      = 
      (((# F f)%sigo :(F R : bmod_disp C C (R : Monad _)) -->[(f : Monad_Mor  _ _)] F S) ;; (#F g)%sigo)%mor_disp.

(** Raw data yields a Sig-module if it satisfies the previous functoriality conditions *)
Definition is_signature_over  (F : signature_over_data) : UU := signature_over_idax F × signature_over_compax F.

(** This statment is hProp *)
Lemma isaprop_is_signature_over (F : signature_over_data) : isaprop (is_signature_over F).
Proof.
  apply isofhleveldirprod.
  - repeat (apply impred; intro).
    apply homset_property.
  - repeat (apply impred; intro).
    apply (homset_property (category_LModule _ _)).
Qed.

(** A Sig-module sends functorially 1-model morphisms onto module morphisms *)
Definition signature_over : UU := ∑ F : signature_over_data, is_signature_over F.

Definition signature_over_data_from_signature_over (F : signature_over) : signature_over_data := pr1 F.
Coercion signature_over_data_from_signature_over : signature_over >-> signature_over_data.

(** Any 1-signature [sig] induces a Sig-module (indeed, this can be proven on paper using the
    forgetful functor 1-model -> monads) *)
Definition sig_over_data_from_sig (sig : signature C) : signature_over_data.
  use tpair.
  use (signature_on_objects sig).
  exact (fun R S f =>  signature_on_morphisms sig f).
Defined.

Local Notation OSig := sig_over_data_from_sig.

(** Functoriality conditions for a Sig-module induced by a signatre *)
Lemma is_sig_over_from_sig (sig : signature C) : is_signature_over (OSig sig). 
  split.
  - use signature_id.
  - red.
    intros; use signature_comp.
Defined.

(** Sig-module from a 1-signature *)
Coercion sig_over_from_sig (sig : signature C) : signature_over :=
  (sig_over_data_from_sig sig ,, is_sig_over_from_sig sig).

(** The tautological Sig-module mapping a 1-model to the underlying monad *)
Definition tautological_signature_over : signature_over :=
  sig_over_from_sig tautological_signature.

(** A Sig-module preserves identity *)
Definition signature_over_id (F : signature_over) :
  ∏ (R : REP), ∏ x ,
  ((# F (identity (C:= REP_CAT) R)))%sigo x  = identity  _
  := pr1 (pr2 F).

(** A Sig-module preserves composition *)
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

(** A Sig-module morphism between two Sig-modules [F] and [F'] is
    a natural family of module morphisms t = (F(R) -> F'(R))_R:
    for any 1-model morphism f : R -> S,
<<<
          F(f)
   F(R) ---------> F(S)
    |               |
    |               |
t_R |               | t_S
    |               |
    V               V
   F'(R)---------> F'(S)
            F'(f)
>>>
*)
Definition is_signature_over_Mor (F F' : signature_over_data)
           (t : ∏ R : REP, LModule_Mor R (F R)  (F' R)) 
  :=
    ∏ (R S : REP)(f : rep_fiber_mor R S),
    (((# F)%sigo f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                  (t S : nat_trans _ _) 
    =
    ((t R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%sigo f : nat_trans _ _).


(** This last statment is hProp *)
Lemma isaprop_is_signature_over_Mor (F F' : signature_over_data) t :
  isaprop (is_signature_over_Mor F F' t).
Proof.
  repeat (apply impred; intro).
  apply homset_property.
Qed.

(** A Sig-module morphism is a naturaly family of module morphisms *)
Definition signature_over_Mor  (F F' : signature_over_data) : UU := ∑ X, is_signature_over_Mor F F' X.

Definition mkSignature_over_Mor {F F' : signature_over_data} X
           (hX : is_signature_over_Mor F F' X) : signature_over_Mor F F' :=
  X ,, hX.
                            
(** Notation for Sig-module morphisms *)
Local Notation "F ⟹ G" := (signature_over_Mor F G) (at level 39) : signature_over_scope.

(** Homsets are hSet *)
Lemma isaset_signature_over_Mor (F F' : signature_over) : isaset (F ⟹ F')%sigo.
Proof.
  apply (isofhleveltotal2 2).
  + apply impred ; intro t; apply (homset_property (category_LModule _ _)).
  + intro x; apply isasetaprop, isaprop_is_signature_over_Mor.
Qed.


Definition signature_over_Mor_data
 {F F' : signature_over_data}(a : signature_over_Mor F F') := pr1 a.
Coercion signature_over_Mor_data : signature_over_Mor >-> Funclass.

(** A Sig-module morphism is natural *)
Definition signature_over_Mor_ax {F F' : signature_over} (a : (F ⟹ F')%sigo)
  : ∏ {R S : REP}(f : rep_fiber_mor R S),
    (((# F)%sigo f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                  (a S : nat_trans _ _) 
    =
    ((a R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%sigo f : nat_trans _ _)
  := pr2 a.

(** A Sig-module morphism is natural (pointwise version of the naturality diagram) *)
Lemma signature_over_Mor_ax_pw {F F' : signature_over} (a : (F ⟹ F')%sigo) 
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

(** Sig-module morphisms are equal if for any 1-model R, their R-component module morphism
  are equal *)
Lemma signature_over_Mor_eq (F F' : signature_over)(a a' : signature_over_Mor F F'):
  (∏ R, a R = a' R) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { apply funextsec. intro; apply H. }
  apply (total2_paths_f H'), proofirrelevance, isaprop_is_signature_over_Mor.
Qed.


(** Intermediate data to build the category of Sig-modules *)
Definition signature_over_precategory_ob_mor  : precategory_ob_mor := precategory_ob_mor_pair
   signature_over (fun F F' => signature_over_Mor F F').

(** The identity family of module morphisms yields a Sig-module morphism *)
Lemma is_signature_over_Mor_id (F : signature_over_data) : is_signature_over_Mor F F
     (fun R => identity (C:=category_LModule _ _) _).
Proof.
  intros ? ? ? .
  rewrite id_left, id_right.
  apply idpath.
Qed.

(** The identity Sig-module morphism *)
Definition signature_over_Mor_id (F : signature_over_data) : signature_over_Mor F F :=
    tpair _ _ (is_signature_over_Mor_id F).

(** Composition of two Sig-module morphisms yields a Sig-module morphism *)
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
(** Composition of Sig-module morphisms *)
Definition signature_over_Mor_comp {F G H : signature_over} (a : signature_over_Mor F G) (b : signature_over_Mor G H)
  : signature_over_Mor F H 
  := tpair _ _ (is_signature_over_Mor_comp a b).

(** Intermediate data to build the category of Sig-modules *)
Definition signature_over_precategory_data : precategory_data.
Proof.
  apply (precategory_data_pair (signature_over_precategory_ob_mor )).
  + intro a; simpl.
    apply (signature_over_Mor_id (pr1 a)).
  + intros a b c f g.
    apply (signature_over_Mor_comp f g).
Defined.

(** Axioms of categories:
 - identity is a neutral element for composition
 - composition is associative *)
Lemma is_precategory_signature_over_precategory_data :
   is_precategory signature_over_precategory_data.
Proof.
  apply mk_is_precategory_one_assoc; simpl; intros.
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

(** The precategory of Sig-modules *)
Definition signature_over_precategory : precategory := 
  tpair (fun C => is_precategory C)
        (signature_over_precategory_data)
        (is_precategory_signature_over_precategory_data).

(** Homsets are hSet *)
Lemma signature_over_category_has_homsets : has_homsets signature_over_precategory.
Proof.
  intros F G.
  apply isaset_signature_over_Mor.
Qed.

(** Hence, we get the category of Sig-modules *)
Definition signature_over_category : category.
Proof.
  exists (signature_over_precategory).
  apply signature_over_category_has_homsets.
Defined.



Local Notation ι := sig_over_from_sig.
Local Notation  "S1 →→s S2" := (signature_over_Mor S1 S2) (at level 23).

(** The action of 1-models yield  signature over morphism *)
Definition action_sig_over_mor : ι Sig  →→s tautological_signature_over.
  use mkSignature_over_Mor.
  - use model_τ.
  - cbn.
    intros R S f.
    apply pathsinv0.
    apply (nat_trans_eq (homset_property _)).
    use (rep_fiber_mor_ax f).
Defined.

(** A 1-sig morphism yields a 2-sig morphism *)
Definition sig_sig_over_mor {S1 S2 : SIG} (f : signature_Mor S1 S2) : ι S1  →→s ι S2 :=
  @mkSignature_over_Mor (ι S1) (ι S2) (λ R : REP, f R)
                        (λ (R S : REP) (g : R →→ S), signature_Mor_ax f g).

Lemma sig_to_sig_over_is_functor :
  is_functor (mk_functor_data (C := signature_category (C := C))(C' := signature_over_category)
                              ι (@sig_sig_over_mor)).
Proof.
  split.
  - intro S.
    use signature_over_Mor_eq.
    intro ; apply idpath.
  - intros S1 S2 S3 f1 f2.
    use signature_over_Mor_eq.
    intro ; apply idpath.
Qed.

Definition sig_to_sig_over_functor : functor (signature_category (C := C)) signature_over_category :=
  mk_functor _ sig_to_sig_over_is_functor.

End OverSignatures.

Notation "# F" := (signature_over_on_morphisms _ F) (at level 3) : signature_over_scope.

Section PushoutOverSig.



  Definition po_signature_over_data
             {C} {S1 S2 : signature C} (f : signature_Mor S1 S2) (SS1 : signature_over S1)
  : signature_over_data S2.
  Proof.
    use tpair.
    - intro R.
      exact (SS1 (pb_rep f R)).
    - intros R S g.
      apply ((# SS1 (pb_rep_mor f g ))%sigo).
  Defined.

  Lemma  po_is_signature_over 
        {C} {S1 S2 : signature C} (f : signature_Mor S1 S2) (SS1 : signature_over S1)
  : is_signature_over _ (po_signature_over_data f SS1).
  Proof.
    split.
    - intros R x.
      cbn.
      etrans;[|use signature_over_id ].
      apply (signature_over_on_morphisms_cancel_pw _ SS1).
      apply pb_rep_mor_id.
    - intros R S T u v.
      cbn -[compose].
      apply LModule_Mor_equiv; [apply homset_property|].
      apply nat_trans_eq;[apply homset_property|].
      intro x.
      etrans. {
        eapply (signature_over_on_morphisms_cancel_pw _ SS1).
        apply pb_rep_mor_comp.
      }
      rewrite signature_over_comp.
      apply idpath.
  Defined.

  Definition  po_signature_over 
         {C} {S1 S2 : signature C} (f : signature_Mor S1 S2) (SS1 : signature_over S1) :
    signature_over S2 := _ ,, po_is_signature_over f SS1.

  Definition  po_signature_over_mor
              {C} {S1 S2 : signature C} (f : signature_Mor S1 S2) {SS1 SS1' : signature_over S1}
              (ff1 : signature_over_Mor _ SS1 SS1')
    :  signature_over_Mor _ 
                             (po_signature_over f SS1)(po_signature_over f SS1')
     :=
     mkSignature_over_Mor _ (F := po_signature_over f SS1)
                                 (F' := po_signature_over f SS1')
                                 (fun R => ff1 (pb_rep f R))
                                 (fun R S g =>  signature_over_Mor_ax _ ff1 _ ) .


End PushoutOverSig.