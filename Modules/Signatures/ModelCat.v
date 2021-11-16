(** * Category of models of a signature

- [rep_fiber_category]: Direct definition 
- [catiso_modelcat]: proof that this category is isomorphic to the definition as a fiber category
  of the fibration of the total 1-model category over the 1-signatures category,
  as defined in Signatures/Signature.v

- if R is a Σ-model R, then so is Σ(R) + Id, and R is isomorphic to Σ(R) + Id if it is the initial model.
   [iso_mod_id_model]

*)

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
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.whiskering.

Require Import Modules.Prelims.lib.

Require Import Modules.Signatures.Signature.

Section ModelCat.

(**
We work  in a category [C], and are going to define the 1-models of a fixed 1-signature.
*)
Context {C : category}.

Local Notation MONAD := (category_Monad C).
Local Notation SIG := (signature C).

(** This proposition states that the monad morphism [g] between two 1-models
    commutes with the action [model_τ].
 *)
Definition rep_fiber_mor_law {a : SIG} (M N : model a) 
           (g : Monad_Mor M N)
  : UU
  := ∏ c : C, model_τ M c · g c = ((#a g)%ar:nat_trans _ _) c ·  model_τ N c .

(** This statment is hProp *)
Lemma isaprop_rep_fiber_mor_law {a  : SIG} (M N : model a)
      (g : Monad_Mor M N) 
  : isaprop (rep_fiber_mor_law  M N  g).
Proof.
  intros.
  apply impred; intro c.
  apply homset_property.
Qed.

(** A model morphism [g] between two 1-models [M] and [N] is a monad morphism
    commuting with the action [model_τ].
 *)
Definition rep_fiber_mor {a : SIG} (M N : model a)  :=
  ∑ g:Monad_Mor M N, rep_fiber_mor_law  M N g.

(** Homsets of 1-models are hSet *)
Lemma isaset_rep_fiber_mor {a : SIG} (M N : model a)  :
  isaset (rep_fiber_mor  M N ).
Proof.
  intros.
  apply isaset_total2 .
  - apply has_homsets_Monad.
  - intros.
    apply isasetaprop.
    apply isaprop_rep_fiber_mor_law.
Qed.

(** Coercion from 1-model morphism to monad morphisms *)
Coercion monad_morphism_from_rep_fiber_mor {a : SIG} {M N : model a} 
          (h : rep_fiber_mor M N) : Monad_Mor M N
  := pr1 h.

(** A model morphism commutes with the action *)
Definition rep_fiber_mor_ax {a : SIG} {M N : model a} 
            (h:rep_fiber_mor  M N ) :
  ∏ c, model_τ M c · h c = (#a h)%ar c ·  model_τ N c 
  := pr2 h.

(** If two 1-model morphisms are equal as natural transformations, then they are equal *)
Lemma rep_fiber_mor_eq_nt {a : SIG} (R S:model a)
      (u v: rep_fiber_mor R S) :
  (u : nat_trans _ _) = v -> u = v.
Proof.
  intros.
  use (invmap (subtypeInjectivity _ _ _ _  )). 
  - intro g.
    apply isaprop_rep_fiber_mor_law.
  - use (invmap (Monad_Mor_equiv _ _  _  )).  
     +  assumption.
Qed.

(** If two 1-model morphisms are pointwise equal, then they are equal *)
Lemma rep_fiber_mor_eq {a : SIG} (R S:model a)
      (u v: rep_fiber_mor R S) :
  (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c) -> u = v.
Proof.
  intros.
  apply rep_fiber_mor_eq_nt.
  apply nat_trans_eq.
  - apply homset_property.
  - assumption.
Qed.

(** The identity natural transformation commutes with the action *)
Lemma is_rep_fiber_id {a : SIG} (M : model a)
  : rep_fiber_mor_law M M (identity (C := MONAD) (M : Monad _)).
Proof.
  intro c.
  rewrite signature_id.
  etrans;[apply id_right|].
  apply pathsinv0.
  apply id_left.
Qed.

(** The composition of two 1-model morphisms commutes with the action *)
Lemma is_rep_fiber_comp {a : SIG} {M N O: model a}
      (f : rep_fiber_mor M N) (g : rep_fiber_mor N O) : rep_fiber_mor_law M O
                                                                          (compose (C := MONAD)
                                                                                   (f : Monad_Mor _ _)
                                                                                   (g : Monad_Mor _ _)).
Proof.
  intro c.
  rewrite signature_comp.
  cbn.
  rewrite id_right.
  rewrite assoc.
  rewrite (rep_fiber_mor_ax f).
  rewrite <- assoc.
  rewrite (rep_fiber_mor_ax g).
  rewrite assoc.
  reflexivity.
Qed.

(** The identity 1-model morphism *)
Definition rep_fiber_id {a : SIG} (M : model a) : rep_fiber_mor M M :=
    tpair _ _ (is_rep_fiber_id M).

(** Composition of 1-model morphisms *)
Definition rep_fiber_comp {a : SIG} {M N O: model a}
      (f : rep_fiber_mor M N) (g : rep_fiber_mor N O) : rep_fiber_mor M O :=
  tpair _ _ (is_rep_fiber_comp f g).

(** Intermediate data to build the category of 1-models of a 1-signature [a] *)
Definition rep_fiber_precategory_ob_mor (a : SIG) : precategory_ob_mor :=
  make_precategory_ob_mor _ (rep_fiber_mor (a := a) ).

Definition rep_fiber_precategory_data (a : SIG) : precategory_data.
Proof.
  apply (make_precategory_data (rep_fiber_precategory_ob_mor a)).
  + intro x; simpl in x.
    apply (rep_fiber_id ).
  + intros M N O.
    apply rep_fiber_comp.
Defined.

(** 1-model morphisms satisfy the axioms of category:
- identity is a neutral element for composition
- composition is associative
 *)
Lemma is_precategory_rep_fiber_precategory_data (S : SIG) :
   is_precategory (rep_fiber_precategory_data S).
Proof.
  apply make_is_precategory_one_assoc; simpl; intros.
  - unfold identity.
    simpl.
    apply rep_fiber_mor_eq. 
    intro x; simpl.
    apply id_left.
  - apply rep_fiber_mor_eq. 
    intro x; simpl.
    apply id_right.
  - apply rep_fiber_mor_eq. 
    intro x; simpl.
    apply assoc.
Qed.

(** The precategory of 1-model morphisms *)
Definition rep_fiber_precategory (S : SIG) : precategory :=
  tpair (fun C => is_precategory C)
        (rep_fiber_precategory_data S)
        (is_precategory_rep_fiber_precategory_data S).

(** Homsets are hSet *)
Lemma rep_fiber_category_has_homsets (S : SIG) : has_homsets (rep_fiber_precategory S).
Proof.
  intros F G.
  apply isaset_rep_fiber_mor.
Qed.


(** The category of 1-model morphisms (= precategory + Homsets are hSet *)
Definition rep_fiber_category (S : SIG) : category.
Proof.
  exists (rep_fiber_precategory S).
  apply rep_fiber_category_has_homsets.
Defined.

  (** The pullback of models along a 1-signature morphism has a functorial
action. This is a consequence of 1-models being fibered over 1-sigs.
However we do a direct proof here because using the fibration would lead to
a dirty term *)
  Lemma pb_rep_mor_law  {S1 S2 : signature C} (f : signature_Mor S1 S2) {R S : model S2}
             (m : rep_fiber_mor R S) : rep_fiber_mor_law (pb_rep f R) (pb_rep f S) m.
  Proof.
    intro c.
    cbn.
    etrans;[apply pathsinv0,assoc|].
    etrans;[ apply cancel_precomposition, rep_fiber_mor_ax|].
    do 2 rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply signature_Mor_ax_pw.
  Qed.

  Definition pb_rep_mor  {S1 S2 : signature C} (f : signature_Mor S1 S2) {R S : model S2}
        (m : rep_fiber_mor R S) : rep_fiber_mor (pb_rep f R) (pb_rep f S) :=
    _ ,, pb_rep_mor_law f m.

  Lemma pb_rep_mor_comp   {S1 S2 : signature C} (f : signature_Mor S1 S2) {R S T : model S2}
        (m : rep_fiber_mor R S)(n : rep_fiber_mor S T)
    : pb_rep_mor f (compose (C := rep_fiber_category S2) m n) =
      compose (C := rep_fiber_category S1) (pb_rep_mor _ m)(pb_rep_mor _ n).
  Proof.
    apply rep_fiber_mor_eq; intro; apply idpath.
  Defined.

  Lemma pb_rep_mor_id  {S1 S2 : signature C} (f : signature_Mor S1 S2) (R : model S2) :
   (pb_rep_mor f (rep_fiber_id R))  = identity (C := rep_fiber_category S1) _.
  Proof.
      apply rep_fiber_mor_eq; intro; apply idpath.
  Defined.
(**

In our presentable signatures formalization (Cf Signatures/), we have defined the
fibration (using the displayed category framework) of the total 1-model category
over the 1-signatures category (Signature.v).

A definition of 1-model category over a 1-signature is retrieved by taking the fiber category over
this signature.

The following is a proof that the two definitions (here and there) yield isomorphic categories.

 *)

Context (S : SIG).

Local Notation FIBER_CAT := (fiber_category (rep_disp C) S).
Local Notation MODEL_CAT := (rep_fiber_category S).

  Definition fib_to_dir_weq : FIBER_CAT  ≃ MODEL_CAT := idweq _.
  Local Notation FSob := fib_to_dir_weq.

  Definition fib_to_dir_mor_weq (R R' : FIBER_CAT) :
    FIBER_CAT ⟦ R , R' ⟧ ≃ MODEL_CAT  ⟦ FSob R , FSob R' ⟧.
  Proof.
    apply weqfibtototal.
    intro f.
    apply weqonsecfibers.
    intro o.
    apply eqweqmap.
    apply maponpaths.
    apply cancel_postcomposition.
    apply ( (id_right _)).
  Defined.
  Local Notation FSmor := fib_to_dir_mor_weq.

  Definition fib_to_dir_functor_data : functor_data FIBER_CAT MODEL_CAT :=
    functor_data_constr _ _  FSob  FSmor.

  Lemma fib_to_dir_is_functor : is_functor fib_to_dir_functor_data.
  Proof.
    split.
    - intro R.
      apply rep_fiber_mor_eq_nt.
      apply idpath.
    - intros R R' T f g.
      apply rep_fiber_mor_eq_nt.
      cbn.
      set (e := id_right _).
      induction e.
      apply idpath.
  Defined.

  Definition fib_to_dir_functor : functor FIBER_CAT MODEL_CAT :=
    _ ,, fib_to_dir_is_functor.
  Local Notation FS := fib_to_dir_functor.

  Definition catiso_modelcat : catiso FIBER_CAT MODEL_CAT
    := FS,, (λ x y : FIBER_CAT, weqproperty (FSmor x y)),, weqproperty FSob.


End ModelCat.

(** In this section, we prove that if m : M -> R is a R-module morphism,
then
- the functor M + Id is a monad
- the morphism [m , η] : M + Id -> R is a monad morphism
- M has a structure of a module over M + Id (by pulling it pack along the monad morphism)
- the inclusion M -> M + Id is a a module morphism

 *)
Section InitAlg.
  Context {C : category} (bc : BinCoproducts C).
  Local Notation Θ := (tautological_LModule ).

  Context {R : Monad C} (M : LModule R C) (m : LModule_Mor R M (Θ R)).

  Local Notation BC F := (BinCoproducts_functor_precat C C bc (F : functor _ _)).
  Local Notation bcO := (BinCoproductObject).

  (** M + Id functor *)
  Definition mod_id_functor  : functor C C :=
    bcO (BC M (functor_identity C)).

  Local Notation IdM := mod_id_functor.
  Local Infix "+" := bc.

  (** [m, η] : M + Id -> R will be the monad morphism *)
  Definition mod_id_nt : nat_trans IdM R.
    apply (BinCoproductArrow  (BC _  _)).
    exact (m : nat_trans _ _).
    apply η.
  Defined.

  (** ι₂ : Id -> M + Id  will be the unit of the monad *)
  Definition mod_id_η : nat_trans (functor_identity _) IdM :=
    BinCoproductIn2 (*[C,C]*) (BC _ _).

  Definition mod_M_idM : nat_trans M IdM :=
    BinCoproductIn1 (*[C,C]*) (BC _ _).

  (** The (M + Id)-multiplication for M:
<<
            M[m , η]
M (M + Id) ---------> M R --------> M
>>
   *)
  Definition mod_id_M_mod : nat_trans (IdM ∙ M) M.
  Proof.
    eapply (compose( C := [C,C]) (b := R ∙ M)).
    - apply post_whisker.
      apply mod_id_nt.
    - apply lm_mult.
  Defined.


  (** First law of (M + Id)-module for M *)
  Lemma mod_id_M_mod_law1  : ∏ c, 
       #M (mod_id_η c) · mod_id_M_mod c = identity _.
  Proof.
    intro c.
    cbn.
    repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
            coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; cbn).
    rewrite assoc.
    etrans;[apply cancel_postcomposition, pathsinv0, functor_comp|].
    rewrite BinCoproductIn2Commutes.
    apply LModule_law1.
  Qed.



    (* De l'intérêt que les nat_trans sont définis entre functor_data ! En effet, ici
   les deux foncteurs ont le même functor_data. C'est la partie hProp qui diffère *)
  Definition postcomp_nt (F : functor C C) : nat_trans (F ∙ IdM)  (bcO (BC (F ∙ M) F): functor _ _) :=
    nat_trans_id (F ∙ IdM) . 

  (** Isomorphism between F (M + Id) and F M + F *)
  Lemma isoRIdM (F : functor C C) : iso (C := [C,C]) (F ∙ IdM)  ((BC (F ∙ M) F)).
    use functor_iso_from_pointwise_iso.
    - apply postcomp_nt.
    - intro o.
      apply identity_is_iso.
  Defined.

  (** The multiplication for the monad M + Id:
<<

                                             M [ρ,η]                   
 (M + Id) (M + Id) ~ M (M + Id) + (M + Id)  ---------> M R + (M + Id) ---> M + (M + Id) ----> M + Id
>>
   *)
  Definition mod_id_μ   : IdM ∙ IdM ⟹ IdM.
    (* TODO/ utiliser ce lemme ailleurs dans la formalisation plutôt que de composer explicitement
      avec l'iso
     *)
    eapply (iso_comp_right_weq (C := [C,C])).
    - apply isoRIdM.
    - apply BinCoproductArrow; [|apply identity].
      eapply compose.
      + apply mod_id_M_mod.
      + apply mod_M_idM.
  Defined.

  (** Data for the (M + Id) monad *)
  Definition mod_id_monad_data : Monad_data C :=
    ((IdM ,, mod_id_μ) ,, mod_id_η).

  Local Infix "++f" := (BinCoproductOfArrows _ _ _) (at level 6).
  Local Notation "[[ f , g ]]" := (BinCoproductArrow _ f g).
  Local Notation ID := (identity _).
  Local Notation ι1 :=  (BinCoproductIn1  (bc  _ _)).
  Local Notation ι2 :=  (BinCoproductIn2  (bc  _ _)).


  Local Lemma helper (c : C) f :
    (η R) (M c + c) · # R f · (μ R) c = f.
  Proof.
    etrans.
    {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (nat_trans_ax (η R)).
    }
    rewrite <- assoc.
    etrans;[|apply id_right].
    apply  cancel_precomposition.
    apply Monad_law1.
  Qed.

  (** Second (M + Id)-module law for M *)
  Lemma mod_id_M_mod_law2  : ∏ c, 
       #M (mod_id_μ _) · mod_id_M_mod c = mod_id_M_mod _ · mod_id_M_mod _.
  Proof.
    intro c.
    repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
            coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
            BinCoproduct_of_functors_mor
            ; cbn).
    repeat rewrite id_left.
    apply pathsinv0.
    etrans.
    {
      rewrite assoc.
      apply cancel_postcomposition.
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      apply pathsinv0.
      apply (nat_trans_ax (lm_mult R M)).
    }
    etrans.
    {
      do 2 rewrite <- assoc.
      do 2 apply cancel_precomposition.
      apply pathsinv0.
      apply LModule_law2.
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans; [|apply functor_comp].
    etrans.
    {
      apply pathsinv0.
      etrans; revgoals.
      {
        apply cancel_postcomposition.
        cbn.
        apply functor_comp.
      }
      apply functor_comp.
    }
    apply maponpaths.
    etrans;[rewrite <- assoc; apply postcompWithBinCoproductArrow|].
    apply pathsinv0.
    apply BinCoproductArrowUnique.
    *  rewrite assoc.
       rewrite BinCoproductIn1Commutes.
       repeat rewrite <- assoc.
       rewrite BinCoproductIn1Commutes.
       etrans; revgoals.
       {
         rewrite assoc.
         apply cancel_postcomposition.
         apply nat_trans_ax.
       }
       etrans; revgoals.
       {
         rewrite <- assoc.
         apply cancel_precomposition.
         apply pathsinv0.
         apply (LModule_Mor_σ _ m).
       }
       reflexivity.
    * rewrite assoc.
      rewrite BinCoproductIn2Commutes.
      etrans;[apply id_left|].
      apply pathsinv0.
      rewrite assoc.
      apply helper.
  Qed.



  (** Monad laws for (M + Id) *)
  Lemma mod_id_monad_laws : Monad_laws mod_id_monad_data.
  Proof.
    repeat split.
    - intro c.
      repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
              coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; cbn).
      rewrite id_left.
      apply BinCoproductIn2Commutes.
    - intro c.

      repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
              coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
              BinCoproduct_of_functors_mor ;
      cbn -[mod_id_M_mod mod_id_η mod_M_idM]
               ).
      rewrite id_left.
      etrans;[ apply precompWithBinCoproductArrow|].
      rewrite id_right.
      rewrite assoc.
      apply pathsinv0.
      apply BinCoproductArrowUnique.
      + apply pathsinv0.
        etrans.
        apply cancel_postcomposition.
        apply (mod_id_M_mod_law1 c).
        rewrite id_right; apply id_left.

      + apply id_right.

    - (*la par contre c'est assez chaud *)
      intro c.
      repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
              coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
              BinCoproduct_of_functors_mor ;
      cbn -[mod_id_M_mod mod_id_η mod_M_idM ]
               ).
      repeat rewrite id_left.
      set (u := [[ _ , _ ]]).
      set (v := [[ _ , _ ]]).
      assert (i2u : ι2 · u = ID) by apply BinCoproductIn2Commutes.
      assert (i2u' : (ι2 · ((# M u) ++f u · u)) = u).
      {
          rewrite assoc.
          rewrite BinCoproductOfArrowsIn2.
          rewrite <- assoc.
          rewrite i2u.
          apply id_right.
      }
      etrans;[apply precompWithBinCoproductArrow|].
      apply pathsinv0.
      rewrite id_right.
      apply BinCoproductArrowUnique; revgoals.
      +
        (* etrans;[apply i2u'|]. *)
        rewrite assoc.
        unfold v.
        rewrite BinCoproductIn2Commutes.
        apply id_left.
      + (** This is the difficult part: M(M(M+I) + M+I) *)
        unfold v.
        repeat rewrite assoc.
        rewrite BinCoproductIn1Commutes.
        unfold u.
        repeat rewrite <- assoc.
        rewrite BinCoproductIn1Commutes.
        repeat rewrite assoc.
        apply cancel_postcomposition.
        etrans;[apply pathsinv0, mod_id_M_mod_law2|].
      repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
              coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
              BinCoproduct_of_functors_mor
              ; cbn).
        repeat rewrite id_left.
        reflexivity.
  Qed.
  

  (** The M + Id monad *)
  Definition mod_id_monad : Monad C := _ ,, mod_id_monad_laws.

  (** The morphism M + Id  --> R is a monad morphism *)
  Lemma mod_id_monad_mor_laws : Monad_Mor_laws (T := mod_id_monad) mod_id_nt.
  Proof.
    split.
    - intro c.

      repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
              coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
              BinCoproduct_of_functors_mor
              ; cbn).
      rewrite id_left.
      (etrans; [ apply BinCoproductArrowEta| apply pathsinv0; apply BinCoproductArrowUnique]); revgoals. 
      + repeat rewrite assoc.
        do 2 rewrite BinCoproductIn2Commutes.
        etrans;[|apply pathsinv0, id_left].
        apply helper.
      + repeat rewrite assoc.
        repeat rewrite BinCoproductIn1Commutes.
        repeat rewrite <- assoc.
        repeat rewrite BinCoproductIn1Commutes.
        etrans.
        {
          rewrite assoc.
          apply cancel_postcomposition.
          apply pathsinv0.
          apply nat_trans_ax.
        }
        rewrite <- assoc.
        apply cancel_precomposition.
        apply (LModule_Mor_σ _ m).
    - intro c.
      repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
              coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
              BinCoproduct_of_functors_mor
              ; cbn).
      apply BinCoproductIn2Commutes.
  Qed.

  Definition mod_id_monad_mor : Monad_Mor mod_id_monad R :=  _ ,, mod_id_monad_mor_laws.

  (** M is a (M + Id)-module *)
  Definition M_IdM_mod : LModule mod_id_monad C := pb_LModule mod_id_monad_mor M.

  (** the inclusion M -> (M + Id) commutes with (M + Id)-substitution*)
  Lemma mod_M_idM_mod_laws : ∏ c, mod_M_idM  (IdM c) · mod_id_μ _ =  mod_id_M_mod _ · mod_M_idM _.
    intro c.
    repeat (unfold BinCoproduct_of_functors_ob, coproduct_nat_trans_data,
            coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data,
            BinCoproduct_of_functors_mor
            ; cbn).
    repeat rewrite id_left.
    apply BinCoproductIn1Commutes.
  Qed.

  (** The inclusion M -> (M + Id) is a module morphism *)
  Definition mod_M_idM_mod_Mor : LModule_Mor _ M_IdM_mod (Θ _) :=
    _ ,, mod_M_idM_mod_laws.

End InitAlg.

(** In this section, we prove that if R is a Σ-model, then
Σ(R) + Id is also a Σ-model *)
Section InitAlg2.

Context {C : category} (bc : BinCoproducts C).

(** The monad structure on Sig(R) + Id *)
Definition mod_id_model_monad {Sig : signature C} (R : model Sig) : Monad C :=
  mod_id_monad bc _ (model_τ R ).

Local Notation IdM := mod_id_model_monad.
Local Notation Θ := (tautological_LModule ).


(** Sig(R) + Id is given the following action:
<<
Sig(Sig(R) + Id) -> Sig(R) -> Sig(R) + Id
>>
*)
Definition mod_id_model_action {Sig : signature C} (R : model Sig) :
  LModule_Mor _ (Sig (IdM R)) (Θ _).
Proof.
  eapply (compose (C := category_LModule _ _)).
  - use ((# Sig  _)%ar); revgoals.
    + apply mod_id_monad_mor.
  - apply mod_M_idM_mod_Mor.
Defined.

(** Sig(R) + Id as a model *)
Definition mod_id_model {Sig : signature C} (R : model Sig) : model Sig :=
   mod_id_model_monad R ,, mod_id_model_action R.

(** The monad morphism Sig(R) + Id -> R is a model morphism *)
Definition mod_id_model_mor_laws {Sig : signature C} (R : model Sig) : 
    rep_fiber_mor_law (mod_id_model R) R (mod_id_monad_mor bc (Sig  R) (model_τ R)).
Proof.
  intro.
  etrans; [apply pathsinv0, assoc|].
  apply cancel_precomposition.
  apply BinCoproductIn1Commutes.
Qed.

Definition mod_id_model_mor {Sig : signature C} (R : model Sig) : 
  rep_fiber_mor (mod_id_model R) R  :=
  _ ,, mod_id_model_mor_laws R.

(** If R is the initial model, then the model morphism Sig(R) + Id -> R is an iso (the inverse
 is the initial arrow). The proof is similar to Lambek's theorem *)
Lemma iso_mod_id_model {Sig : signature C} (R : model Sig) (iR : isInitial (rep_fiber_category Sig) R)
      (** This is the initial arrow *)
      (fR := iscontrpr1 (iR(mod_id_model R)))
    :
  is_iso (C := rep_fiber_category Sig) (mod_id_model_mor R).
Proof.
  use is_iso_qinv.
  - exact fR.
  - assert (h1 : fR · mod_id_model_mor R
                 = identity (C:= rep_fiber_category _) R)
           by apply proofirrelevancecontr, iR.
    split.
    + apply rep_fiber_mor_eq_nt.
      apply nat_trans_eq;[apply homset_property|].
      intro c.
      cbn in fR.
      apply pathsinv0.
      use BinCoproduct_endo_is_identity; cbn; unfold coproduct_nat_trans_data; cbn; etrans;try apply assoc.
      * etrans;[apply cancel_postcomposition,  BinCoproductIn1Commutes|].
        etrans;[apply (rep_fiber_mor_ax fR)|].
        etrans;[apply assoc|].
        etrans;[|apply id_left].
        apply cancel_postcomposition.
        etrans;[|apply signature_id].
        etrans.
        {
              eassert (h :=  signature_comp Sig _ _).
              apply (maponpaths (T1 := LModule_Mor R _ _) (fun m => m c)) in h.
              simpl in h.
              rewrite id_right in h.
              apply pathsinv0.
              exact h.
        }
        eapply (paths_rect _ _
                (fun a eq => 
                   (# Sig)%ar (Monad_composition fR (mod_id_monad_mor bc (Sig (pr1 R)) (model_τ R))) c
                   = (# Sig)%ar a c));
          [|exact (maponpaths  pr1 h1)].
        apply idpath.
      * etrans;[apply cancel_postcomposition,  BinCoproductIn2Commutes|].
        apply (Monad_Mor_η fR).
    + exact h1.
Qed.

End InitAlg2.

                             
