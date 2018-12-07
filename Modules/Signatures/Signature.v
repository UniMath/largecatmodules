(* =================================================================================== *)
(** * Signatures and their models.

    Content:
    - Definition of signature (aka arity).
    - Definition of model of a signature.
    - Forgetful functor to the category of modules over a given monad R.                *)
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


Set Automatic Introduction.
Delimit Scope signature_scope with ar.


Section Signatures.

Context {C : category}.

Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).

(* ----------------------------------------------------------------------------------- *)
(** ** Definition of signature.                                                        *)
(* ----------------------------------------------------------------------------------- *)

Definition signature_data :=
  ∑ F : (∏ R : MONAD, LModule R C),
        ∏ (R S : MONAD) (f : Monad_Mor R S), LModule_Mor _ (F R) (pb_LModule f (F S)).
(* :(F R : bmod_disp C C R) -->[f] F S. *)

Definition signature_on_objects (a : signature_data) : ∏ R, LModule R C
  := pr1 a.

Coercion signature_on_objects : signature_data >-> Funclass.

Definition signature_on_morphisms  (F : signature_data) {R S : MONAD} 
  : ∏ (f: Monad_Mor R S), LModule_Mor _ (F R) (pb_LModule f (F S)) 
  := pr2 F R S.

Notation "# F" := (signature_on_morphisms F) (at level 3) : signature_scope.

(* ----------------------------------------------------------------------------------- *)
(** In classical terms, signatures are sections of a functor.  Here the same fact is
    expressed in the language of displayed cateteories with the following two
    property.                                                                          *)
(* ----------------------------------------------------------------------------------- *)

Definition signature_idax  (F : signature_data) :=
  ∏ (R : MONAD), ∏ x ,
  (# F (identity (C:= PRE_MONAD) R))%ar x  = identity  _.

Definition signature_compax  (F : signature_data) :=
  ∏ (R S T : MONAD) (f : PRE_MONAD ⟦R, S⟧) (g : PRE_MONAD ⟦S, T⟧),
  (#F  (f · g))%ar 
  = 
  (((# F f)%ar :(F R : bmod_disp C C R) -->[f] F S) ;; (#F g)%ar)%mor_disp.

Definition is_signature  (F : signature_data) : UU := signature_idax F × signature_compax F.

Lemma isaprop_is_signature (F : signature_data) : isaprop (is_signature F).
Proof.
  apply isofhleveldirprod.
  - repeat (apply impred; intro).
    apply homset_property.
  - repeat (apply impred; intro).
    apply (homset_property (category_LModule _ _)).
Qed.

Definition signature : UU := ∑ F : signature_data, is_signature F.

Definition signature_data_from_signature (F : signature) : signature_data := pr1 F.
Coercion signature_data_from_signature : signature >-> signature_data.

Notation Θ := tautological_LModule.

Definition tautological_signature_on_objects : ∏ (R : Monad C), LModule R C := Θ.
Definition tautological_signature_on_morphisms : 
  ∏ (R S : Monad C) (f : Monad_Mor R S), LModule_Mor _ (Θ R) (pb_LModule f (Θ S)) :=
  @monad_mor_to_lmodule C.


Definition tautological_signature_data : signature_data  :=
  tautological_signature_on_objects ,, tautological_signature_on_morphisms.

Lemma tautological_signature_is_signature :  is_signature tautological_signature_data.
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

Definition tautological_signature : signature := _ ,, tautological_signature_is_signature.

Definition signature_id (F : signature) :
  ∏ (R : MONAD), ∏ x ,
  ((# F (identity (C:= PRE_MONAD) R)))%ar x  = identity  _
  := pr1 (pr2 F).
(* ((# F (identity (C:= PRE_MONAD) R): LModule_Mor _ _ _ ))%ar x  = identity  _ *)

Definition signature_comp (F : signature) {R S T : MONAD} 
           (f : PRE_MONAD ⟦R,S⟧) (g : PRE_MONAD⟦S,T⟧) 
  : (#F  (f · g))%ar 
    = 
    ((# F f : (F R : bmod_disp C C R) -->[f] F S) %ar ;; (#F g)%ar)%mor_disp 
  := pr2 (pr2 F) _ _ _ _ _ .

(* Demander la version pointwise plutôt ? *)
Definition is_signature_Mor (F F' : signature_data)
           (t : ∏ R : MONAD, LModule_Mor R (F R)  (F' R)) 
  :=
    ∏ (R S : MONAD)(f : Monad_Mor R S),
    (((# F)%ar f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                  (t S : nat_trans _ _) 
    =
    ((t R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%ar f : nat_trans _ _).

  (* ((((# F)%ar f : LModule_Mor _ _ _) : nat_trans _ _) : [_,_]⟦_,_⟧) · *)
  (*                                                                   (t S : nat_trans _ _) = *)
  (* ((t R : nat_trans _ _) : [_,_]⟦_,_⟧) · (((#F')%ar f:LModule_Mor _ _ _) : nat_trans _ _). *)

Lemma isaprop_is_signature_Mor (F F' : signature_data) t :
  isaprop (is_signature_Mor F F' t).
Proof.
  repeat (apply impred; intro).
  apply homset_property.
Qed.

Definition signature_Mor  (F F' : signature_data) : UU := ∑ X, is_signature_Mor F F' X.
                            
Local Notation "F ⟹ G" := (signature_Mor F G) (at level 39) : signature_scope.

Lemma isaset_signature_Mor (F F' : signature) : isaset (signature_Mor F F').
Proof.
  apply (isofhleveltotal2 2).
  + apply impred ; intro t; apply (homset_property (category_LModule _ _)).
  + intro x; apply isasetaprop, isaprop_is_signature_Mor.
Qed.


Definition signature_Mor_data
 {F F' : signature_data}(a : signature_Mor F F') := pr1 a.
Coercion signature_Mor_data : signature_Mor >-> Funclass.

Definition signature_Mor_ax {F F' : signature} (a : signature_Mor F F') 
  : ∏ {R S : MONAD}(f : Monad_Mor R S),
    (((# F)%ar f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                  (a S : nat_trans _ _) 
    =
    ((a R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%ar f : nat_trans _ _)
  := pr2 a.

Lemma signature_Mor_ax_pw {F F' : signature} (a : signature_Mor F F') 
  : ∏ {R S : Monad C}(f : Monad_Mor R S) x,
    (((# F)%ar f :   nat_trans _ _) x) ·
                                       ((a S : nat_trans _ _) x) 
    =
    ((a R : nat_trans _ _)  x) · (((#F')%ar f : nat_trans _ _) x).
Proof.
  intros.
  assert (h := signature_Mor_ax a f).
  eapply nat_trans_eq_pointwise in h.
  apply h.
Qed.

(** Equality between two signature morphisms *)

Lemma signature_Mor_eq (F F' : signature)(a a' : signature_Mor F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { apply funextsec. intro; apply H. }
  apply (total2_paths_f H'), proofirrelevance, isaprop_is_signature_Mor.
Qed.

Lemma is_signature_Mor_comp {F G H : signature} (a : signature_Mor F G) (b : signature_Mor G H) 
  : is_signature_Mor F H (fun R  => (a R : category_LModule _ _ ⟦_,_⟧ ) · b R).
Proof.
  intros ? ? ?.
  etrans.
  apply (assoc (C:= [_,_])).
  etrans.
  apply ( cancel_postcomposition (C:= [_,_])).
  apply (signature_Mor_ax (F:=F) (F':=G) a f).
  rewrite <- (assoc (C:=[_,_])).
  etrans.
  apply (cancel_precomposition ([_,_])).
  apply signature_Mor_ax.
  rewrite assoc.
  apply idpath.
Qed.

Definition signature_precategory_ob_mor  : precategory_ob_mor := precategory_ob_mor_pair
   signature (fun F F' => signature_Mor F F').

Lemma is_signature_Mor_id (F : signature_data) : is_signature_Mor F F
     (fun R => identity (C:=category_LModule _ _) _).
Proof.
  intros ? ? ? .
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition signature_Mor_id (F : signature_data) : signature_Mor F F :=
    tpair _ _ (is_signature_Mor_id F).

Definition signature_Mor_comp {F G H : signature} (a : signature_Mor F G) (b : signature_Mor G H)
  : signature_Mor F H 
  := tpair _ _ (is_signature_Mor_comp a b).

Definition signature_precategory_data : precategory_data.
Proof.
  apply (precategory_data_pair (signature_precategory_ob_mor )).
  + intro a; simpl.
    apply (signature_Mor_id (pr1 a)).
  + intros a b c f g.
    apply (signature_Mor_comp f g).
Defined.

Lemma is_precategory_signature_precategory_data :
   is_precategory signature_precategory_data.
Proof.
  apply mk_is_precategory_one_assoc; simpl; intros.
  - unfold identity.
    simpl.
    apply signature_Mor_eq. 
    intro x; simpl.
    apply (id_left (C:=category_LModule _ _)).
  - apply signature_Mor_eq.
    intro x; simpl.
    apply (id_right (C:=category_LModule _ _)).
  - apply signature_Mor_eq.
    intro x; simpl.
    apply (assoc (C:=category_LModule _ _)).
Qed.

Definition signature_precategory : precategory :=
  tpair (fun C => is_precategory C)
        (signature_precategory_data)
        (is_precategory_signature_precategory_data).

Lemma signature_category_has_homsets : has_homsets signature_precategory.
Proof.
  intros F G.
  apply isaset_signature_Mor.
Qed.


Definition signature_category : category.
Proof.
  exists (signature_precategory).
  apply signature_category_has_homsets.
Defined.

End Signatures.

Arguments signature _ : clear implicits.

Notation "# F" := (signature_on_morphisms F) (at level 3) : signature_scope.




Section ForgetSigFunctor.
  Context {C : category} (R : Monad C) .
  Local Notation MOD := (precategory_LModule R C).
  Local Notation HAR := (signature_precategory (C:=C)).

  Definition forget_Sig_data : functor_data HAR MOD :=
    mk_functor_data (C := HAR) (C' := MOD)
                    (fun X => ((X : signature C) R))
                    (fun a b f => ((f : signature_Mor _ _ ) R)).

  Definition forget_Sig_is_functor : is_functor forget_Sig_data :=
    (( fun x => idpath _) : functor_idax forget_Sig_data)
      ,, ((fun a b c f g => idpath _) : functor_compax forget_Sig_data).

  Definition forget_Sig: functor HAR MOD  :=
    mk_functor forget_Sig_data forget_Sig_is_functor.
End ForgetSigFunctor.

(* large category of model defined as a display category

Not that contrary to the large category of modules, we do not construct the category of
models of a specific signature

This is an attempt to use directly the display category construction.
The category of represenations of a specific signature can be retrieved as a fiber category.


Let us recall what it the category of models of a signature B.
It is a pair (R,m) where R is monad and m a module morphism (on R) m : B(R) -> R.

Now, any morphism of signature F : A -> B induces a functor F* : Rep(B) -> Rep(A) defined by
F*(R,m) = (R, m o (F R))

That's how the large category of models is built.

*)


Section LargeCatRep.
  
Context {C : category}.
  
Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).
  

(* Signatures are display functors over the identity *)
Local Notation PRECAT_SIGNATURE  := (@signature_precategory C).

Notation signature  := (@signature C).
Local Notation SIGNATURE := signature.

Goal signature = ob PRECAT_SIGNATURE.
  reflexivity.
Abort.

Local Notation Θ := tautological_LModule.


  (* We define the displayed category of models of a signature
We could also define it as a displayed category over the monads
and we have no idea what that would look like *)

(** A model is a monad with a module morphisme from its image by the signature
 to itself *)
Definition model (ar : SIGNATURE) :=
  ∑ R : MONAD, LModule_Mor R (ar R) (Θ R).

Coercion Monad_from_rep_ar (ar : SIGNATURE) (X : model ar) : MONAD := pr1 X.

Definition model_τ {ar : signature} (X : model ar) := pr2 X.

Definition model_mor_law {a b : signature} (M : model a) (N : model b)
           (f : signature_Mor a b) (g : Monad_Mor M N) 
  := ∏ c : C, model_τ M c · g c = ((#a g)%ar:nat_trans _ _) c · f N c · model_τ N c .

Lemma isaprop_model_mor_law {a b : SIGNATURE} (M : model a) (N : model b)
      (f : signature_Mor a b) (g : Monad_Mor M N) 
  : isaprop (model_mor_law M N f g).
Proof.
  intros.
  apply impred; intro c.
  apply homset_property.
Qed.

Definition model_mor_mor (a b : SIGNATURE) (M : model a) (N : model b) f :=
  ∑ g:Monad_Mor M N, model_mor_law  M N f g.

Lemma isaset_model_mor_mor (a b : SIGNATURE) (M : model a) (N : model b) f :
  isaset (model_mor_mor a b M N f).
Proof.
  intros.
  apply isaset_total2 .
  - apply has_homsets_Monad.
  - intros.
    apply isasetaprop.
    apply isaprop_model_mor_law.
Qed.

Coercion monad_morphism_from_model_mor_mor {a b : SIGNATURE} {M : model a} {N : model b}
         {f} (h : model_mor_mor a b M N f) : Monad_Mor M N
  := pr1 h.

Definition model_mor_ax {a b : SIGNATURE} {M : model a} {N : model b}
           {f} (h:model_mor_mor a b M N f) :
  ∏ c, model_τ M c · h c = (#a h)%ar c · f N c · model_τ N c 
  := pr2 h.

Definition rep_disp_ob_mor : disp_cat_ob_mor PRECAT_SIGNATURE :=
  (model,, model_mor_mor).

Lemma rep_id_law (a : SIGNATURE) (RM : rep_disp_ob_mor a) :
  model_mor_law RM RM (identity (C:=PRECAT_SIGNATURE) _) (Monad_identity _).
Proof.
  intro c.
  apply pathsinv0.
  etrans.
    { apply cancel_postcomposition, id_right. }
  etrans.
    { apply cancel_postcomposition, (signature_id a (pr1 RM) c). } 
  etrans; [  apply id_left |].
  apply pathsinv0.
  apply id_right.
Qed.

Definition rep_id  (a : SIGNATURE) (RM : rep_disp_ob_mor a) :
  RM -->[ identity (C:=PRECAT_SIGNATURE) a] RM.
Proof.
  intros.
  exists (Monad_identity _).
  apply rep_id_law.
Defined.



Lemma transport_signature_mor (x y : SIGNATURE) (f g : signature_Mor x y)
      (e : f = g)
      (xx : rep_disp_ob_mor x)
      (yy : rep_disp_ob_mor y)
      (ff : xx -->[ f] yy)
      (c : C) :
  pr1 (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 (pr1 ff) c.
Proof.
  induction e.
  apply idpath.
Qed.




(** type de ff ; b (pr1 R) tt -->[ identity (pr1 R) ;; pr1 α] c (pr1 S) tt *)
Lemma model_mor_mor_equiv (a b : SIGNATURE) (R:rep_disp_ob_mor a)
      (S:rep_disp_ob_mor b) (f:signature_Mor a b)
      (u v: R -->[ f] S) :
  (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c) -> u = v.
Proof.
  intros.
  use (invmap (subtypeInjectivity _ _ _ _  )). 
  - intro g.
    apply isaprop_model_mor_law.
  - use (invmap (Monad_Mor_equiv _ _  _  )).  
     +  apply homset_property.
     +  apply nat_trans_eq.
        apply homset_property.
        assumption.
Qed.


(** Defining the composition in rep *)

Lemma rep_comp_law  (a b c : SIGNATURE) (f : signature_Mor a b) (g : signature_Mor b c)
      (R : rep_disp_ob_mor a) (S : rep_disp_ob_mor b)    (T : rep_disp_ob_mor c)
      (α:R -->[ f ] S) (β:S -->[g]  T) :
  (model_mor_law R T (compose (C:=PRECAT_SIGNATURE) f g)
                  (compose (C:=PRE_MONAD) (monad_morphism_from_model_mor_mor α)
                           ( monad_morphism_from_model_mor_mor  β))).
Proof.
  intro x.
  cbn.    
  rewrite assoc.
  etrans.
  { apply cancel_postcomposition.
    use model_mor_ax. }
    
  etrans.
  { rewrite <- assoc.
    apply cancel_precomposition.
    use model_mor_ax. }
  
  (* Cf diagramme à ce point *)
  
  symmetry.
  repeat rewrite assoc.
  apply cancel_postcomposition.
  apply cancel_postcomposition.
  etrans.
  {
    apply cancel_postcomposition.
    assert (h:= (signature_comp a (pr1 α) (pr1 β))).
    apply LModule_Mor_equiv in h.
    eapply nat_trans_eq_pointwise in h.
    apply h.
    apply homset_property.
  }
  cbn.
  rewrite id_right.
  repeat rewrite <- assoc.
  apply cancel_precomposition.
  assert (h:=signature_Mor_ax f (pr1 β)).
  eapply nat_trans_eq_pointwise in h.
  apply h.
Qed.

Definition rep_comp (a b c : SIGNATURE) f g
           (RMa : rep_disp_ob_mor a) 
           (RMb : rep_disp_ob_mor b)    
           (RMc : rep_disp_ob_mor c)
           (mab : RMa -->[ f ] RMb) 
           (mbc:RMb -->[g]  RMc) 
  : RMa -->[f·g] RMc.
Proof.
  intros.
  exists (compose (C:=PRE_MONAD) (pr1 mab) (pr1 mbc)).
  apply rep_comp_law.
Defined.


Definition rep_id_comp : disp_cat_id_comp _ rep_disp_ob_mor.
Proof.
  split.
  - apply rep_id.
  - apply rep_comp.
Defined.


Definition rep_data : disp_cat_data _ := (rep_disp_ob_mor ,, rep_id_comp).


Lemma rep_axioms : disp_cat_axioms signature_category rep_data.
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

Definition rep_disp : disp_cat signature_category := rep_data ,, rep_axioms.

Definition pb_rep {a a' : signature} (f : signature_Mor a a') (R : model a') : model a :=
  ((R : MONAD) ,, ((f R : category_LModule _ _ ⟦_, _⟧) · model_τ R)).

Lemma pb_rep_to_law {a a'} (f : signature_category ⟦ a, a' ⟧) (R : model a') :
  model_mor_law (pb_rep f R) R f (identity ((R : MONAD) : PRE_MONAD)).
Proof.
  intros.
  intro c.
  cbn.
  rewrite id_right.
  apply cancel_postcomposition.
  apply pathsinv0.
  etrans; [| apply id_left].
  apply cancel_postcomposition.
  apply signature_id.
Qed.

(** ** Now the cleaving *)


Definition pb_rep_to {a a'} (f : signature_category ⟦ a, a' ⟧) (R : model a') :
  (pb_rep f R : rep_disp a) -->[f] R :=
  (identity (C:=PRE_MONAD) (R:MONAD),, pb_rep_to_law f R).

Lemma rep_mor_law_pb {a a' b} (f : signature_category ⟦ a, a' ⟧) (g : signature_category ⟦ b, a ⟧)
      (S : model b) (R : model a') (hh : (S : rep_disp _) -->[g·f] R) :
  model_mor_law S (pb_rep f R) g (hh : model_mor_mor _ _ _ _ _ ).
Proof.
  intros.
  destruct hh as [hh h].
  intro c.
  etrans; [apply h|].
  cbn.
  repeat rewrite assoc.
  apply idpath.
Qed.

Lemma rep_mor_pb {a a' b} (f : signature_category ⟦ a, a' ⟧) (g : signature_category ⟦ b, a ⟧)
      (S : model b) (R : model a') (hh : (S : rep_disp _) -->[g·f] R) :
   (S : rep_disp _) -->[ g] pb_rep f R.
Proof.
    use tpair.
    + apply hh.
    + apply rep_mor_law_pb.
Defined.
    
Definition pb_rep_to_cartesian {a a'} (f : signature_category ⟦ a, a' ⟧)
           (R : model a') : is_cartesian ((pb_rep_to f R) :
                                             (pb_rep f R : rep_disp a) -->[_] R).
Proof.
  intros.
  intro b.
  intros g S hh.
  unshelve eapply unique_exists.
  - apply rep_mor_pb.
    exact hh.
  - abstract (apply model_mor_mor_equiv;
    intro c;
    apply id_right).
  - intro u.
    apply isaset_model_mor_mor.
  - abstract (intros u h;
    apply model_mor_mor_equiv;
    intro c;
    cbn;
    rewrite <- h;
    apply pathsinv0;
    apply id_right).
Defined.
           (* (pb_rep f R) R f *)
Lemma rep_cleaving : cleaving rep_disp.
Proof.
  intros a a' f R.
  red.
  use tpair;[ |use tpair].
  - apply (pb_rep f R).
  - apply pb_rep_to.
  - apply pb_rep_to_cartesian.
Defined.
     
End LargeCatRep.

Arguments rep_disp _ : clear implicits.
Arguments rep_cleaving : clear implicits.



(*
Lemma transport_disp_mor {C} {d:disp_cat C} {x y : C} {f g : C ⟦ x, y ⟧}
        (e : f = g)
        {xx : d x}     {yy : d y}
        (ff : xx -->[ f] yy)
        (Q : UU)
        (P : ∏ (z:C ⟦ x, y ⟧) ,xx -->[ z] yy -> Q)
    :
      (P _ (transportf (mor_disp xx yy) e ff))  = P _ ff.
  Proof.
    destruct e.
    intros.
    apply idpath.
  Qed.
*)

  (*
Lemma rep_ar_mor_mor_equiv_inv {a b : SIGNATURE} {R:rep_disp_ob_mor a}
      {S:rep_disp_ob_mor b} {f:signature_Mor  a b}
      (u v: R -->[ f] S) 
  : u = v -> (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c).
Proof.
  intros.
  now induction X.
Qed.
   *)

  (*
 Lemma transport_signature_mor' (x y : SIGNATURE) f g 
        (e : f = g)
        (ff : disp_nat_trans f x y)
        (R:MONAD)
        (c : C) :
    pr1 (pr1 (transportf (mor_disp (D:=GEN_SIGNATURE) x y) e ff) R tt) c
    = pr1 (pr1 ff R tt) c.
  Proof.
    now induction e.
  Qed.
*)

  (*
  Lemma eq_ar_pointwise  (a b c : SIGNATURE)  (f:PRECAT_SIGNATURE⟦ a,b⟧)
        (g:PRECAT_SIGNATURE⟦ b,c⟧) (R:MONAD) x :
    ( (f ;; g) `` R) x = ( f`` R) x ;; ( g`` R) x .
  Proof.
    intros.
    etrans.
    use (transport_signature_mor' a c _ ).
    cbn.
    now rewrite  id_right.
  Qed.
*)

  (*
  Lemma rep_transport (x y : SIGNATURE)
        (R S:MONAD)
        (f g : Monad_Mor R S )
        (e : f = g)
        (ff : pr1 x R (tt) -->[ f] pr1 y S (tt))
        (c : C) :
    pr1 (transportf _ e ff) c  = pr1 ff c .
  Proof.
    intros.
    simpl.
    now induction e.
  Qed.
*)

  (* Notation "# F" := (ar_mor F) (at level 3) : signature_scope. *)

  (*
  Definition ar_mor_pw {a b : SIGNATURE} (f:signature_Mor a b) (R:MONAD) :
    LModule_Mor _  (a ` R)
                (pb_LModule ((nat_trans_id (functor_identity PRE_MONAD)) R)
                            (b ` R))
    := (f : signature_mor (a:signature) (b:signature)) R.
*)

  (* Infix "``" := ar_mor_pw (at level 25) : signature_scope . *)
