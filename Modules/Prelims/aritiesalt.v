Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.


Set Automatic Introduction.
Delimit Scope arity_scope with ar.
Section Arities.
  Context {C : category}.
  Local Notation MONAD := (Monad C).
  Local Notation PRE_MONAD := (category_Monad C).
  Local Notation BMOD := (bmod_disp C C).

  Definition arity_data :=
    ∑ F : (∏ R : MONAD, LModule R C),
          ∏ (R S : MONAD) (f : Monad_Mor R S), LModule_Mor _ (F R) (pb_LModule f (F S)).
    (* :(F R : bmod_disp C C R) -->[f] F S. *)

  Definition arity_on_objects  (a : arity_data) : ∏ R, LModule R C :=
    pr1 a.

  Coercion arity_on_objects : arity_data >-> Funclass.
  Definition arity_on_morphisms  (F : arity_data)
             { R S : MONAD } : ∏ (f: Monad_Mor R S), LModule_Mor _ (F R)
                                                                 (pb_LModule f (F S)) :=
     pr2 F R S.

  Notation "# F" := (arity_on_morphisms F) (at level 3) : arity_scope.


Definition arity_idax  (F : arity_data) :=
          ( ∏ (R : MONAD), ∏ x ,
           ((# F (identity (C:= PRE_MONAD) R)))%ar x  = identity  _).

Definition arity_compax  (F : arity_data) :=
  ∏ (R S T : MONAD) (f : PRE_MONAD ⟦R, S⟧) (g : PRE_MONAD ⟦S, T⟧),
               (#F  (f ;; g)%mor)%ar = (((# F f)%ar:(F R : bmod_disp C C R) -->[f] F S) ;; (#F g)%ar)%mor_disp.
Definition is_arity  (F : arity_data) :=
  dirprod ( arity_idax F ) ( arity_compax F ) .

Lemma isaprop_is_arity (F : arity_data) : isaprop (is_arity F).
Proof.
Admitted.

Definition arity : UU :=
  total2 ( fun F : arity_data => is_arity F ).

Definition arity_data_from_arity (F : arity) : arity_data := pr1 F.
Coercion arity_data_from_arity : arity >-> arity_data.

Definition arity_id (F : arity) :
  ∏ (R : MONAD), ∏ x ,
           (* ((# F (identity (C:= PRE_MONAD) R): LModule_Mor _ _ _ ))%ar x  = identity  _ *)
           ((# F (identity (C:= PRE_MONAD) R)))%ar x  = identity  _
 := pr1 (pr2 F).


Definition arity_comp (F : arity) {R S T : MONAD} (f : PRE_MONAD ⟦R,S⟧) (g : PRE_MONAD⟦S,T⟧) :
                 (#F  (f ;; g)%mor)%ar = ((# F f : (F R : bmod_disp C C R) -->[f] F S) %ar ;; (#F g)%ar)%mor_disp 
  := pr2 (pr2 F) _ _ _ _ _ .

Definition is_arity_Mor 
  (F F' : arity_data)
  (t : ∏ R : MONAD, LModule_Mor R (F R)  (F' R)) :=
  ∏ (R S : MONAD)(f : Monad_Mor R S),
  (((# F)%ar f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                                    (t S : nat_trans _ _) =
  ((t R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%ar f : nat_trans _ _).
  (* ((((# F)%ar f : LModule_Mor _ _ _) : nat_trans _ _) : [_,_]⟦_,_⟧) · *)
  (*                                                                   (t S : nat_trans _ _) = *)
  (* ((t R : nat_trans _ _) : [_,_]⟦_,_⟧) · (((#F')%ar f:LModule_Mor _ _ _) : nat_trans _ _). *)

Lemma isaprop_is_arity_Mor (F F' : arity_data) t :
  isaprop (is_arity_Mor F F' t).
Admitted.

Definition arity_Mor  (F F' : arity_data) : UU :=
  total2 (is_arity_Mor F F').
                            
Notation "F ⟹ G" := (arity_Mor F G) (at level 39) : arity_scope.

Definition arity_Mor_data
 {F F' : arity_data}(a : arity_Mor F F') := pr1 a.
Coercion arity_Mor_data : arity_Mor >-> Funclass.

Definition arity_Mor_ax 
  {F F' : arity} (a : arity_Mor F F') : ∏ {R S : MONAD}(f : Monad_Mor R S),
  (((# F)%ar f :   nat_trans _ _) : [_,_]⟦_,_⟧) ·
                                                                    (a S : nat_trans _ _) =
  ((a R : nat_trans _ _) : [_,_]⟦_,_⟧) · ((#F')%ar f : nat_trans _ _)
  := pr2 a.
Lemma is_arity_Mor_comp {F G H : arity_data} (a : arity_Mor F G) (b : arity_Mor G H): is_arity_Mor F H
     (fun R  => ((a R : category_LModule _ _ ⟦_,_⟧ ) · b R)).
Proof.
Admitted.

Definition arity_precategory_ob_mor  : precategory_ob_mor := precategory_ob_mor_pair
   arity (fun F F' => arity_Mor F F').

Lemma is_arity_Mor_id (F : arity_data) : is_arity_Mor F F
     (fun R => identity (C:=category_LModule _ _) _).
Proof.
  intros ? ? ? .
  now rewrite id_left, id_right.
Qed.

Definition arity_Mor_id (F : arity_data) : arity_Mor F F :=
    tpair _ _ (is_arity_Mor_id F).

Definition arity_Mor_comp {F G H : arity} (a : arity_Mor F G) (b : arity_Mor G H): arity_Mor F H :=
    tpair _ _ (is_arity_Mor_comp a b).

Definition arity_precategory_data : precategory_data.
Proof.
  apply (precategory_data_pair (arity_precategory_ob_mor )).
  + intro a; simpl.
    apply (arity_Mor_id (pr1 a)).
  + intros a b c f g.
    apply (arity_Mor_comp f g).
Defined.

Lemma is_precategory_arity_precategory_data :
   is_precategory arity_precategory_data.
Proof.
Admitted.

Definition arity_precategory : precategory :=
  tpair (fun C => is_precategory C)
        (arity_precategory_data)
        (is_precategory_arity_precategory_data).

Lemma arity_category_has_homsets : has_homsets arity_precategory.
Proof.
Admitted.


Definition arity_category : category.
Proof.
  exists (arity_precategory).
  apply arity_category_has_homsets.
Defined.



End Arities.
  Notation "# F" := (arity_on_morphisms F) (at level 3) : arity_scope.

(* large category of representation defined as a display category

Not that contrary to the large category of modules, we do not construct the category of
representations of a specific arity

This is an attempt to use directly the display category construction.
The category of represenations of a specific arity can be retrieved as a fiber category.


Let us recall what it the category of representations of an arity B.
It is a pair (R,m) where R is monad and m a module morphism (on R) m : B(R) -> R.

Now, any morphism of arity F : A -> B induces a functor F* : Rep(B) -> Rep(A) defined by
F*(R,m) = (R, m o (F R))

That's how the large category of representations is built.



 *)


Section LargeCatRep.

  Variable (C :category).
  
  Local Notation MONAD := (Monad C).
  Local Notation PRE_MONAD := (category_Monad C).
  Local Notation BMOD := (bmod_disp C C).
  

  (* Arities are display functors over the identity *)
  Local Notation PRECAT_ARITY  := (@arity_precategory C).

  Notation arity  := (@arity C).
  Local Notation ARITY := arity.

  Goal arity = ob PRECAT_ARITY.
    reflexivity.
  Abort.

  (* Question B: why do you not define the category of arities to be the fiber 
               category over the identity functor on PRE_MONAD ? *)



  (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
  (*
  Lemma right_inverse_arity  (ar:ARITY )
    :  (pr1_category BMOD) □ (total_functor ar) = pr1_category LMONAD.
  Proof.
    intros.
    apply subtypeEquality; [| reflexivity].
    intro x ;  apply isaprop_is_functor.
    apply homset_property.
  Qed.
*)

  Local Notation Θ := tautological_LModule.





  (* Notation "# F" := (ar_mor F) (at level 3) : arity_scope. *)

  (*
  Definition ar_mor_pw {a b : ARITY} (f:arity_Mor a b) (R:MONAD) :
    LModule_Mor _  (a ` R)
                (pb_LModule ((nat_trans_id (functor_identity PRE_MONAD)) R)
                            (b ` R))
    := (f : arity_mor (a:arity) (b:arity)) R.
*)

  (* Infix "``" := ar_mor_pw (at level 25) : arity_scope . *)

  (* We define the displayed category of representations of an arity
We could also define it as a displayed category over the monads
and we have no idea what that would look like *)

  (* A representation is a monad with a module morphisme from its image by the arity
 to itself *)
  Definition rep_ar (ar: ARITY) :=
    ∑ (R:MONAD),
    LModule_Mor R (ar R) (Θ R).

  Coercion Monad_from_rep_ar (ar:ARITY) (X:rep_ar ar) : MONAD := pr1 X.

  Definition rep_τ {ar:arity} (X:rep_ar ar) := pr2 X.


  Definition rep_ar_mor_law {a b : arity} (M:rep_ar a) (N: rep_ar b)
             (f: arity_Mor a b) (g:Monad_Mor M N) :=
    ∏ c, rep_τ M c ;; g c = ((#a g)%ar:nat_trans _ _) c ;;  (f N) c ;; rep_τ N c .

  Lemma isaprop_rep_ar_mor_law {a b : ARITY} (M:rep_ar a) (N: rep_ar b)
        (f: arity_Mor a b) (g:Monad_Mor M N) :
    isaprop (rep_ar_mor_law (M:rep_ar a) (N: rep_ar b) f g).
  Proof.
    intros.
    apply impred; intro c.
    apply homset_property.
  Qed.

  Definition rep_ar_mor_mor (a b : ARITY) (M:rep_ar a) (N: rep_ar b) f :=
    ∑ g:Monad_Mor M N, rep_ar_mor_law  M N f g.

  Lemma isaset_rep_ar_mor_mor (a b : ARITY) (M:rep_ar a) (N: rep_ar b) f :
    isaset (rep_ar_mor_mor a b M N f).
  Proof.
    intros.
    apply isaset_total2 .
    apply has_homsets_Monad.
    intros.
    apply isasetaprop.
    apply isaprop_rep_ar_mor_law.
  Qed.

  Coercion monad_morphism_from_rep_ar_mor_mor {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
           {f} (h:rep_ar_mor_mor a b M N f) : Monad_Mor M N
    := pr1 h.

  Definition rep_ar_mor_ax {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
             {f} (h:rep_ar_mor_mor a b M N f) :
    ∏ c,  ((rep_τ M) c);; ( h c) = (#a h )%ar c ;; ( f N)  c ;; rep_τ N c 
    := pr2 h.

  Definition rep_disp_ob_mor : disp_cat_ob_mor PRECAT_ARITY :=
    (rep_ar,, rep_ar_mor_mor).

  Lemma rep_id_law (a : ARITY) (RM : rep_disp_ob_mor a) :
    rep_ar_mor_law RM RM (identity (C:=PRECAT_ARITY) _) (Monad_identity _).
  Proof.
    intros.
    intro c.
    apply pathsinv0.
    etrans.
    apply cancel_postcomposition.
    (* apply id_left *)
    apply id_right.
    etrans.
    apply cancel_postcomposition.
    apply (arity_id a (pr1 RM) c).
    etrans.
    apply id_left.
    apply pathsinv0.
    apply id_right.
  Qed.

  Definition rep_id  (a : ARITY) (RM : rep_disp_ob_mor a) :
    RM -->[ identity (C:=PRECAT_ARITY) a] RM.
  Proof.
    intros.
    exists (Monad_identity _).
    apply rep_id_law.
  Defined.

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


  Lemma transport_arity_mor (x y : ARITY) (f g : arity_Mor x y)
        (e : f = g)
        (xx : rep_disp_ob_mor x)
        (yy : rep_disp_ob_mor y)
        (ff : xx -->[ f] yy)
        (c : C) :
    pr1 (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 (pr1 ff) c.
  Proof.
    now induction e.
  Qed.

  (*
  Lemma rep_transport (x y : ARITY)
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


  (*
 Lemma transport_arity_mor' (x y : ARITY) f g 
        (e : f = g)
        (ff : disp_nat_trans f x y)
        (R:MONAD)
        (c : C) :
    pr1 (pr1 (transportf (mor_disp (D:=GEN_ARITY) x y) e ff) R tt) c
    = pr1 (pr1 ff R tt) c.
  Proof.
    now induction e.
  Qed.
*)

  (*
  Lemma eq_ar_pointwise  (a b c : ARITY)  (f:PRECAT_ARITY⟦ a,b⟧)
        (g:PRECAT_ARITY⟦ b,c⟧) (R:MONAD) x :
    ( (f ;; g) `` R) x = ( f`` R) x ;; ( g`` R) x .
  Proof.
    intros.
    etrans.
    use (transport_arity_mor' a c _ ).
    cbn.
    now rewrite  id_right.
  Qed.
*)

  (* type de ff ; b (pr1 R) tt -->[ identity (pr1 R) ;; pr1 α] c (pr1 S) tt *)
  Lemma rep_ar_mor_mor_equiv (a b : ARITY) (R:rep_disp_ob_mor a)
        (S:rep_disp_ob_mor b) (f:arity_Mor a b)
        (u v: R -->[ f] S) :
    (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c) -> u = v.
  Proof.
    intros.
    use (invmap (subtypeInjectivity _ _ _ _  )) ; cycle 1.
    use (invmap (Monad_Mor_equiv _ _  _  )) ; cycle 1.
    apply nat_trans_eq.
    apply homset_property.
    assumption.
    apply homset_property.
    intro g.
    apply isaprop_rep_ar_mor_law.
  Qed.

  (*
Lemma rep_ar_mor_mor_equiv_inv {a b : ARITY} {R:rep_disp_ob_mor a}
      {S:rep_disp_ob_mor b} {f:arity_Mor  a b}
      (u v: R -->[ f] S) 
  : u = v -> (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c).
Proof.
  intros.
  now induction X.
Qed.
   *)

  (** Defining the composition in rep *)

  Lemma rep_comp_law  (a b c : ARITY) (f : arity_Mor a b) (g : arity_Mor b c)
        (R : rep_disp_ob_mor a) (S : rep_disp_ob_mor b)    (T : rep_disp_ob_mor c)
        (α:R -->[ f ] S) (β:S -->[g]  T) :
    (rep_ar_mor_law R T (compose (C:=PRECAT_ARITY) f g)
                    (compose (C:=PRE_MONAD) (monad_morphism_from_rep_ar_mor_mor α)
                             ( monad_morphism_from_rep_ar_mor_mor  β))).
  Proof.
    intros.
    intros x.
    cbn.
    
    rewrite assoc.
    etrans.
    apply cancel_postcomposition.
    use rep_ar_mor_ax.
    simpl.
    
    etrans.
    rewrite <- assoc.
    apply cancel_precomposition.
    use rep_ar_mor_ax.
    
    simpl.
    (* Cf diagramme à ce point *)
    
    symmetry.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    etrans.
    {
    apply cancel_postcomposition.
    assert (h:= (arity_comp a (pr1 α) (pr1 β))).
    apply LModule_Mor_equiv in h.
    eapply nat_trans_eq_pointwise in h.
    apply h.
    apply homset_property.
    }
    cbn.
    rewrite id_right.
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    assert (h:=arity_Mor_ax f (pr1 β)).
    eapply nat_trans_eq_pointwise in h.
    apply h.
  Qed.

  Definition rep_comp (a b c : ARITY) f g
             (RMa : rep_disp_ob_mor a) 
             (RMb : rep_disp_ob_mor b)    
             (RMc : rep_disp_ob_mor c)
             (mab : RMa -->[ f ] RMb) 
             (mbc:RMb -->[g]  RMc) 
    : RMa -->[f;;g] RMc.
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


  Definition rep_data : disp_cat_data _
    := (rep_disp_ob_mor ,, rep_id_comp).


  Lemma rep_axioms : disp_cat_axioms arity_category rep_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    -  apply rep_ar_mor_mor_equiv.
       intros c.
       etrans. apply id_left.
       symmetry.
       apply transport_arity_mor.
    - apply rep_ar_mor_mor_equiv.
      intro c.
      etrans. apply id_right.
      symmetry.
      apply transport_arity_mor.
    - set (heqf:= assoc f g h).
      apply rep_ar_mor_mor_equiv.
      intros c.
      etrans; cycle 1.
      symmetry.
      apply transport_arity_mor.
      cbn.
    now rewrite assoc.
  -  apply isaset_rep_ar_mor_mor.
Qed.

Definition rep_disp : disp_cat arity_category := rep_data ,, rep_axioms.


Definition pb_rep {a a' : arity} (f : arity_Mor a a') (R : rep_ar a') : rep_ar a :=
  ((R : MONAD) ,, ((f R : category_LModule _ _ ⟦_, _⟧);;  rep_τ R)%mor).

(*
Definition id_disp_exp 
  : ∏ (C : precategory_data) (D : disp_cat_data C) (x : C) (xx : D x), xx -->[ identity x] xx :=
  @id_disp.

Definition disp_functor_on_mor_exp :
∏ (C' C : precategory_data) (F : functor_data C' C) (D' : disp_cat_data C') 
(D : disp_cat_data C) (FF : disp_functor_data F D' D) (x y : C') (xx : D' x) 
(yy : pr1 D' y) (f : C' ⟦ x, y ⟧), xx -->[ f] yy → FF x xx -->[ (# F)%Cat f] FF y yy :=
  @disp_functor_on_morphisms.

*)
Lemma pb_rep_to_law {a a'} (f : arity_category ⟦ a, a' ⟧) (R : rep_ar a') :
  rep_ar_mor_law (pb_rep f R) R f (identity ((R : MONAD) : PRE_MONAD)).
Proof.
  intros.
  intro c.
  cbn.
  rewrite id_right.
  apply cancel_postcomposition.
  apply pathsinv0.
  etrans; [| apply id_left].
  apply cancel_postcomposition.
  apply arity_id.
Qed.

Definition pb_rep_to {a a'} (f : arity_category ⟦ a, a' ⟧) (R : rep_ar a') :
  (pb_rep f R : rep_disp a) -->[f] R :=
  (identity (C:=PRE_MONAD) (R:MONAD),, pb_rep_to_law f R).

Definition paths_exp : ∏ A : Type, A → A → Type := @paths.
Lemma rep_mor_law_pb {a a' b} (f : arity_category ⟦ a, a' ⟧) (g : arity_category ⟦ b, a ⟧)
      (S : rep_ar b) (R : rep_ar a') (hh : (S : rep_disp _) -->[ g;; f] R) :
  rep_ar_mor_law S (pb_rep f R) g (hh : rep_ar_mor_mor _ _ _ _ _ ).
Proof.
  intros.
  destruct hh as [hh h].
  intro c.
  etrans; [apply h|].
  etrans; [|apply assoc].
  etrans; [eapply pathsinv0; apply assoc|].
  apply cancel_precomposition.
  cbn.
  now rewrite assoc.
Qed.

Definition pb_rep_to_cartesian {a a'} (f : arity_category ⟦ a, a' ⟧)
           (R : rep_ar a') : is_cartesian ((pb_rep_to f R) :
                                             (pb_rep f R : rep_disp a) -->[_] R).
Proof.
  intros.
  intro b.
  intros g S hh.
  mkpair.
  unshelve eapply unique_exists.
  - cbn.
    mkpair.
    + apply hh.
    + apply rep_mor_law_pb.
      
  - 
Admitted.
           (* (pb_rep f R) R f *)
Lemma rep_cleaving : cleaving rep_disp.
Proof.
  intros a a' f R.
  red.
  mkpair;[ |mkpair].
  - apply (pb_rep f R).
  - apply pb_rep_to.
  - apply pb_rep_to_cartesian.
Defined.
     
End LargeCatRep.

Arguments ar_obj [_] _ _.
Infix "`" := ar_obj (at level 25) : arity_scope .

Arguments ar_mor_pw [_ _ _] _ _.
Infix "``" := ar_mor_pw (at level 25) : arity_scope .

