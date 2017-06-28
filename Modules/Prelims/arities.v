Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.Monads.
(* Require Import Modules.Prelims.modules. *)
Require Import UniMath.CategoryTheory.LModules.


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).


(* 
-(* Une première définition possible des arités, en tant que functor_lifting
-
-Inconvénient : ce n'est pas démontré dans la bibliothèque DisplayCat que les functor_lifting
-forment une catégorie. Il faudra donc démontrer que les arités forment une catégorie.
-
-.*)
-Module Arites1.
-  Section Arities.
-
-    Variables (C D:Precategory).
-
-    Local Notation MONAD := (monadPrecategory C).
-    Local Notation BMOD := (bmod_disp C D).
-
-    (* Définitions des arités *)
-    Definition arity := functor_lifting BMOD (functor_identity MONAD).
-
-
-    (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
-    Lemma right_inverse_arity  (ar:arity ) :
-      ((pr1_precat BMOD)□ (lifted_functor ar) )    =  (functor_identity MONAD).
-    Proof.
-      intros.
-      apply subtypeEquality; [| reflexivity].
-      red.
-      intros;  apply isaprop_is_functor.
-      apply homset_property.
-    Qed.
-
-    (* Réciproque : si on a un foncteur qui vérifié ça, alors on a un functor lifting qui vaut
-lui-même *)
-
-    Section Reciproque.
-
-      Variable (F:functor MONAD (total_precat BMOD)).
-      Hypothesis (hF :  ((pr1_precat (bmod_disp C D))□ F) = (functor_identity (monadPrecategory C))).
-
-      Definition ar_inv_ob (x:MONAD): BMOD x.
-        intro x.
-
-        unfold BMOD; simpl.
-        change x with (functor_identity MONAD x).
-        rewrite <- hF.
-        exact (pr2 (F x)).
-      Defined.
-
-      Definition ar_inv_data : section_disp_data BMOD.
-        exists ar_inv_ob.
-        intros.
-        unfold mor_disp.
-        (* Trop dur, il faut faire des transport c'est trop la galère *)
-        change f with (#(functor_identity MONAD) f).
-        (* rewrite <- hF. *)
-      Abort.
-
-
-    End Reciproque.
-
-  End Arities.
-End Arites1.
*)
Inductive phantom {A:UU} (x:A) :UU := ttp.

Arguments ttp {_} _.

Notation TTP := (ttp _) (only parsing).

(* a category can be viewed as a display category with singletons.
*)
Section LiftCatDispCat.

  Context (C:category).

  Definition liftcat_disp_ob_mor : disp_cat_ob_mor C:=
    ((fun x => phantom x) ,, fun  _ _ _ _ f => phantom f).

  Definition liftcat_id_comp : disp_cat_id_comp _ liftcat_disp_ob_mor.
  Proof.
    split.
    - intros x xx.
      simpl.
      apply  ttp.
    - intros x y z f g xx yy zz ff gg.
      apply ttp.
  Defined.


  Definition liftcat_data : disp_cat_data _
    := (liftcat_disp_ob_mor ,, liftcat_id_comp).

  Lemma uniq_tt (A:UU) (x:A) (y:phantom x): y=ttp x.
    now destruct y.
  Qed.

  Lemma iscontr_ttp (A:UU) (x:A) :iscontr (phantom x).
  Proof.
    intros A x.
    exists (ttp x).
    apply uniq_tt.
  Qed.

  Lemma isasetphantom (A:UU) (x:A) : isaset (phantom x).
  Proof.
    intros A x.
    apply isasetifcontr.
    apply iscontr_ttp.
  Qed.    

  Lemma liftcat_axioms : disp_cat_axioms _ liftcat_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property; try  now rewrite uniq_tt;
      symmetry;    rewrite uniq_tt.
    apply isasetphantom.
  Qed.

  Definition liftcat_disp : disp_cat _ :=
    (liftcat_data ,, liftcat_axioms).


End LiftCatDispCat.




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
  Local Notation LMONAD := (liftcat_disp (PRE_MONAD)).
  Local Notation BMOD := (bmod_disp C C).
  Local Notation GEN_ARITY := (disp_functor_cat _ _ LMONAD BMOD).
  
  Local Notation PRE_ARITY :=
    (fiber_precategory GEN_ARITY (functor_identity _)).
  (* Arities are display functors over the identity *)
  Definition arity := (disp_functor (C:=PRE_MONAD) (C':=PRE_MONAD)
                      (functor_identity (precategory_Monad_data C)) LMONAD BMOD).
  Local Notation ARITY := arity.

  Coercion functor_over_from_ar (a:ARITY) :
    (disp_functor (C:=PRE_MONAD) (C':=PRE_MONAD)
                  (functor_identity (precategory_Monad_data C)) LMONAD BMOD)
  := a.

  Definition arity_Mor (a b:arity) :=
    disp_nat_trans
      (nat_trans_id (C:=PRE_MONAD) (C':=PRE_MONAD)
                    (functor_identity _)) a b.

  Coercion nat_trans_over_from_arity_Mor {a b} (f:arity_Mor a b) :
    disp_nat_trans
      (nat_trans_id (C:=PRE_MONAD) (C':=PRE_MONAD)
                    (functor_identity _)) a b
    := f.

  Definition arity_Precategory : category :=
    (PRE_ARITY,, has_homsets_fiber_category GEN_ARITY (functor_identity _)).

  (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
  Lemma right_inverse_arity3  (ar:ARITY )
    :  ((pr1_category BMOD)□ (total_functor ar) )    =  (pr1_category LMONAD).
  Proof.
    intros.
    apply subtypeEquality; [| reflexivity].
    red.
    intros;  apply isaprop_is_functor.
    apply homset_property.
  Qed.

  Local Notation Θ := tautological_LModule.


  (* a representation is a monad with a module morphisme from arity to itself *)
  Definition rep_ar (ar: ARITY) :=
    ∑ (R:MONAD),
    LModule_Mor R (ar (* (((ar:functor_over _ _ _):functor_over_data _ _ _)  *)R (ttp R) )
                (Θ R).

  Coercion Monad_from_rep_ar (ar:ARITY) (X:rep_ar ar) : MONAD := pr1 X.

  Definition μr {ar:ARITY} (X:rep_ar ar) := pr2 X.

  Definition functor_from_monad (R:MONAD) : functor C C := R.

  Definition functor_from_module {D:precategory} {R:MONAD} (S:LModule R D) : functor C D :=
    S.


  Definition ar_obj (a:ARITY) (M:MONAD) : LModule M _ := a M (ttp M).

  Delimit Scope arity_scope with ar.
  Notation AO := ar_obj.

  Definition ar_mor (a:ARITY) {M N:MONAD} (f:Monad_Mor  M N ) :
      LModule_Mor M (AO a M) (pb_LModule f (AO a N)).
  Proof.
    simpl.
    intros.
    apply (disp_functor_on_morphisms a).
    apply ttp.
  Defined.

  Lemma ar_mor_eq (a:ARITY) {M N:MONAD} (f:Monad_Mor  M N ) :
    @disp_functor_on_morphisms
      (category_Monad C) (category_Monad C)
      (functor_identity (precategory_Monad_data C))
      (liftcat_disp (category_Monad C))
      (bmod_disp C C)
      (disp_functor_data_from_disp_functor a) M N (ttp _) (ttp _) f (ttp _) =
    ar_mor a f .
  Proof.
    reflexivity.
  Qed.

  Notation "# F" := (ar_mor F)
                      (at level 3) : arity_scope.

  Delimit Scope arity_scope with ar.
    

  Definition armor_ob {a b : ARITY} (f:arity_Mor a b) (R:MONAD) :
    LModule_Mor _  (AO a R)
                (pb_LModule ((nat_trans_id (functor_identity PRE_MONAD)) R)
                                 (AO b R))
    := f R TTP.

  Definition rep_ar_mor_law {a b : ARITY} (M:rep_ar a) (N: rep_ar b)
             (f: arity_Mor a b) (g:Monad_Mor M N) :=
    ∏ c,  ((μr M) c);; (g c) =    (#a g )%ar c ;; armor_ob f N  c ;; μr N c .
  (* or the other way around a g ;;; f N : it is the same thanks to the naturality of f *)
    (* Π c,  ((μr M) c);; (pr1 g c) = armor_ob f M  c ;;  pr1 (#b g )%ar c ;; μr N c . *)

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

  Definition rep_ar_mor_law1 {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
             {f} (h:rep_ar_mor_mor a b M N f) :
    ∏ c,  ((μr M) c);; ( h c) =    (#a h )%ar c ;; armor_ob f N  c ;; μr N c 
    := pr2 h.



  Definition brep_disp_ob_mor : disp_cat_ob_mor PRE_ARITY:=
    (rep_ar,, rep_ar_mor_mor).


  Lemma brep_id_law (a : ARITY) (RM : brep_disp_ob_mor a) :
    (rep_ar_mor_law RM RM (identity (C:=PRE_ARITY) _) (Monad_identity _)).
    intros.
    intro c.
    apply pathsinv0.
    etrans.
    apply cancel_postcomposition.
    (* apply id_left *)
    apply id_right.
    etrans.
    apply cancel_postcomposition.
    eapply nat_trans_eq_pointwise.
    apply maponpaths.
    apply (disp_functor_id a).
    etrans.
    apply id_left.
    apply pathsinv0.
    apply id_right.
  Qed.

  Definition brep_id  (a : ARITY) (RM : brep_disp_ob_mor a) :
    RM -->[ identity (C:=PRE_ARITY) a] RM.
  Proof.
    intros.
    exists (Monad_identity _).
    apply brep_id_law.
  Defined.

  Lemma transport_disp_mor {C} {d:disp_cat C} {x y : C} {f g : C ⟦ x, y ⟧}
        (e : f = g)
        {xx : d x}     {yy : d y}
        (ff : xx -->[ f] yy)
        (Q : UU)
        (P : ∏ (z:C ⟦ x, y ⟧) ,xx -->[ z] yy -> Q  )
        :
    (P _ (transportf (mor_disp xx yy) e ff))  = P _ ff.
  Proof.
    destruct e.
    intros.
    apply idpath.
  Qed.


  Lemma transport_arity_mor (x y : ARITY) (f g : arity_Mor x y)
        (e : f = g)
        (xx : brep_disp_ob_mor x)
        (yy : brep_disp_ob_mor y)
        (ff : xx -->[ f] yy)
        (c : C) :
    pr1 (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 (pr1 ff) c.
  Proof.
    destruct e.
    intros.
    apply idpath.
  Qed.
  Lemma brep_transport    (x y : ARITY)
        (R S:MONAD)
        (f g : Monad_Mor R S )
        (e : f = g)
        (ff : pr1 x R (ttp _) -->[ f] pr1 y S (ttp _))
        (c : C) :
      pr1 (transportf _ e ff) c  = pr1 ff c .
  Proof.
    intros.
    simpl.
    now induction e.
  Qed.


  Lemma transport_arity_mor' (x y : ARITY) f g 
        (e : f = g)
        (ff : disp_nat_trans f x y)
        (R:MONAD)
        (c : C) :
    pr1 (pr1 (transportf (mor_disp (D:=GEN_ARITY) x y) e ff) R TTP) c
    = pr1 (pr1 ff R TTP) c.
  Proof.
    now induction e.
  Qed.

  Lemma eq_ar_pointwise  (a b c : ARITY) ( f : arity_Mor a b) (g : arity_Mor b c)
        (R:MONAD) x :
    armor_ob (compose (C:=PRE_ARITY) f g) R x = armor_ob f R x ;; armor_ob g R x .
  Proof.
    intros.
    cbn.
    etrans.
    use (transport_arity_mor' a c _ ).
    cbn.
    now rewrite  id_right.
  Qed.

  (* type de ff ; b (pr1 R) tt -->[ identity (pr1 R) ;; pr1 α] c (pr1 S) tt *)
  Lemma rep_ar_mor_mor_equiv (a b : ARITY) (R:brep_disp_ob_mor a)
        (S:brep_disp_ob_mor b) (f:arity_Mor a b)
        (a b: R -->[ f] S) :
    (∏ c, pr1 (pr1 a) c = pr1 (pr1 b) c) -> a = b.
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
  Lemma rep_ar_mor_mor_equiv_inv {a b : ARITY} {R:brep_disp_ob_mor a}
        {S:brep_disp_ob_mor b} {f:arity_Mor  a b}
        (u v: R -->[ f] S) : u = v -> (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c).
  Proof.
    intros.
    now induction X.
  Qed.


  (** Defining the composition in brep *)

  Lemma brep_comp_law  (a b c : ARITY) (f : arity_Mor a b) (g : arity_Mor b c)
             (R : brep_disp_ob_mor a) (S : brep_disp_ob_mor b)    (T : brep_disp_ob_mor c)
             (α:R -->[ f ] S) (β:S -->[g]  T) :
    (rep_ar_mor_law R T (compose (C:=PRE_ARITY) f g)
                    (compose (C:=PRE_MONAD) (monad_morphism_from_rep_ar_mor_mor α)
                             ( monad_morphism_from_rep_ar_mor_mor  β))).
  Proof.
    intros.
    intros x.
    cbn.

    rewrite assoc.
    etrans.
    apply cancel_postcomposition.
    use rep_ar_mor_law1.
    simpl.

    etrans.
    rewrite <- assoc.
    apply cancel_precomposition.
    use rep_ar_mor_law1.

    simpl.
    (* Cf diagramme à ce point *)

    symmetry.
    etrans.
    apply cancel_postcomposition.

    
    apply cancel_precomposition. 
    use (transport_arity_mor' a c _ _ _ _ (pr1 T) x).
    set (z := (# ( a))%ar _).
    set (hc := (@disp_functor_comp _ _ _ _ _ (a (* c *))) (pr1 R) (pr1 S) (pr1 T) (ttp _) (ttp _)
                                                     (ttp _)
                                                    (pr1 α) (pr1  β) (ttp _) (ttp _)).
    assert (hz := pathscomp0 (a:=z) (idpath _) hc).
    rewrite hz.

    simpl.
    rewrite ar_mor_eq,ar_mor_eq,id_right, id_right.

    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    assert (hg':= nat_trans_eq_pointwise
                    (LModule_Mor_equiv _ (homset_property _) _ _
                      (pr2 f _ _ (pr1 β) (ttp _) (ttp _) (ttp _)) ) x).
    cbn in hg'.
    rewrite id_right in hg'.
    etrans.
    apply hg'.
    (* set (e:=is_nat_trans_id _ _ _ _). *)
    clear.
    unfold transportb.
    set (e:= ! _).
    induction e.
    cbn.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition brep_comp (a b c : ARITY) f g
             (RMa : brep_disp_ob_mor a) (RMb : brep_disp_ob_mor b)    (RMc : brep_disp_ob_mor c)
             (mab:RMa -->[ f ] RMb) (mbc:RMb -->[g]  RMc) : RMa -->[f;;g] RMc.
    intros.
    exists (compose (C:=PRE_MONAD) (pr1 mab) (pr1 mbc)).
    apply brep_comp_law.
  Defined.


  Definition brep_id_comp : disp_cat_id_comp _ brep_disp_ob_mor.
  Proof.
    split.
    - apply brep_id.
    - apply brep_comp.
  Defined.


  Definition brep_data : disp_cat_data _
    := (brep_disp_ob_mor ,, brep_id_comp).




  Lemma brep_axioms : disp_cat_axioms arity_Precategory brep_data.
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

  Definition brep_disp : disp_cat arity_Precategory :=
    (brep_data ,, brep_axioms).

End LargeCatRep.
