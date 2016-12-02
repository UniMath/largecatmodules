
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.Monads.
Require Import Largecat.modules.
(* Require Import UniMath.CategoryTheory.Modules. *)


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).


Ltac pr1_norm  :=
  match goal with
    |- context f [pr1 ?T] =>
    let x:=type of (pr1 T) in
    change (pr1 T) with (T:x) (* (RModule_data_from_RModule _ _ T) *)
  end.

Ltac receq t t' :=
  let u := constr:(t,t') in
  match u with
    (?f ?x, ?f' ?x') =>
    let h := fresh in
    cut (x=x');[intro h; try rewrite h; clear h;
                receq f f'|]
  | (?x,?x')=>
    let h := fresh in
    cut (x=x');[intro h; try rewrite h; clear h|]
  end.


Ltac my_f_equal :=
  match goal with
  | |- paths ?x ?y => receq x y; try reflexivity
 end.


Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section Pullback_module.
  Context {B:precategory} {M M':Monad B} (m: Monad_Mor M M').

  Context {C:precategory}.

  Variable (T:RModule M' C).

  Definition pbm_σ : T □ M ⟶ T :=  (T ∘ m) ;;; σ _ T.

  Definition pbm_data : Σ F : functor B C, F □ M ⟶ F := tpair _ (T:functor B C) pbm_σ.

  Definition pbm_laws : RModule_laws M pbm_data.
    split.
    - simpl.
      assert (hT1:= RModule_law2 _ (T:=T)).
      assert (hT2:= RModule_law1 _ (T:=T)).
      intro c.
      rewrite <- hT2; clear hT2.
      simpl.
      assert (hm := Monad_Mor_η m).
      rewrite <- hm; clear hm.
      rewrite functor_comp.
      now rewrite assoc.
    - simpl.
      intro c.
      assert (hT1:= RModule_law2 _ (T:=T)).

      assert (hm := Monad_Mor_μ m).
      rewrite assoc.
      rewrite <- (functor_comp T).
      specialize (hm c).
      simpl in hm.
      repeat pr1_norm.
      rewrite hm; clear hm.
      rewrite functor_comp.
      rewrite <- assoc.
      specialize (hT1 c).
      simpl in hT1.
      simpl.
      rewrite hT1; clear hT1.
      repeat rewrite functor_comp.

      assert (hs := nat_trans_ax (σ M' T)).
      simpl.
      simpl in hs.
      repeat rewrite assoc.
      my_f_equal.
      repeat rewrite <- assoc.
      rewrite <- hs.
      reflexivity.
  Qed.


  Definition pullback_module : RModule M C := tpair _ _ pbm_laws.


End Pullback_module.


Section Pullback_Module_Morphism.

  Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :RModule M' C}
          (n : RModule_Mor _ T T').

  Local Notation pbmT := (pullback_module m T).
  Local Notation pbmT' := (pullback_module m T').

  Lemma pbm_mor_law : RModule_Mor_laws M (T:=pbmT) (T':=pbmT') (pr1 n).
    intros b.
    set (pbmT := pullback_module m T).
    set (pbmT' := pullback_module m T').
    assert (hn:= RModule_Mor_σ _ n b).
    simpl in hn.
    revert hn.
    pr1_norm ;  simpl.
    auto.
    intros hn.
    rewrite <- assoc.
    rewrite <- hn.
    clear hn.
    repeat rewrite assoc.
    my_f_equal.
    rewrite (nat_trans_ax n).
    reflexivity.
  Qed.

  Definition pbm_mor  : RModule_Mor _  pbmT pbmT'  := ( _ ,, pbm_mor_law).

  Lemma is_nat_trans_id_pw {B C} {F G:functor B C} (f:Π x : B, C ⟦ F x, G x ⟧)
        (heq: Π x,  F x = G x)
        (heqf:Π x, f x = transportf (fun A =>  C ⟦ F x, A ⟧)
                                    (heq x) (identity (F x) )) : is_nat_trans F G f.
  Proof.
    intros.
    red.
    intros b b' g.
    rewrite heqf.
    rewrite heqf.
    clear heqf.
    simpl.
    assert  (tr:= fun P Q f=> transport_map(P:=P) (Q:=Q)f (heq b)).
    simpl.
  Abort.

End Pullback_Module_Morphism.

Section Pullback_Identity_Module.


    Context {B} {M':Monad B}  {C:precategory} {T  :RModule M' C}.


    Local Notation pbmid := (pullback_module (Monad_identity M') T).

    Lemma  pbm_id_is_nat_trans  :  is_nat_trans T  pbmid (fun x => identity _).
      red; intros; simpl.
      now rewrite id_right, id_left.
    Qed.

    Definition pbm_id_nat_trans : nat_trans T pbmid  := (_ ,, pbm_id_is_nat_trans).

    Lemma pbm_id_law : RModule_Mor_laws _ (T:=T) (T':=pbmid) pbm_id_nat_trans.
      red.
      intros b; simpl.
      rewrite id_left,id_right.
      pr1_norm.
      rewrite Precategories.Functor_identity.
      rewrite id_left.
      reflexivity.
    Qed.

    Definition pbm_id  : RModule_Mor _ T pbmid := (_ ,, pbm_id_law) .

End Pullback_Identity_Module.


Section Pullback_Composition.

   Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :RModule M' C}
     {M'': Monad B} (m' : Monad_Mor M' M'') (T'' : RModule M'' C).

    Local Notation comp_pbm := (pullback_module m (pullback_module m' T'')).
    Local Notation pbm_comp := (pullback_module (Monad_composition m  m') T'').

    Lemma pbm_mor_comp_is_nat_trans
      : is_nat_trans comp_pbm pbm_comp (fun x => identity _).
      red; intros; simpl.
      rewrite id_right.
      rewrite id_left.
      reflexivity.
    Qed.

    Definition pbm_mor_comp_nat_trans := (_ ,, pbm_mor_comp_is_nat_trans ).

    Lemma pbm_mor_comp_law : RModule_Mor_laws (T:=comp_pbm) (T':=pbm_comp) _ pbm_mor_comp_nat_trans.
      intros b; simpl.
      now rewrite id_left,id_right, (functor_comp T''), assoc.
    Qed.

    Definition pbm_mor_comp : RModule_Mor _ comp_pbm pbm_comp := (_ ,, pbm_mor_comp_law).
End Pullback_Composition.

Section LargeCatMod.

  Context (C:Precategory).


  (* range of modules *)
  Context (D:Precategory).

  (* total_precat_has_homsets *)
  Lemma monad_category_has_homsets : has_homsets (precategory_Monad C (homset_property C)).
    intros F G.
    simpl.

    unfold Monad_Mor.
    apply isaset_total2 .
    apply isaset_nat_trans.
    apply homset_property.
    intros m.

    apply isasetaprop.
    apply isaprop_Monad_Mor_laws.
    apply homset_property.
  Qed.

  Lemma rmodule_category_has_homsets (R:Monad C): has_homsets
                                                    (precategory_RModule R D (homset_property D)).
    intros R F G.
    simpl.


    apply isaset_total2 .
    apply isaset_nat_trans.
    apply homset_property.
    intros m.

    apply isasetaprop.
    apply isaprop_RModule_Mor_laws.
    apply homset_property.
  Qed.


  Definition monadPrecategory : Precategory :=
    (precategory_Monad C (homset_property C) ,, monad_category_has_homsets).


  Local Notation MONAD := monadPrecategory.
  Local Notation MODULE R := (precategory_RModule R _ (homset_property D)).

  Definition bmod_disp_ob_mor : disp_precat_ob_mor MONAD.
  Proof.
    exists (fun R : MONAD => ob (MODULE R)).
    intros xx' yy' g h ff'.
    exact (precategory_morphisms  g ( pullback_module  ff'  h )).
  Defined.

  Definition bmod_id_comp : disp_precat_id_comp _ bmod_disp_ob_mor.
  Proof.
    split.
    -
      intros x xx.
      simpl.
      apply pbm_id.
    - intros x y z f g xx yy zz ff gg.
      set (pbm_g := pbm_mor f gg).
      set (pbm_gf := (RModule_composition _ pbm_g (pbm_mor_comp f g _))).
      exact (compose ff pbm_gf).
  Defined.


  Definition bmod_data : disp_precat_data _
    := (bmod_disp_ob_mor ,, bmod_id_comp).

  (* Peut etre que c'est le genre de pb qui intéresse André.. Cf utilisation de foo *)
  Lemma foo (x y : MONAD) (f g : MONAD ⟦ x, y ⟧)
        (e : f = g)
        (xx : bmod_data x)
        (yy : pr1 bmod_data y)
        (ff : xx -->[ f] yy)
        (c : C) :
    (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 ff c.
  Proof.
    destruct e.
    intros.
    apply idpath.
  Qed.


  Lemma bmod_axioms : disp_precat_axioms MONAD bmod_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    - simpl.
      unfold id_disp; simpl.

      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      intros c; simpl.
      simpl.
      rewrite assoc; simpl.
      etrans. Focus 2. eapply pathsinv0.
      apply  foo.
      cbn. simpl. unfold pbm_mor_comp.
      unfold transportb.
      rewrite id_left.
      rewrite id_right.
      apply idpath.
    - (* this is for Ambroise *)

      set (heqf := id_right f).
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      simpl.
      intros c.
      rewrite id_right,id_right.
      revert ff.

      destruct (heqf).
      intros; simpl.
      reflexivity.
    - set (heqf:= assoc f g h).
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      intros c; simpl.
      (* rewrite id_right,id_right. *)
      (* rewrite assoc. *)
      etrans; cycle 1.
      (* set (z:= (ff:nat c ;; gg c ;; hh c). *)
      symmetry.

      clearbody heqf.

      (* impossible de faire un destruct ici... *)

      apply foo.
      simpl.
      repeat rewrite id_right.
      rewrite assoc.
      reflexivity.
    - simpl.
      apply rmodule_category_has_homsets.
  Qed.

  Definition bmod_disp : disp_precat MONAD:=
    (bmod_data ,, bmod_axioms).


End LargeCatMod.


(* a category can be viewed as a display category with singletons.
*)
Section LiftCatDispCat.

  Context (C:Precategory).

  Definition unit_hom := unit.
  Definition unit_ob := unit.
  Definition tt_hom := tt.
  Definition tt_ob := tt.


  Definition liftcat_disp_ob_mor : disp_precat_ob_mor C:=
    ((fun _ => unit_ob) ,, fun  _ _ _ _ _ => unit_hom).

  Definition liftcat_id_comp : disp_precat_id_comp _ liftcat_disp_ob_mor.
  Proof.
    split.
    -
      intros x xx.
      simpl.
      exact tt_hom.
    - intros x y z f g xx yy zz ff gg.
      exact tt_ob.
  Defined.


  Definition liftcat_data : disp_precat_data _
    := (liftcat_disp_ob_mor ,, liftcat_id_comp).

  Lemma uniq_tt (x:unit) : x=tt.
    now destruct x.
  Qed.

  Lemma liftcat_axioms : disp_precat_axioms _ liftcat_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property; try  now rewrite uniq_tt;
      symmetry;    rewrite uniq_tt.
    exact isasetunit.
  Qed.

  Definition liftcat_disp : disp_precat _ :=
    (liftcat_data ,, liftcat_axioms).


End LiftCatDispCat.


Section Arities.

  Variables (C D:Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation BMOD := (bmod_disp C D).

  (* Définitions des arités *)
  Definition arity := functor_lifting BMOD (functor_identity MONAD).


  (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
  Lemma right_inverse_arity  (ar:arity ) :
    ((pr1_precat BMOD)□ (lifted_functor ar) )    =  (functor_identity MONAD).
  Proof.
    intros.
    apply subtypeEquality; [| reflexivity].
    red.
    intros;  apply isaprop_is_functor.
    apply homset_property.
  Qed.

  (* Réciproque : si on a un foncteur qui vérifié ça, alors on a un functor lifting qui vaut
lui-même *)

  Section Reciproque.

    Variable (F:functor MONAD (total_precat BMOD)).
    Hypothesis (hF :  ((pr1_precat (bmod_disp C D))□ F) = (functor_identity (monadPrecategory C))).

    Definition ar_inv_ob (x:MONAD): BMOD x.
      intro x.

      unfold BMOD; simpl.
      change x with (functor_identity MONAD x).
      rewrite <- hF.
      exact (pr2 (F x)).
    Defined.

    Definition ar_inv_data : section_disp_data BMOD.
      exists ar_inv_ob.
      intros.
      unfold mor_disp.
      (* Trop dur, il faut faire des transport c'est trop la galère *)
      change f with (#(functor_identity MONAD) f).
      (* rewrite <- hF. *)
    Abort.


  End Reciproque.

End Arities.


(* deuxième manière de définir les arités *)
Section Arities2.

  Variables (C D:Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation BMOD := (bmod_disp C D).
  Local Notation LMONAD := (liftcat_disp MONAD).

  (* Définitions des arités *)
  Definition arity2 := functor_over (functor_identity _) LMONAD (bmod_disp C D).

  (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
  Lemma right_inverse_arity2  (ar:arity2 ) :
    ((pr1_precat BMOD)□ (total_functor ar) )    =  (pr1_precat LMONAD).
  Proof.
    intros.
    apply subtypeEquality; [| reflexivity].
    red.
    intros;  apply isaprop_is_functor.
    apply homset_property.
  Qed.

End Arities2.


(* large category of representation defined as a display category

Not that contrary to the large category of modules, we do not construct the category of
representations of a specific arity

This is an attempt to use directly the display category construction.
The category of represenations of a specific arity can be retrieved as a fiber category.

*)
Section LargeCatRep.

  Variable (C :Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation LMONAD := (liftcat_disp MONAD).
  Local Notation BMOD := (bmod_disp C C).
  Local Notation GEN_ARITY := (disp_functor_precat _ _ LMONAD BMOD).
  (* Arities are display functors over the identity *)
  Local Notation ARITY :=  (fiber_precategory GEN_ARITY (functor_identity _)).

  Lemma eq_ar_pointwise  (a b c : ARITY) ( f : ARITY ⟦ a, b ⟧) ( g : ARITY ⟦ b, c ⟧) (R:MONAD) x:
    (pr1 (pr1 (f ;; g) R tt)) x = (pr1 (pr1 f R tt) ;;; pr1 (pr1 g R tt)) x.
    intros.
    simpl.
    (* ***************

Question pour Benedikt

Pourquoi reflexivity ne marche pas

************* *)
    etrans.
    unfold compose.
    simpl.

  Abort.


  (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
  Lemma right_inverse_arity3  (ar:ARITY )
    :  ((pr1_precat BMOD)□ (total_functor ar) )    =  (pr1_precat LMONAD).
  Proof.
    intros.
    apply subtypeEquality; [| reflexivity].
    red.
    intros;  apply isaprop_is_functor.
    apply homset_property.
  Qed.


(*
  Définition du module tautologique
*)

  Definition taut_rmod_data (R:MONAD) : RModule_data R C.
    intros.
    exists (pr1 R).
    apply μ.
  Defined.

  Lemma taut_rmod_law (R:MONAD) : RModule_laws R (taut_rmod_data R).
  Proof.
    split; intro c.
    - apply Monad_law2.
    - apply Monad_law3.
  Qed.

  Definition taut_rmod (R:Monad C) : BMOD R := (taut_rmod_data R,, taut_rmod_law R).

  Notation Θ := taut_rmod.

  (* a representation is a monad with a module morphisme from arity to itself *)
  Definition rep_ar (ar: ARITY) :=
    Σ (R:MONAD), RModule_Mor R (((ar:functor_over _ _ _):functor_over_data _ _ _) R tt_ob) (Θ R).

  Coercion Monad_from_rep_ar (ar:ARITY) (X:rep_ar ar) : MONAD := pr1 X.

  Definition μr {ar:ARITY} (X:rep_ar ar) := pr2 X.

  Definition functor_from_monad (R:MONAD) : functor C C := pr1 (pr1 R).

  Definition functor_from_module {D:precategory} {R:MONAD} (S:RModule R D) : functor C D :=
    pr1 (pr1 S).

  Definition ar_obj (a:ARITY) (M:MONAD)  := pr1 a M tt_ob.

  Delimit Scope arity_scope with ar.
  (* ne marche pas.. *)
  (* Coercion ar_obj : ARITY >-> Funclass. *)
  Notation AO := ar_obj.

  Definition ar_mor (a:ARITY) {M N:MONAD} (f:MONAD  ⟦ M,N ⟧) :
    ((ar_obj a M )  -->[f] (ar_obj a N))%mor_disp.
  Proof.
    simpl.
    intros.
    apply (functor_over_on_morphisms a).
    exact tt_hom.
  Defined.

  Lemma ar_mor_eq (a:ARITY) {M N:MONAD} (f:MONAD  ⟦ M,N ⟧) :
    @functor_over_on_morphisms
      (monadPrecategory C) (monadPrecategory C)
      (functor_identity (precategory_Monad_data C)) (liftcat_disp (monadPrecategory C))
      (bmod_disp C C) (functor_over_data_from_functor_over a) M N tt_ob tt_ob f tt_hom =
    ar_mor a f .
  Proof.
    reflexivity.
  Qed.

  Notation "# F" := (ar_mor F)
                      (at level 3) : arity_scope.

  Delimit Scope arity_scope with ar.

  Definition rep_ar_mor_law {a b : ARITY} (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧)
             (g:MONAD ⟦ M, N ⟧) :=
     Π c,  ((μr M) ;;; pr1 g) c = (pr1 (pr1 f M tt) ;;;  pr1 (#b g )%ar ;;; μr N) c.

  Definition rep_ar_mor_mor (a b : ARITY) (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧) :=
    (* or the other way around a g ;;; f N : it is the same thanks to the naturality of f *)
    Σ g:MONAD ⟦ M, N ⟧, rep_ar_mor_law  M N f g.

  Coercion monad_morphism_from_rep_ar_mor_mor {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
           {f: ARITY ⟦ a, b ⟧} (h:rep_ar_mor_mor a b M N f) : MONAD ⟦ M, N ⟧
    := pr1 h.

  Definition rep_ar_mor_law1 {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
           {f: ARITY ⟦ a, b ⟧} (h:rep_ar_mor_mor a b M N f) := pr2 h.



  Definition brep_disp_ob_mor : disp_precat_ob_mor ARITY:= (rep_ar,, rep_ar_mor_mor).

  (*
  Definition maponpathsf {T1  : UU} (f:T1) {T2: T1->UU}  (t1 t2 : Π (x: T1) , T2 x)
             (e: t1 = t2) : t1 f = t2 f.
  Proof.
    intros. induction e. apply idpath.
  Defined.


  Definition functoreq (C D:precategory) (F G:functor C D)
             (e: F = G) x : F x = G x.
  Proof.
    intros. induction e. apply idpath.
  Defined.
*)
(* Definition maponpathsf2 {T1  : UU} {T2: T1->UU} (f:T1) (t1 t2 : Π (x: T1) , T2 x) *)
(*            (e: t1 = t2) (e':f = g): t1 f = t2 g. *)
(* Proof. *)
(*   intros. induction e. apply idpath. *)
(* Defined. *)


  Ltac neweq z :=
    let t := type of z in
    let x := fresh in
    evar (x:t); cut (z=x); subst x; cycle 1.

  Ltac neweqsubst z :=
    let h := fresh in
    neweq z; [subst z| intro h; rewrite h; clear h z].


(*
  Lemma compose_eq :  Π (C : precategory_data) (a b c : C) (f f' : C ⟦ a, b ⟧) (g g' : C ⟦ b, c ⟧)
                        (e:f = f') (e':g = g') , f ;; g = f' ;; g'.
    intros.
    now destruct e,e'.
  Qed.
 *)

  Lemma brep_id_law (a : ARITY) (RM : brep_disp_ob_mor a) :
    (rep_ar_mor_law RM RM (identity _) (Monad_identity _)).
    intros.
    intro c.
    simpl.
    rewrite -> id_right, id_left.
    symmetry.
    rewrite <- id_left.
    apply cancel_postcomposition.
    unfold ar_mor.
    match goal with
    | |- nat_trans_data (pr1 ?f) c = _  => set (z := f)
    end.
    neweqsubst z.
    change tt_hom with (@id_disp _ (LMONAD) (pr1 RM) tt).
    now apply (functor_over_id a).
    reflexivity.
  Qed.

  Definition brep_id  (a : ARITY) (RM : brep_disp_ob_mor a) : RM -->[ identity a] RM.
    intros.
    exists (Monad_identity _).
    apply brep_id_law.
  Defined.

  Lemma brep_comp_law  (a b c : ARITY) (f : ARITY ⟦ a, b ⟧) (g : ARITY ⟦ b, c ⟧)
             (R : brep_disp_ob_mor a) (S : brep_disp_ob_mor b)    (T : brep_disp_ob_mor c)
             (α:R -->[ f ] S) (β:S -->[g]  T) :
    (rep_ar_mor_law R T (f;;g)
                    ( monad_morphism_from_rep_ar_mor_mor α ;; monad_morphism_from_rep_ar_mor_mor β)).
  Proof.
    intros.
    intros x.
    simpl.

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

    etrans.
    apply cancel_postcomposition.

    set (fg :=   (compose _ _ )).
    simpl in fg.

    unfold fg,compose.
    simpl.
    nat_trans_ov    set (fg2 := (pr1 fg)).
er
    simpl in fg.


    set (z := (# ( c))%ar _).

    neweqsubst z.

    assert( hc:= (@functor_over_comp _ _ _ _ _ ( c)) (pr1 R) (pr1 S) (pr1 T) tt tt tt
                                                     (pr1 α) (pr1  β) tt tt).
    apply hc.
    rewrite ar_mor_eq.
    rewrite ar_mor_eq.
    simpl.
    rewrite id_right.
    rewrite assoc.




  Admitted.


  Definition brep_comp (a b c : ARITY) (f : ARITY ⟦ a, b ⟧) (g : ARITY ⟦ b, c ⟧)
             (RMa : brep_disp_ob_mor a) (RMb : brep_disp_ob_mor b)    (RMc : brep_disp_ob_mor c)
             (mab:RMa -->[ f ] RMb) (mbc:RMb -->[g]  RMc) : RMa -->[f;;g] RMc.
    intros.
    exists (pr1 mab;; pr1 mbc).
    apply brep_comp_law.
  Defined.

(*


NE PAS LIRE APRES C'EST LE BORDEL

*)

Definition brep_id_comp : disp_precat_id_comp _ brep_disp_ob_mor.
Proof.
  split.
  - apply brep_id.
  -
    intros x xx.
    simpl.
    apply (tpair _ (Monad_identity _)).
    intro c.
    simpl.
    rewrite -> id_right, id_left.

    symmetry.
    rewrite <- id_left.
    apply cancel_postcomposition.
    unfold ar_mor.
    match goal with
    | |- nat_trans_data (pr1 ?f) c = _  => set (z := f)
    end.
    neweqsubst z.
    change tt_hom with (@id_disp _ (LMONAD) (pr1 xx) tt).
    now apply (functor_over_id x).
    reflexivity.

  - intros a b c f g RM RM2 RM3 m1 m2.
    exists (pr1 m1 ;; pr1 m2).
    intros x.
    simpl.

    set (z := (# ( c))%ar _).

    neweqsubst z.

    assert( hc:= (@functor_over_comp _ _ _ _ _ ( c)) (pr1 RM) (pr1 RM2) (pr1 RM3) tt tt tt (pr1 m1) (pr1 m2) tt tt).
    apply hc.
    do 2! rewrite ar_mor_eq.
    simpl.
    rewrite id_right.
    rewrite assoc.
    pr1_norm.


    match goal with
    | |-  ?f = _  => set (z := f)
    end.

    set (z := nat_trans_data (pr1
    apply functor_over_comp.
    simpl.
set (z' := (# z)%ar _).
neweq z'.
unfold z'.
unfold ar_mor.
 apply functor_over_comp.
unfold z'.
apply
 match goal with
 | |- context fff [((# z)%ar ?x )]     => (* let yop := context fff[((# z)%ar x)] in  *) set (x':=((# z)%ar x ) );
                                                                                         let t:= type of x' in
                                                                                         evar( z'':t);
                                                                                           assert (hz'':x'=z'')
 end.
 unfold z''.
 apply functor_over_comp.
rewrite functor_over_comp in x'.
    ff gg.
    set (pbm_g := pbm_mor f gg).
    set (pbm_gf := (RModule_composition _ pbm_g (pbm_mor_comp f g ))).
    exact (compose ff pbm_gf).
Defined.


Definition brep_data : disp_precat_data _
:= (brep_disp_ob_mor ,, brep_id_comp).


Lemma foo (x y : MONAD) (f g : MONAD ⟦ x, y ⟧)
  (e : f = g)
  (xx : brep_data x)
  (yy : pr1 brep_data y)
  (ff : xx -->[ f] yy)
  (c : C) :
  (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 ff c.
Proof.
  destruct e.
  intros.
  apply idpath.
Qed.


Lemma brep_axioms : disp_precat_axioms MONAD brep_data.
Proof.

  repeat apply tpair; intros; try apply homset_property.
  - simpl.
    unfold id_disp; simpl.

    apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
    apply nat_trans_eq; try apply homset_property.
    intros c; simpl.
    simpl.
    rewrite assoc; simpl.
    etrans. Focus 2. eapply pathsinv0.
      apply  foo.
   cbn. simpl. unfold pbm_mor_comp.
      unfold transportb.
      rewrite id_left.
      rewrite id_right.
      apply idpath.
  - (* this is for Ambroise *)

    set (heqf := id_right f).
     apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
     apply nat_trans_eq; try apply homset_property.
     simpl.
     intros c.
     rewrite id_right,id_right.
    revert ff.

    destruct (heqf).
    intros; simpl.
    reflexivity.
  - set (heqf:= assoc f g h).
     apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
     apply nat_trans_eq; try apply homset_property.
     intros c; simpl.
     (* rewrite id_right,id_right. *)
     (* rewrite assoc. *)
     etrans; cycle 1.
     (* set (z:= (ff:nat c ;; gg c ;; hh c). *)
     symmetry.

     clearbody heqf.

(* impossible de faire un destruct ici... *)

     apply foo.
     simpl.
     repeat rewrite id_right.
     rewrite assoc.
     reflexivity.
  - simpl.
    apply rmodule_category_has_homsets.
Qed.

Definition brep_disp : disp_precat MONAD:=
   (brep_data ,, brep_axioms).

End LargeCatRep.

  (*
 Definition nat_trans_dataE {C C' : precategory_data}
  {F F' : functor_data C C'}(a : nat_trans F F') : pr1 a = (nat_trans_data a  :
   Π x : ob C, F x --> F' x)  := idpath _.

 Definition precategory_data_from_precategoryE (C : precategory) : pr1 C = precategory_data_from_precategory C := idpath _.
*)
 (* Definition functor_data_from_functorE (C C': precategory_data) *)
 (*     (F : functor C C') : pr1 F = functor_data_from_functor _ _ F  := idpath _. *)


(* Hint Rewrite @nat_trans_dataE functor_data_from_functorE : coercions. *)



Require Import lemmacoercions.
