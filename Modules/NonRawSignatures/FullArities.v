(* Full arities : pairs of old arities *)
(* With the definition of represetnation as displayed category *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.

Require Import Modules.Signatures.Signature.


Module HAr := Signature.
Set Automatic Introduction.

Definition FullSignature (C : category) := precategory_binproduct
                                         (@arity_category C)  ((@arity_category C) ^op).

Definition FullSignature_has_homsets C : has_homsets (FullSignature C) :=
  has_homsets_precategory_binproduct _ _ (homset_property arity_category)
                                     (has_homsets_opp (homset_property _) ).

Definition FullSignature_cat (C : category) : category := category_pair _
                                                                    (FullSignature_has_homsets C).

Definition dom { C : category} (a : FullSignature C) : arity C := ob1 a.
Definition codom { C : category} (a : FullSignature C) : arity C := ob2 a.

Definition dom_mor {C : category} { a b : FullSignature C} (f : FullSignature C ⟦a , b ⟧)
           : arity_Mor (dom a) (dom b) := mor1 f.

Definition codom_mor {C : category} { a b : FullSignature C} (f : FullSignature C ⟦a , b ⟧)
           : arity_Mor (codom b) (codom a) := mor2 f.


(* large category of representation defined as a display category


*)


Section LargeCatRep.
  
Variable (C : category).
  
Local Notation MONAD := (Monad C).
Local Notation PRE_MONAD := (category_Monad C).
Local Notation BMOD := (bmod_disp C C).
  

(* Signatures are display functors over the identity *)
Local Notation FSignature  := (FullSignature C).



Local Notation Θ := tautological_LModule.


  

(** A representation is a monad with a module morphisme from its image by the arity
 to itself *)
Definition rep_ar (ar : FSignature) :=
  ∑ R : MONAD, LModule_Mor R (dom ar R) (codom ar R).

Coercion Monad_from_rep_ar (ar : FSignature) (X : rep_ar ar) : MONAD := pr1 X.

Definition rep_τ {ar : FSignature} (X : rep_ar ar) :
  LModule_Mor X (dom ar X) (codom ar X)
  := pr2 X.

Definition rep_ar_mor_law {a b : FSignature} (M : rep_ar a) (N : rep_ar b)
           (f : FSignature ⟦ a,  b⟧) (g : Monad_Mor M N) : UU :=
  ∏ c : C, rep_τ M c · ((#(codom a) g)%ar:nat_trans _ _) c =
            ((#(dom a) g)%ar:nat_trans _ _) c · dom_mor f N c ·
                                            rep_τ N c · codom_mor f N c.
  (*
top right is left hand side
     dom a M --> codom a M ---> codom a N
       |                             ^
       |                             |
       |                             |
       V                             |
     dom a N ---> dom b N --->  codom b N
   *)

Lemma isaprop_rep_ar_mor_law {a b : FSignature} (M : rep_ar a) (N : rep_ar b)
      (f : FSignature ⟦a, b⟧) (g : Monad_Mor M N) 
  : isaprop (rep_ar_mor_law M N f g).
Proof.
  intros.
  apply impred; intro c.
  apply homset_property.
Qed.

Definition rep_ar_mor_mor {a b : FSignature} (M : rep_ar a) (N : rep_ar b) f :=
  ∑ g : Monad_Mor M N, rep_ar_mor_law  M N f g.

Lemma isaset_rep_ar_mor_mor {a b} (M : rep_ar a) (N : rep_ar b) f :
  isaset (rep_ar_mor_mor  M N f).
Proof.
  intros.
  apply isaset_total2 .
  - apply has_homsets_Monad.
  - intros.
    apply isasetaprop.
    apply isaprop_rep_ar_mor_law.
Qed.

Coercion monad_morphism_from_rep_ar_mor_mor {a b } {M : rep_ar a} {N : rep_ar b}
         {f} (h : rep_ar_mor_mor  M N f) : Monad_Mor M N
  := pr1 h.

Definition rep_ar_mor_ax {a b : FSignature} {M : rep_ar a} {N : rep_ar b}
           {f} (h:rep_ar_mor_mor  M N f) :
  ∏ c : C, rep_τ M c · ((#(codom a) h)%ar:nat_trans _ _) c =
            ((#(dom a) h)%ar:nat_trans _ _) c · dom_mor f N c ·
                                            rep_τ N c · codom_mor f N c
  := pr2 h.

Definition rep_disp_ob_mor : disp_cat_ob_mor FSignature :=
  (rep_ar,, @rep_ar_mor_mor).

Lemma rep_id_law a  (RM : rep_disp_ob_mor a) :
  rep_ar_mor_law RM RM (identity (C:=FSignature) _) (Monad_identity _).
Proof.
  intro c.
  cbn.
  repeat rewrite id_right.
  etrans.
  - apply cancel_precomposition.
    apply arity_id.
  - rewrite id_right.
    apply pathsinv0.
    etrans; [|apply id_left].
    apply cancel_postcomposition.
    apply arity_id.
Qed.

Definition rep_id  (a : FSignature)  (RM : rep_disp_ob_mor a) :
  RM -->[ identity (C:=FSignature) a] RM.
Proof.
  intros.
  exists (Monad_identity _).
  apply rep_id_law.
Defined.



Lemma transport_arity_mor (x y : FSignature) (f g : FSignature ⟦ x, y⟧)
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
Lemma rep_ar_mor_mor_equiv (a b : FSignature) (R:rep_disp_ob_mor a)
      (S:rep_disp_ob_mor b) (f:FSignature⟦ a, b⟧)
      (u v: R -->[ f] S) :
  (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c) -> u = v.
Proof.
  intros.
  use (invmap (subtypeInjectivity _ _ _ _  )). 
  - intro g.
    apply isaprop_rep_ar_mor_law.
  - use (invmap (Monad_Mor_equiv _ _  _  )).  
     +  apply homset_property.
     +  apply nat_trans_eq.
        apply homset_property.
        assumption.
Qed.


(** Defining the composition in rep *)

Lemma rep_comp_law  (a b c : FSignature) (f : FSignature ⟦ a,  b⟧) (g : FSignature ⟦ b,  c⟧)
      (R : rep_disp_ob_mor a) (S : rep_disp_ob_mor b)    (T : rep_disp_ob_mor c)
      (α:R -->[ f ] S) (β:S -->[g]  T) :
  (rep_ar_mor_law R T (compose (C:=FSignature) f g)
                  (compose (C:=PRE_MONAD) (monad_morphism_from_rep_ar_mor_mor α)
                           ( monad_morphism_from_rep_ar_mor_mor  β))).
Proof.
  intro x.
  rewrite arity_comp.
  rewrite arity_comp.
  cbn.
  repeat rewrite id_right.
  rewrite assoc.

  etrans.
  { apply cancel_postcomposition.
    use rep_ar_mor_ax. }
  repeat rewrite <- assoc.
  apply cancel_precomposition.
  etrans.
  { apply cancel_precomposition.
    etrans.
    {
      apply cancel_precomposition.
      eapply pathsinv0.
      apply arity_Mor_ax_pw.
    }
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    use rep_ar_mor_ax.
  }
  repeat rewrite assoc.
  do 4 apply cancel_postcomposition.
  apply pathsinv0.
  apply arity_Mor_ax_pw.
Qed.

Definition rep_comp (a b c : FSignature ) f g
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

(* TODO *)

Lemma rep_axioms : disp_cat_axioms (FullSignature_cat _) rep_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  - apply rep_ar_mor_mor_equiv.
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
    etrans. Focus 2.
      symmetry.
      apply transport_arity_mor.
      cbn.
      rewrite assoc.
      apply idpath.
  - apply isaset_rep_ar_mor_mor.
Qed.

Definition rep_disp : disp_cat (FullSignature_cat _) := rep_data ,, rep_axioms.

Definition pb_rep {a a' : FSignature} (f : FSignature ⟦ a , a'⟧) (R : rep_ar a') : rep_ar a :=
  ((R : MONAD) ,, ((dom_mor f R : category_LModule _ _ ⟦_, _⟧)
                     · rep_τ R · (codom_mor f R : category_LModule _ _ ⟦_, _⟧))).

Lemma pb_rep_to_law {a a'} (f : FSignature ⟦ a, a' ⟧) (R : rep_ar a') :
  rep_ar_mor_law (pb_rep f R) R f (identity ((R : MONAD) : PRE_MONAD)).
Proof.
  intro c.
  do 2 rewrite arity_id.
  rewrite id_right,id_left.
  apply idpath.
Qed.

(** ** Now the cleaving *)

(* make the half-arity version useless *)
(* exactement les mêmes preuves *)

Definition pb_rep_to {a a'} (f : FSignature ⟦ a, a' ⟧) (R : rep_ar a') :
  (pb_rep f R : rep_disp a) -->[f] R :=
  (identity (C:=PRE_MONAD) (R:MONAD),, pb_rep_to_law f R).

Lemma rep_mor_law_pb {a a' b} (f : FSignature ⟦ a, a' ⟧) (g : FSignature ⟦ b, a ⟧)
      (S : rep_ar b) (R : rep_ar a') (hh : (S : rep_disp _) -->[g·f] R) :
  rep_ar_mor_law S (pb_rep f R) g (hh : rep_ar_mor_mor  _ _ _ ).
Proof.
  intros.
  destruct hh as [hh h].
  intro c.
  etrans; [apply h|].
  cbn.
  repeat rewrite assoc.
  apply idpath.
Qed.

Lemma rep_mor_pb {a a' b} (f : FSignature ⟦ a, a' ⟧) (g : FSignature ⟦ b, a ⟧)
      (S : rep_ar b) (R : rep_ar a') (hh : (S : rep_disp _) -->[g·f] R) :
   (S : rep_disp _) -->[ g] pb_rep f R.
Proof.
    use tpair.
    + apply hh.
    + apply rep_mor_law_pb.
Defined.
    
Definition pb_rep_to_cartesian {a a'} (f : FSignature ⟦ a, a' ⟧)
           (R : rep_ar a') : is_cartesian ((pb_rep_to f R) :
                                             (pb_rep f R : rep_disp a) -->[_] R).
Proof.
  intros.
  intro b.
  intros g S hh.
  unshelve eapply unique_exists.
  - apply rep_mor_pb.
    exact hh.
  - abstract (apply rep_ar_mor_mor_equiv;
    intro c;
    apply id_right).
  - intro u.
    apply isaset_rep_ar_mor_mor.
  - abstract (intros u h;
    apply rep_ar_mor_mor_equiv;
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
Lemma rep_ar_mor_mor_equiv_inv {a b : ARITY} {R:rep_disp_ob_mor a}
      {S:rep_disp_ob_mor b} {f:arity_Mor  a b}
      (u v: R -->[ f] S) 
  : u = v -> (∏ c, pr1 (pr1 u) c = pr1 (pr1 v) c).
Proof.
  intros.
  now induction X.
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

  (* Notation "# F" := (ar_mor F) (at level 3) : arity_scope. *)

  (*
  Definition ar_mor_pw {a b : ARITY} (f:arity_Mor a b) (R:MONAD) :
    LModule_Mor _  (a ` R)
                (pb_LModule ((nat_trans_id (functor_identity PRE_MONAD)) R)
                            (b ` R))
    := (f : arity_mor (a:arity) (b:arity)) R.
*)

  (* Infix "``" := ar_mor_pw (at level 25) : arity_scope . *)
