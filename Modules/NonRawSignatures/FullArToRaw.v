(** Let (a, Θ^(n)) be an arity
Then the category of representation is isomorphic to
(a × Θ^n, 1) in the sense required by SigEquivRep
 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Monads.Derivative.
Require Import UniMath.CategoryTheory.Adjunctions.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.DerivationIsFunctorial.
Require Import Modules.Prelims.LModPbCommute.

Require Import Modules.Signatures.aritiesalt.
Require Import Modules.Signatures.FullSignatures.
Require Import Modules.Signatures.HssToArity.
Require Import Modules.Signatures.HArityBinproducts.
Require Import Modules.Signatures.HArityDerivation.
(* Require Import Modules.Signatures.CheckCorrespondanceAdjonction. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import Modules.Prelims.deriveadj.


Module HAr := aritiesalt.

(* TODO chercher cette def dans UniMath *)

Definition catiso_comp {A B C : precategory_data} (F : catiso A B)
           (G : catiso B C) : catiso A C.
Proof.
  use tpair.
  - exact (F ∙ G).
  - split.
    + intros a b.
      apply twooutof3c.
      * apply (weqproperty (catiso_fully_faithful_weq F _ _)).
      * apply (weqproperty (catiso_fully_faithful_weq G _ _)).
    + apply twooutof3c.
      * apply (weqproperty (catiso_ob_weq F)).
      * apply (weqproperty (catiso_ob_weq G)).
Defined.

(* TODO : déplacer ceci dans un novueau fichier *)
Section CoBindingArity.

(** Content of this section:
    - translate a natural number into a half-arity
*)
  
Fixpoint nat_deriv_HAr {C : category} bcp T (n :nat) : arity C :=
  match n with
    0 => tautological_harity
  | S m => harity_deriv bcp T (nat_deriv_HAr bcp T m)
  end.

Let prodHAr {C : category} (bpC : BinProducts C)
    : arity_precategory ⟶ arity_precategory
  :=
  (functor_fix_snd_arg _ _ _  (binproduct_functor  (harity_BinProducts bpC ))
                       (tautological_harity)).

Definition nat_prod_HAr {C : category} (bp : BinProducts C) (n : nat) : arity C :=
  iter_functor (prodHAr bp) n tautological_harity.

Definition CoBinding_to_FullArity {C : category} bcp T ( a : HAr.arity C)
           (n : nat) 
  : FullArity C
  :=  a ,, nat_deriv_HAr bcp T n.

Context {C : category} .
Hypothesis ( bp : BinProducts C).
Let bpHAr := harity_BinProducts (C := C) bp.
Local Notation BPO := (BinProductObject _).
  
  (* Let prodHAr  := *)
  (*   (functor_fix_snd_arg _ _ _  (binproduct_functor  (harity_BinProducts bp )) *)
  (*                        (tautological_harity)). *)

  (* Definition DeBind_HArity  (a : HAr.arity C) (n : nat) := *)
(*   iter_functor prodHAr n a. *)

(** Input: an arity [a] and a natural number
    Output: [a × θ × θ × ... × θ] 
*)
Fixpoint DeBind_HArity  (a : HAr.arity C) (n : nat) : HAr.arity C :=
  match n with
    0 => a
  | S m => DeBind_HArity (BPO (bpHAr a tautological_harity)) m
  end.
(* iter_functor prodHAr n a. *)

End CoBindingArity.





(* Tentative de généralisation sans SET *)
(** Generalization of what?

 *)
Section NoSetGenNat.

  Context {C : category}.
  Hypothesis ( bp : BinProducts C).
  Hypothesis ( bcp : BinCoproducts C).
  Hypothesis ( Tset : Terminal C).

  Local Notation HalfArity := (HAr.arity C).
  Let MOD (R : Monad C) := (precategory_LModule R C).



  Let hs := homset_property C.

  Let LMOD_bp (R : Monad C) :=
    (LModuleBinProduct.LModule_BinProducts R bp hs).

  Local Notation "M '" := (LModule_deriv Tset bcp M) (at level 30).

  Let deriv R :=
    (LModule_deriv_functor (TerminalObject Tset) bcp hs R).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject Tset) bcp hs _).

  (* Local Infix  "× '" := (LModule_deriv Tset bcp M) (at level 30). *)
  Local Notation "×ℜ" :=  (binproduct_functor  (LMOD_bp _)).
  Let bpM  (R : Monad C) :=
    (LModuleBinProduct.LModule_binproduct (R := R) bp (homset_property C)).
  (* (a R) (tautological_LModule R)). *)
  (* Local Notation "×ℜ" :=  (bpM. *)
  Local Notation Θ :=  (tautological_LModule).

  Let deriv_pb_iso {R S : Monad C} (f : Monad_Mor R S) 
      : ∏ M, iso (C := MOD R) (pb_LModule f (M ')) ((pb_LModule f M) ')
    :=
    pb_deriv_to_deriv_pb_iso Tset bcp (D := C) f.

  Let bp_pb_iso {R S : Monad C} (f : Monad_Mor R S) 
    : ∏ M N, iso (C := MOD R) 
                 (bpM _ (pb_LModule f M)(pb_LModule f N) )
                 (pb_LModule f (bpM _ M N))
    :=
    binprod_pbm_to_pbm_iso f (cpC := bp).

  (* Let deriv_12_iso := *)
  (*   LMod_deriv12_iso bp bcp Tset. *)

  (* décomposition de l'hypothès *)
  Hypothesis
    (adj1 : ∏ R M N,
     LModule_Mor R M (N ')
                 ≃
         LModule_Mor R
         (bpM R M (Θ R))
    (* (LModuleBinProduct.LModule_binproduct bp (homset_property C) (a R) (tautological_LModule R)) *)
    N
    ).


  (*
f : R -> S
u : M -> N' et v : N -> f* A

      u            v'
 M ---------> N' --------> (f* A)'
Par l'adjonction ça doit devenir

       !u        v
M x R ----> N --------> f*A


*)
  Hypothesis (adj_law1 :
                ∏ R S (f : Monad_Mor (C := C) R S)
                  (M N : LModule R _) (A : LModule S _)
                  (u : LModule_Mor _ M (N '))
                  (v : LModule_Mor _ N (pb_LModule f A)),
                adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · ((# ∂ v))) =
                (adj1 R _ _ u : MOD R ⟦_,_⟧) · v).
  (*
Et maintenant,
On dit que l'action de l'adjonction  sur
   u         f*v           i
M ---> f* A -----> f* B' ----> (f* B)'
donne
      u x f                 i2                f* !v
M×R ---------> f* A x f* S ------> f*(A x S) -------> f* B
*)
  Hypothesis (adj_law2 :
                ∏ R S (f : Monad_Mor (C := C) R S)
                  (M : LModule R _) (A B : LModule S _)
                  (u : LModule_Mor _ M (pb_LModule f A))
                  (v : LModule_Mor _ A (B ')),
                adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · (pb_LModule_Mor f v) · deriv_pb_iso f _)
                  =
                (BinProductOfArrows _ (LMOD_bp R _ _) (LMOD_bp R _ _) (u : MOD R ⟦_,_⟧) (monad_mor_to_lmodule f : MOD R ⟦_,_⟧))
                                    · bp_pb_iso f _ _
                                                      · pb_LModule_Mor f (adj1 _ _ _ v)).

  Context (a : HalfArity) .
  (* Let nat_d_HAr  := nat_deriv_HAr (C:=C) bp bcp Tset . *)
  Let nat_d_HAr  := nat_deriv_HAr (C:=C)  bcp Tset .
  Let nat_p_HAr  := nat_prod_HAr (C:=C) bp  .

  (* TODO donner des defs generales de ça *)
  Let a_n n : FullArity C := CoBinding_to_FullArity bcp Tset a n.

  Let bpHAr := harity_BinProducts (C := C) bp.

  Local Notation BPO := (BinProductObject _).
  (* Let b n : HalfArity := BPO (bpHAr a (nat_p_HAr n)). *)
  Let b  : HalfArity := BPO (bpHAr a tautological_harity ).

  Let b_n n : FullArity C := CoBinding_to_FullArity bcp Tset b n.
  Let c_n n : HalfArity := DeBind_HArity bp   a n.
  Let d_n n : FullArity C := c_n n ,, tautological_harity.

  Definition equiv_is_rep_ar_one_to_raw (a' : HalfArity) n R : 
                 LModule_Mor R (a' R)(nat_d_HAr (S n) R) ≃
                             LModule_Mor R (BPO (LMOD_bp R (a' R) (tautological_LModule R)))
                             (nat_d_HAr n R).
  Proof.
    apply adj1.
  Defined.

  Definition equiv_is_rep_ar_to_raw (a' : HalfArity) n R : 
                 LModule_Mor R (a' R)( nat_d_HAr n R) ≃
                             LModule_Mor R ((DeBind_HArity bp a' n : HAr.arity _) R)
                             (tautological_LModule R).
  Proof.
    revert a'.
    induction n; intro a'.

    - apply idweq.
    - eapply weqcomp.
      + apply equiv_is_rep_ar_one_to_raw.
      + apply (IHn (BPO (bpHAr a' tautological_harity))).
  Defined.

  Local Notation Fmod_one := equiv_is_rep_ar_one_to_raw.
  Local Notation Fmod := equiv_is_rep_ar_to_raw.

  Definition FAr_to_one_HAr_ob n :  rep_ar _ (a_n (S n)) ≃ rep_ar _ (b_n n) :=
    weqfibtototal _ _ (equiv_is_rep_ar_one_to_raw _ n).

  Definition FAr_to_HAr_ob n :  rep_ar _ (a_n n) ≃ rep_ar _ (d_n n) :=
    weqfibtototal _ _ (equiv_is_rep_ar_to_raw _ n).

  Local Notation Fob_one := (FAr_to_one_HAr_ob _).
  Local Notation Fob := (FAr_to_HAr_ob _).


  Lemma rep_ar_mor_law_a_n_equiv {n: nat} {R T : rep_ar C (a_n (S n))}
        (f : Monad_Mor R T)
    : rep_ar_mor_law C R T (identity (a_n (S n))) f ≃
                     (
                       (rep_τ _ R : MOD _ ⟦ _, _⟧)
                     · (# ∂ (# (nat_d_HAr n) f)%ar)
                     =
                     ((# a f)%ar : MOD _ ⟦_,_⟧)
                       · (pb_LModule_Mor f ((rep_τ _ T : MOD T ⟦_,_⟧)
                                                  (* · *)
                                                  (* deriv_12_iso S *)
                                           ) : MOD _ ⟦ _, _⟧) ·
                       deriv_pb_iso f _
  ).
  Proof.
    apply weqinvweq.
    eapply weqcomp; [apply LModule_Mor_equiv; apply homset_property|].
    eapply weqcomp; [apply nat_trans_eq_weq; apply homset_property|].
    apply weqonsecfibers.
    intro x.
    cbn.
    repeat rewrite id_right.
    apply idweq.
  Qed.
  Definition equiv_raw_ar_one_mor_law {n}
     {R S : rep_ar _ (a_n (S n))} (f : Monad_Mor R S) :
                      rep_ar_mor_law _ R S (identity _) f ≃
                                     rep_ar_mor_law _ (Fob_one R) (Fob_one S)
                                     (identity   _) f.
  Proof.
    eapply weqcomp; [apply rep_ar_mor_law_a_n_equiv|].
    eapply weqcomp;[ eapply (weqonpaths (adj1 _ _ _))|].
    rewrite adj_law2.
    eapply (transportb (fun z => (z = _) ≃ _));[apply adj_law1|].
    eapply weqcomp;[apply LModule_Mor_equiv;apply homset_property|].
    eapply weqcomp;[apply nat_trans_eq_weq;apply homset_property|].
    apply weqonsecfibers.
    intro c.
    cbn.

    unfold BinCoproduct_of_functors_ob,binproduct_nat_trans_data; cbn.
    unfold binproduct_nat_trans_pr1_data,binproduct_nat_trans_pr2_data; cbn.
    repeat rewrite id_right.
    repeat rewrite id_left.
    apply idweq.
  Qed.


  (*
  Definition FAr_to_HAr_mor {n} (R T : rep_ar _ (a_n (S n))) :
             ( rep_ar_mor_mor _ R T (identity _)) ≃
    rep_ar_mor_mor _   (Fob_one R) (Fob_one T) (identity  _ ) :=
        weqfibtototal _ _ (@equiv_raw_ar_one_mor_law n R T).


  Local Notation Fmor := FAr_to_HAr_mor.

  Definition FAr_to_HAr_one_functor_data n : functor_data ((rep_disp C)[{a_n (S n)}])
                                                    ((rep_disp C)[{b_n n }]) :=
    functor_data_constr ((rep_disp C)[{a_n (S n)}])
                        ((rep_disp C)[{b_n n }])
                        Fob_one  Fmor.

  Lemma FAr_to_HAr_one_is_functor n : is_functor (FAr_to_HAr_one_functor_data n).
  Proof.
    split.
    - intro R.
      apply rep_ar_mor_mor_equiv.
      intro; apply idpath.
    - intros R S T f g.
      apply rep_ar_mor_mor_equiv.
      intro c.
      cbn.
      etrans;[ use transport_arity_mor|].
      apply pathsinv0.
      match goal with
        |- context [ transportf (mor_disp ?x' ?y') ?e' ?f' ] =>
        set (e := e'); set (ff := f'); set (xx := x'); set (yy := y')
      end.
      apply (transport_arity_mor _ _ _ _ _ e xx yy ff).
  Defined.

  
  Definition FAr_to_HAr_one_functor n : (rep_disp C)[{a_n (S n)}] ⟶ (rep_disp C)[{b_n n}] :=
    _ ,, FAr_to_HAr_one_is_functor n.

  Local Notation FS := FAr_to_HAr_one_functor.

  Definition iso_FAr_HAr_rep n : catiso ((rep_disp C)[{a_n (S n)}])
                                        ((rep_disp C)[{b_n n}]) :=
     FS n,, (λ x y  , weqproperty (Fmor (n := n) x y)),, weqproperty Fob_one.
*)

End NoSetGenNat.

Section FAR_ToHAR_Rep.
  
  Context {C : category}.
  Hypothesis ( bp : BinProducts C).
  Hypothesis ( bcp : BinCoproducts C).
  Hypothesis ( Tset : Terminal C).

  Local Notation HalfArity := (HAr.arity C).
  Let MOD (R : Monad C) := (precategory_LModule R C).



  Let hs := homset_property C.

  Let LMOD_bp (R : Monad C) :=
    (LModuleBinProduct.LModule_BinProducts R bp hs).

  Local Notation "M '" := (LModule_deriv Tset bcp M) (at level 30).

  Let deriv R :=
    (LModule_deriv_functor (TerminalObject Tset) bcp hs R).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject Tset) bcp hs _).

  (* Local Infix  "× '" := (LModule_deriv Tset bcp M) (at level 30). *)
  Local Notation "×ℜ" :=  (binproduct_functor  (LMOD_bp _)).
  Let bpM  (R : Monad C) :=
    (LModuleBinProduct.LModule_binproduct (R := R) bp (homset_property C)).
  (* (a R) (tautological_LModule R)). *)
  (* Local Notation "×ℜ" :=  (bpM. *)
  Local Notation Θ :=  (tautological_LModule).

  Let deriv_pb_iso {R S : Monad C} (f : Monad_Mor R S) 
      : ∏ M, iso (C := MOD R) (pb_LModule f (M ')) ((pb_LModule f M) ')
    :=
    pb_deriv_to_deriv_pb_iso Tset bcp (D := C) f.

  Let bp_pb_iso {R S : Monad C} (f : Monad_Mor R S) 
    : ∏ M N, iso (C := MOD R) 
                 (bpM _ (pb_LModule f M)(pb_LModule f N) )
                 (pb_LModule f (bpM _ M N))
    :=
    binprod_pbm_to_pbm_iso f (cpC := bp).

  (* Let deriv_12_iso := *)
  (*   LMod_deriv12_iso bp bcp Tset. *)

  (* décomposition de l'hypothès *)
  Hypothesis
    adj1 : ∏ R M N,
            LModule_Mor R M (N ')
                        ≃
                        LModule_Mor R (bpM R M (Θ R)) N
    (* (LModuleBinProduct.LModule_binproduct bp (homset_property C) (a R) (tautological_LModule R)) *)
  .


(*
f : R -> S
u : M -> N' et v : N -> f* A

      u            v'
 M ---------> N' --------> (f* A)'
Par l'adjonction ça doit devenir

       !u        v
M x R ----> N --------> f*A

*)
  
  Hypothesis adj_law1 :
                ∏ R S (f : Monad_Mor (C := C) R S)
                  (M N : LModule R _) (A : LModule S _)
                  (u : LModule_Mor _ M (N '))
                  (v : LModule_Mor _ N (pb_LModule f A)),
                adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · ((# ∂ v))) =
                (adj1 R _ _ u : MOD R ⟦_,_⟧) · v.
  (*
Et maintenant,
On dit que l'action de l'adjonction  sur
   u         f*v           i
M ---> f* A -----> f* B' ----> (f* B)'
donne
      u x f                 i2                f* !v
M×R ---------> f* A x f* S ------> f*(A x S) -------> f* B
*)
  Hypothesis adj_law2 :
                ∏ R S (f : Monad_Mor (C := C) R S)
                  (M : LModule R _) (A B : LModule S _)
                  (u : LModule_Mor _ M (pb_LModule f A))
                  (v : LModule_Mor _ A (B ')),
                adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · (pb_LModule_Mor f v) · deriv_pb_iso f _)
                  =
                (BinProductOfArrows _ (LMOD_bp R _ _) (LMOD_bp R _ _) (u : MOD R ⟦_,_⟧) (monad_mor_to_lmodule f : MOD R ⟦_,_⟧))
                                    · bp_pb_iso f _ _
                                                      · pb_LModule_Mor f (adj1 _ _ _ v).

  Let Fmod a n (R  : rep_ar C (CoBinding_to_FullArity bcp Tset a n)) :=
    equiv_is_rep_ar_to_raw bp bcp Tset adj1 a n R (rep_τ C R).
  Lemma equiv_raw_ar_mor_law {n} {a : HalfArity}
        (R T : rep_ar C (CoBinding_to_FullArity bcp Tset a n))
  (f : Monad_Mor R T) :
  rep_ar_mor_law C R T (identity (CoBinding_to_FullArity bcp Tset a n)) f
                 ≃ rep_ar_mor_law C
                 (a := (DeBind_HArity bp a n,, tautological_harity))
                 (b := (DeBind_HArity bp a n,, tautological_harity))
                 ((R : Monad _),, Fmod a n R)
                 ((T : Monad _),, Fmod a n  T)
      (identity _) f.
  Proof.
    revert a R T f.
    induction n as [|n]; intros a R T f.
    - apply idweq.
    - eapply weqcomp.
      {
        apply equiv_raw_ar_one_mor_law.
        - apply adj_law1.
        - apply adj_law2.
      }
      apply IHn.
  Qed.

  (*)
  Fixpoint iso_FAr_full_HAr_rep n a :
    catiso ((rep_disp C)[{CoBinding_to_FullArity bcp Tset a n}])
           ((rep_disp C)[{DeBind_HArity bp a n ,, tautological_harity}]).
  Proof.
    destruct n as [|n].
    - apply identity_catiso.
    - eapply catiso_comp.
      + apply (@iso_FAr_HAr_rep C bp bcp Tset adj1 adj_law1 adj_law2).
      + apply (iso_FAr_full_HAr_rep n).
  Defined.
*)
End FAR_ToHAR_Rep.

(*



(* Tentative de généralisation sans SET *)
Section NoSet.

  Context {C : category}.
  Local Notation HalfArity := (HAr.arity C).
  Let MOD (R : Monad C) := (precategory_LModule R C).

  (* TODO déplacer ça dans arity *)
  Lemma HAr_rep_ar_mor_law_nt {a b : HAr.arity _} (M : HAr.rep_ar _ a)
             (N : HAr.rep_ar _ b)
           (f : arity_Mor a b) (g : Monad_Mor M N) :
  HAr.rep_ar_mor_law _ M N f g ≃ 
                     ((HAr.rep_τ _ M : (MOD _ ⟦_,_⟧))  · (monad_mor_to_lmodule g)  =
                      ((#a g)%ar : MOD _ ⟦_,_⟧)  ·
                                                 pb_LModule_Mor g
                                                 ((f N : MOD _ ⟦_,_⟧))
                                                 · pb_LModule_Mor g
                                                 ( HAr.rep_τ _ N )) .
  Proof.
    apply weqinvweq.
    eapply weqcomp.
    {  apply LModule_Mor_equiv;apply homset_property. }

    (* eapply weqcomp. *)
    {  apply nat_trans_eq_weq;apply homset_property. }
    (*
    (* assoc *)
    apply weqonsecfibers.
    intro x.
    cbn.
    rewrite assoc.
    apply idweq.
*)
  Defined.

  (*inutile TODO suppriemr *)
Definition FAr_rep_ar_mor_law_nt {a b : FullArity C} (M : rep_ar _ a) (N : rep_ar _ b)
           (f : FullArity C ⟦ a,  b⟧) (g : Monad_Mor M N) : 
  rep_ar_mor_law C M N f g ≃ (
   (rep_τ _ M : MOD _ ⟦_ , _⟧)  · ((#(codom a) g)%ar)  =
            ((#(dom a) g)%ar : MOD _ ⟦_ , _⟧)  · pb_LModule_Mor g (dom_mor f N)  ·
                                               pb_LModule_Mor g (rep_τ _ N)  ·
                                               pb_LModule_Mor g (codom_mor f N) 
                   ).
Proof.
    apply weqinvweq.
    eapply weqcomp.
    {  apply LModule_Mor_equiv;apply homset_property. }
    (* eapply weqcomp. *)
    {  apply nat_trans_eq_weq;apply homset_property. }
Defined.

  Context (a : HalfArity) .

  Let hs := homset_property C.
  Hypothesis ( bp : BinProducts C).
  Hypothesis ( bcp : BinCoproducts C).
  Hypothesis ( Tset : Terminal C).

  Let LMOD_bp (R : Monad C) :=
    (LModuleBinProduct.LModule_BinProducts R bp hs).

  Local Notation "M '" := (LModule_deriv Tset bcp M) (at level 30).

  Let deriv R :=
    (LModule_deriv_functor (TerminalObject Tset) bcp hs R).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject Tset) bcp hs _).

  (* Local Infix  "× '" := (LModule_deriv Tset bcp M) (at level 30). *)
  Local Notation "×ℜ" :=  (binproduct_functor  (LMOD_bp _)).
  Let bpM  (R : Monad C) :=
    (LModuleBinProduct.LModule_binproduct (R := R) bp (homset_property C)).
  (* (a R) (tautological_LModule R)). *)
  (* Local Notation "×ℜ" :=  (bpM. *)
  Local Notation Θ :=  (tautological_LModule).


  Hypothesis
    (adj :
       ∏ R : Monad C,
             are_adjoints
               (functor_fix_snd_arg (MOD R)
                                    (MOD R)
                                    (MOD R)
                                    (binproduct_functor (LMOD_bp R))
                                    (tautological_LModule R))
               (DerivationIsFunctorial.LModule_deriv_functor Tset bcp hs R)
    ).

  (* décomposition de l'hypothès *)
  Hypothesis
    (adj1 : ∏ R M N,
     LModule_Mor R M (N ')
                 ≃
         LModule_Mor R
         (bpM R M (Θ R))
    (* (LModuleBinProduct.LModule_binproduct bp (homset_property C) (a R) (tautological_LModule R)) *)
    N
    ).


  (* (adj1 : ∏ R, *)
  (*    LModule_Mor R (a R) (Derivative.LModule_deriv Tset bcp (tautological_LModule R)) *)
  (*                ≃ *)
  (*        LModule_Mor R *)
  (*   (LModuleBinProduct.LModule_binproduct bp (homset_property C) (a R) (tautological_LModule R)) *)
  (*   (tautological_LModule R) *)
  (*   ) *)



  Let nat_d_HAr  := nat_deriv_HAr (C:=C) bp bcp Tset .
  Let nat_p_HAr  := nat_prod_HAr (C:=C) bp bcp Tset .

  Let a_n n : FullArity C := a ,, nat_d_HAr n.

  Let bpHAr := harity_BinProducts (C := C) bp.

  Local Notation BPO := (BinProductObject _).
  Let b n : HalfArity := BPO (bpHAr a (nat_p_HAr n)).

  Definition equiv_is_rep_ar_to_raw R : 
                 LModule_Mor R (a R)(nat_d_HAr 1 R) ≃
                             LModule_Mor R (b 1 R)(tautological_LModule R).
  Proof.
    eapply weqcomp.
    - eapply (iso_comp_left_weq (C := MOD R)).
      apply LMod_deriv12_iso.
    - eapply weqcomp; revgoals.
      + eapply (iso_comp_right_weq (C := MOD R)).
        unfold b.
        eapply LMod_prod12_iso.
      + cbn.
        apply adj1.
        (* apply (adjunction_hom_weq (adj R)). *)
  Defined.

  Local Notation Fmod := equiv_is_rep_ar_to_raw.

  Definition FAr_to_HAr_ob :  rep_ar _ (a_n 1) ≃ HAr.rep_ar _ (b 1) :=
    weqfibtototal _ _ equiv_is_rep_ar_to_raw.

  Local Notation Fob := FAr_to_HAr_ob.

  (* Definition zoppr (A B : UU) (e : A ≃ B) (x y : A) : x = y ≃ e x = e y. *)
  (*   apply weqonpaths. *)
  (* Search ((_ = _) ≃ (_ = _)). *)


   (* (HAr.rep_τ _ M : MOD R  · g  = ((#a g)%ar:nat_trans _ _)  · f N  · HAr.rep_τ N  . *)
(* Definition FAr_rep_ar_mor_law_nt {a b : FArity} (M : rep_ar a) (N : rep_ar b) *)
(*            (f : FArity ⟦ a,  b⟧) (g : Monad_Mor M N) :  *)
(*   rep_ar_mor_law  M N f g ≃  (rep_τ M : nat_trans _ _) · ((#(codom a) g)%ar:nat_trans _ _)  = *)
(*             ((#(dom a) g)%ar:nat_trans _ _)  · dom_mor f N  · *)
(*                                             rep_τ N c · codom_mor f N c. *)
  Let deriv_pb_iso {R S : Monad C} (f : Monad_Mor R S) 
      : ∏ M, iso (C := MOD R) (pb_LModule f (M ')) ((pb_LModule f M) ')
    :=
    pb_deriv_to_deriv_pb_iso Tset bcp (D := C) f.

  Let bp_pb_iso {R S : Monad C} (f : Monad_Mor R S) 
    : ∏ M N, iso (C := MOD R) 
                 (bpM _ (pb_LModule f M)(pb_LModule f N) )
                 (pb_LModule f (bpM _ M N))
    :=
    binprod_pbm_to_pbm_iso f (cpC := bp).

  Let deriv_12_iso :=
    LMod_deriv12_iso bp bcp Tset.

  (*
f : R -> S
u : M -> N' et v : N -> f* A

      u            v'
 M ---------> N' --------> (f* A)'
Par l'adjonction ça doit devenir

       !u        v
M x R ----> N --------> f*A


*)
  Hypothesis (adj_law1 :
                ∏ R S (f : Monad_Mor (C := C) R S)
                  (M N : LModule R _) (A : LModule S _)
                  (u : LModule_Mor _ M (N '))
                  (v : LModule_Mor _ N (pb_LModule f A)),
                adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · ((# ∂ v))) =
                (adj1 R _ _ u : MOD R ⟦_,_⟧) · v).
  (*
Et maintenant,
On dit que l'action de l'adjonction  sur
   u         f*v           i
M ---> f* A -----> f* B' ----> (f* B)'
donne
      u x f                 i2                f* !v
M×R ---------> f* A x f* S ------> f*(A x S) -------> f* B
*)
  Hypothesis (adj_law2 :
                ∏ R S (f : Monad_Mor (C := C) R S)
                  (M : LModule R _) (A B : LModule S _)
                  (u : LModule_Mor _ M (pb_LModule f A))
                  (v : LModule_Mor _ A (B ')),
                adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · (pb_LModule_Mor f v) · deriv_pb_iso f _)
                  =
                (BinProductOfArrows _ (LMOD_bp R _ _) (LMOD_bp R _ _) (u : MOD R ⟦_,_⟧) (monad_mor_to_lmodule f : MOD R ⟦_,_⟧))
                                    · bp_pb_iso f _ _
                                                      · pb_LModule_Mor f (adj1 _ _ _ v)

                (* (# ×ℜ (dirprodpair (u : MOD R ⟦_,_⟧) (monad_mor_to_lmodule f : MOD R ⟦_,_⟧))) *)
                

                (* adj1 R  _ _  ((u : MOD R ⟦_,_⟧) · (pb_LModule_Mor f v) · deriv_pb_iso f _) *)
             ).

  Lemma rep_ar_mor_law_a_n_equiv {R S : rep_ar C _}
        (f : Monad_Mor R S)
    : rep_ar_mor_law C R S (identity (a_n 1)) f ≃
                     (
                     (rep_τ _ R : MOD _ ⟦ _, _⟧) · deriv_12_iso R
                     · (# ∂ (monad_mor_to_lmodule f))
                     =
                     ((# a f)%ar : MOD _ ⟦_,_⟧)
                       · (pb_LModule_Mor f ((rep_τ _ S : MOD S ⟦_,_⟧)
                                                  ·
                                                  deriv_12_iso S
                                           ) : MOD _ ⟦ _, _⟧) ·
                       deriv_pb_iso f _
  ).
  Proof.
    apply weqinvweq.
    eapply weqcomp; [apply LModule_Mor_equiv; apply homset_property|].
    eapply weqcomp; [apply nat_trans_eq_weq; apply homset_property|].
    apply weqonsecfibers.
    intro x.
    cbn.
    repeat rewrite id_right.
    apply idweq.
  Qed.

  Definition equiv_raw_ar_mor_law 
     {R S : rep_ar _ (a_n 1)} (f : Monad_Mor R S) :
                      rep_ar_mor_law _ R S (identity _) f ≃
                                     HAr.rep_ar_mor_law _ (Fob R) (Fob S)
                                     (identity (C := arity_category)  _) f.
  Proof.
    eapply weqcomp; [apply rep_ar_mor_law_a_n_equiv|].
    eapply weqcomp;[ eapply (weqonpaths (adj1 _ _ _))|].
    rewrite adj_law2.
    eapply (transportf (fun z => (z = _) ≃ _)).
    {
    eapply pathsinv0.
    apply adj_law1.
    }
    eapply weqcomp;[apply LModule_Mor_equiv;apply homset_property|].
    eapply weqcomp;[apply nat_trans_eq_weq;apply homset_property|].
    apply weqonsecfibers.
    intro c.
    cbn.

    unfold BinCoproduct_of_functors_ob,binproduct_nat_trans_data; cbn.
    unfold binproduct_nat_trans_pr1_data,binproduct_nat_trans_pr2_data; cbn.
    repeat rewrite id_right.
    repeat rewrite id_left.
    apply idweq.
  Qed.
  (* The following part is useless to use SigEquivRep but we do it for sport *)

  Definition FAr_to_HAr_mor (R S : rep_ar _ (a_n 1)) :
             ( rep_ar_mor_mor _ R S (identity _)) ≃
    HAr.rep_ar_mor_mor _ _ _  (Fob R) (Fob S) (identity (C := arity_category) _ ) :=
        weqfibtototal _ _ (@equiv_raw_ar_mor_law R S).


  Local Notation Fmor := FAr_to_HAr_mor.

  Definition FAr_to_HAr_functor_data : functor_data ((rep_disp C)[{a_n 1}])
                                                    ((HAr.rep_disp C)[{b 1}]) :=
    functor_data_constr ((rep_disp C)[{a_n 1}]) ((HAr.rep_disp C)[{b 1}])  Fob  Fmor.

  Lemma FAr_to_HAr_is_functor : is_functor FAr_to_HAr_functor_data.
  Proof.
    split.
    - intro R.
      now apply HAr.rep_ar_mor_mor_equiv.
    - intros R S T f g.
      apply HAr.rep_ar_mor_mor_equiv.
      intro c.
      etrans;[ apply transport_arity_mor|].
      apply pathsinv0.
      apply HAr.transport_arity_mor.
  Defined.

  Definition FAr_to_HAr_functor : functor _ _ :=
    _ ,, FAr_to_HAr_is_functor.

  Local Notation FS := FAr_to_HAr_functor.

  Definition iso_FAr_HAr_rep : catiso _ _ :=
     FS,, (λ x y  , weqproperty (Fmor x y)),, weqproperty Fob.
End NoSet.
  

*)
