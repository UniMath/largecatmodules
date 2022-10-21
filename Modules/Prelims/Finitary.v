(** * Finitary functors

Definition of finitary functor F: it is such that FX is the union of the image by F
of the finite subsets of X.

The goal is to show that if F -> G is en epimorphism and F is finitary, then G also is finitary

The category of finite subsets of X is defined as the comma category restricted to
monomorphisms n → X, which I denote by I ↓ X,  where I : FinSet -> Set. Of course, X is the colimit of the
diagram (J : I ↓ X  → Set).

A finitary functor F by definition is a functor which commutes with any filtered colimit.
Equivalently, Vladimir Voevodsky suggested another definition: it is a functor F such that for any
set X it commutes with any colimit of diagram (J : I ↓ X  → Set).
This leads to a first attempt in this file (some commented code is about that), but the problem is
that it is painful to define binary coproduct in I ↓ X, which is necessary for the proof that for
any set X and any functor, the canonical morphism colim (F ∘ J) -> F (colim J) is monic
(explanation comes after), which requires as an intermediate step to show that I ↓ X is filtered.
The pain is that not much is formalized in UniMath about finite sets.

Therefore I suggest an alternative definition (not yet implemented) : it is the same but I
do not enforce the subsets of X to be finite in the slice category. The difficulty is thus
reported to the proof that ∐_n∈N F(n) Xⁿ → F(X) is epimorphic for any finitary functor F, but
if we don't need this it is ok.

How to define binary coproducts in the category of subsets of X:
let p : m → X and q : n → X be two subsets of X (i.e., p and q are mono).
Then we define the binary coproduct (which is the union) as the mono part of the
epi-mono factorization of [p,q]:m+n → X.

Btw, I am not sure this is really a binary coproduct, but who cares. Anyway it is clear this construction
is needed in the proof that I ↓ X is filtered


*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.Limits.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.Combinatorics.FiniteSets.

Require Import UniMath.MoreFoundations.DecidablePropositions.


(*
Definition subsetFiniteness_decidable {X : UU} (fX : isfinite X){P : X -> hProp}(dP : ∏ x , decidable (P x))
  : isfinite (∑ x , P x) :=
   (subsetFiniteness fX (fun x => _ ,, decidable_to_isdecprop (dP x))).
*)

(*

Definition stn_rect (P : ∏ (n : nat), (⟦ n ⟧)%stn -> UU)
           (P0 : ∏ n , P (S n) firstelement ) 
           (PS : ∏ {n} (p : (⟦ n ⟧)%stn) , (P n p) ->
                 P (S n) (dni_firstelement  p))
  : ∏ n p , P n p.
Proof.
  intro n.
  induction n.
  {
    induction p as [p ip].
    induction (nopathsfalsetotrue ip). }
  induction p as [p ip].
  induction p.
  - assert (hip : ip = idpath _) by apply uip, isasetbool.
    rewrite hip.
    apply P0.
  - apply (PS n (p ,, ip) (IHn _)).
Defined.
Definition stn_rec (P : UU)
           (P0 : P)
           (PS : P -> P)
  : ∏ n (p : (⟦ n ⟧)%stn)  , P :=
  stn_rect (fun _ _ => P)(fun _ => P0) (fun _ _ => PS).

Definition isin {X : UU}  (dX : isdeceq X) (x : X) (n : nat) : ∏ (f : (⟦ n ⟧)%stn -> X) , bool.
Proof.
  induction n as [|n' _].
  { exact (fun _ => false). }
  use (stn_rect (fun n _ =>  ((⟦ n ⟧)%stn -> X) -> bool) (fun n f => booleq dX (f firstelement) x)).
  cbn.
  - intros n p IHp f.
    refine (if (booleq dX (f (dni_firstelement p)) x) then _ else false).
    apply IHp.
    use (funcomp _ f).
    apply dni_firstelement.
  - exact lastelement.
Defined.

Definition countunique {X : UU}  (dX : isdeceq X) (n : nat) : ∏ (f : (⟦ n ⟧)%stn -> X) , nat.
Proof.
  use (stn_rect (fun n _ =>  ((⟦ n ⟧)%stn -> X) -> nat) (fun n f => 1)).
  cbn.
  - intros n' p IHp f.
    assert (count : nat).
    {
      apply IHp.
      use (funcomp _ f).
      apply dni_firstelement.
    }
    refine (if isin dX (f lastelement) (funcomp (dni_firstelement  _) f) then S count else count).
    apply IHp.
    use (funcomp _ f).
  - exact lastelement.



Definition stn_rec (P : UU)
           (P0 : P)
           (PS : P -> P)
                 P (S n) (dni_firstelement  p))
  : ∏ n p , P n p.
Proof.
  intro n.
  induction n.
  {
    induction p as [p ip].
    induction (nopathsfalsetotrue ip). }
  induction p as [p ip].
  induction p.
  - assert (hip : ip = idpath _) by apply uip, isasetbool.
    rewrite hip.
    apply P0.
  - apply (PS n (p ,, ip) (IHn _)).
Defined.
*)
    

Definition imagehSet {X : UU} {Y : hSet} (f : (X → Y)) : hSet :=
  Subtypes.carrier_set (fun (y : Y) => ∥ hfiber f y ∥).


(* Definition finstructimage (L : LEM){X : UU}(sX : finstruct X) {Y : hSet} (f : (X → Y)) : finstruct (image f). *)
(* Proof. *)
(*   use finstructpair. *)
  
(*
Definition isfiniteimage (L : LEM) {X : UU}(fX : isfinite X) {Y : hSet} (f : (X → Y)) : isfinite (image f).
Proof.
  generalize fX.
  apply hinhfun.
  intros 
Qed.
*)
  

Open Scope cat.

Definition colim_on_nat {C D : precategory}{F G : C ⟶ D} (p : F ⟹ G){g : graph}{d : diagram g C}
                  (cF : ColimCocone (mapdiagram F d))
                  (cG : ColimCocone (mapdiagram G d))
  :
    D ⟦ colim cF , colim cG ⟧
      :=
        colimOfArrows cF cG
                      (λ u : vertex g, p (dob d u))
                      (λ (u v : vertex g) (e : edge u v), nat_trans_ax p (dob d u) (dob d v) (dmor d e)).

Definition colimcompare
   {C : precategory}{D : precategory}(F : C ⟶ D){g : graph}{d : diagram g C}
   (cd : ColimCocone d)
   (cFd : ColimCocone (mapdiagram F d))
  : D ⟦ colim cFd ,  F (colim cd) ⟧ :=
    colimArrow _ _  (mapcocone F _ (colimCocone cd)).


(**

colim (F ∘ J) --> F (colim J)
   |                |
   |                |
   |                |
   |                |
   V                V
 colim (G ∘ J) --> G (colim J)
*)
Lemma colim_on_nat_is_nat {C D : precategory}{F G : C ⟶ D} (p : F ⟹ G){g : graph}{d : diagram g C}
                  (cd : ColimCocone d)
                  (cF : ColimCocone (mapdiagram F d))
                  (cG : ColimCocone (mapdiagram G d)) :
        colim_on_nat p cF cG · colimcompare G  cd cG
    = (colimcompare F  cd cF) · p (colim cd).
Proof.
  etrans; [apply precompWithColimOfArrows|].
  apply pathsinv0.
  apply colimArrowUnique.
  intro u.
  cbn.
  etrans.
  {
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    unfold colimcompare.
    apply ( colimArrowCommutes cF (F (colim cd))).
  }
  apply nat_trans_ax.
Qed.

Local Notation "'SET' / X" :=(slice_precat SET X has_homsets_HSET) (at level 3).

Definition is_finite_subob (X : hSet) (fX : SET / X) : hProp :=
  ((hProppair (isincl (slicecat_ob_morphism _ _ fX)) (isapropisincl _))).

(*
Definition is_finite_subob (X : hSet) (fX : SET / X) : hProp :=
  ((isfinite (pr1hSet (slicecat_ob_object _  _ fX))) ∧
    (hProppair (isincl (slicecat_ob_morphism _ _ fX)) (isapropisincl _))).
*)

Definition FinSubsets_precategory (X : hSet) : precategory :=
  full_sub_precategory (C := SET / X) (is_finite_subob X).

(*
Lemma FinSubsets_mor_is_injective {X : hSet} {A B : FinSubsets_precategory X} (f : SET / X ⟦ pr1 A , pr1 B ⟧) :
   isincl (slicecat_mor_morphism _ _ ( f)).
Proof.
  eapply isincltwooutof3a; revgoals.
  - eapply (transportf isincl).
    + exact (slicecat_mor_comm _ _  f).
    + exact (pr2 (pr2 A)).
  - exact (pr2 (pr2 B)).
Defined.
*)


Definition forget_FinSubsets (X : hSet) : FinSubsets_precategory X ⟶ HSET :=
  (sub_precategory_inclusion _ _ ∙ slicecat_to_cat _ _).


Definition BinCoproduct_FinSubsetsTip (L : LEM) {X : hSet} (A B : FinSubsets_precategory X) :
  FinSubsets_precategory X.
Proof.
  set (AB := (sumofmaps (pr2 (pr1 A)) (pr2 (pr1 B)))).
  unshelve refine ((_ ,, _) ,, _).
  - exact (imagehSet AB).
  - exact (pr1image AB).
  - apply isinclpr1image.
    (*
    split.
    + apply subsetFiniteness_decidable.
      isfinite
    + apply isinclpr1image.
*)
Defined.
    (* assert (h' := (pr1image AB)). *)
    (* cbn. *)
    (* exact h'. *)
    (* cbn . *)

Lemma BinCoproducts_FinSubsets (X : hSet) : BinCoproducts (FinSubsets_precategory X).
Proof.
  intros A B.
  use make_BinCoproduct.
    use (bin_coproducts_in_full_subcategory
           (C := category_pair(SET / X) (has_homsets_slice_precat (homset_property SET) X ))
      (is_finite_subob X)).
    + apply BinCoproducts_slice_precat, BinCoproductsHSET.
    + intros X1 X2 [fX1 iX1]  [fX2 iX2].
Abort.

Local Notation coSET d := (ColimsHSET_of_shape _ d).

Definition diag_subobj (X : hSet) :=
  (diagram_from_functor (FinSubsets_precategory X) HSET (forget_FinSubsets X)).

Definition colimcompare_fin (F : HSET ⟶ HSET) (X : hSet) : _ :=
  (colimcompare (C := HSET)(D := HSET) F
                            (coSET (diag_subobj X))
                            (coSET _)
              ).

Definition colimcompare_fin_injempty (F : HSET ⟶ HSET)  : isweq (colimcompare_fin F emptyHSET).
Proof.
Admitted.

(** This is true of any filtered category *)
Definition colimfin_ante  (X : hSet)
           (g := (graph_from_precategory (FinSubsets_precategory X) ))
           (d : diagram g HSET)
           (cc := coSET d)
           (a b : pr1hSet (colim cc)) : ∥ ∑ (c : FinSubsets_precategory X), pr1hSet (dob d c) × pr1hSet (dob d c) ∥.
Proof.
  generalize (issurjsetquotpr _ a); apply factor_through_squash;[apply propproperty|].
  intros [[a' fa'] ha].
  generalize (issurjsetquotpr _ b); apply hinhfun.
  intros [[b' fb'] hb].
  use tpair.
  - eapply BinCoproductObject.
    use (bin_coproducts_in_full_subcategory
           (C := category_pair(SET / X) (has_homsets_slice_precat (homset_property SET) X ))
      (is_finite_subob X)).
    + apply BinCoproducts_slice_precat, BinCoproductsHSET.
    + intros. cbn -[isfinite].
Abort.

(** The hard part *)
(* non empty sets *)
Definition colimcompare_fin_inj (F : HSET ⟶ HSET) (X : hSet) : ∥ X ∥ -> isincl (colimcompare_fin F X).
Proof.
  apply factor_through_squash; [ apply isapropisincl|].
  intro x.
  apply isinclbetweensets; [apply setproperty|apply setproperty|].
  intros a b eq_ab.
  generalize (issurjsetquotpr _ a); apply factor_through_squash; [ apply setproperty |].
  intros [[a' fa'] ha].
  generalize (issurjsetquotpr _ b); apply factor_through_squash; [ apply setproperty |].
  intros [[b' fb'] hb].
  (*
  apply isinclbetweensets; [apply setproperty|apply setproperty|].
  setquotpr
    issurjsetquotpr
    issurjective
  cobase.
  isincl
*)
Abort.

Definition is_finitary (F : HSET ⟶ HSET) : UU :=
  ∏ X , isweq (colimcompare_fin F X).



Definition fin_nat_alt_eq
           {F G : HSET ⟶ HSET} (p : F ⟹ G)
            (X : hSet)
           (* (w := weqpair _ (finF X)) *)
  :
        colim_on_nat p (coSET _) (coSET _) ·
      colimcompare_fin G X
  = (colimcompare_fin F X) · p _ := colim_on_nat_is_nat _ _ _ _.

(** This is true of any colimit shape *)
Lemma epi_preserves_finepi {F G : HSET ⟶ HSET}
      {p : F ⟹ G}(epip : ∏ Y, isEpi (p Y))
      (finF : is_finitary F) (X : hSet) : isEpi (colimcompare_fin G X).
Proof.
  eapply isEpi_precomp.
  apply (transportb (isEpi (C := HSET) (x := _) (y := _)) (fin_nat_alt_eq p  X)) .
  apply isEpi_comp.
  - apply EpisAreSurjective_HSET.
    apply issurjectiveweq.
    apply finF.
  - apply epip.
Qed.

(* isweqinclandsurj *)
Lemma epi_preserves_finitary {F G : HSET ⟶ HSET}
      (p : F ⟹ G)(finF : is_finitary F) : is_finitary G.
Proof.
  (* this is a consequence of epi_preserves_finepi and colimcompare_fin_inj* *)
Abort.
  
