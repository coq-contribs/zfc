Add LoadPath "/home/user/0my/GITHUB/".
Require Import ZFC.Sets.
Require Import ZFC.Axioms.
Require Import ZFC.Cartesian.
Require Import ZFC.Replacement.

Require Import Setoid. (* for 'rewrite' tactic *)

(** GD BEGIN: SUBCLASS OF SET IS A SET **)
(* every set is a class *)
(* 1) function *)
Theorem esiacf : Ens -> (Ens -> Prop).
Proof.
intro e.
exact (fun x => IN x e).
Defined.

(* "is a set" predicate *)
Definition ias (s: Ens -> Prop) : Prop.
Proof.
exact (EXType _ (fun x:Ens => forall w, s w <-> esiacf x w)).
Defined.

(* class must respect extensional equality
   sree is a witness of the soundness of class' definition *)
Section sec.
Context (s:Ens->Prop)
        (sree : forall (w1 w2:Ens), EQ w1 w2 -> s w1 <-> s w2).

Theorem thm (w1 w2:Ens) (J:s w1) (H : EQ w1 w2) : s w2.
Proof.
rewrite <- (sree w1 w2); assumption.
Defined.

(* subclass of a set is a set *)
Theorem scosias (m:Ens) 
(sc : forall x, s x -> (esiacf m) x) 
: ias s.
Proof.
unfold ias.
unfold esiacf in * |- *.
(* { x e. m | s x }*)
exists (Comp m s).
intro w.
split.
+ intro u.
  pose(y:=sc w u).
  unfold esiacf in * |- *.
  apply IN_P_Comp.
  * intros w1 w2 K H.
    apply (thm _ _  K H).
  * exact y.
  * exact u.
+ intro u.
  Check IN_Comp_P m.
  apply (IN_Comp_P m).
  exact thm.
  exact u.
Defined.

End sec.

Theorem INC_antisym : forall E E' : Ens,
  INC E E' -> INC E' E -> EQ E E'.
Proof.
unfold INC in |- *; auto with zfc.
Defined.


Require Import ZFC.zfcOmega.

Section inddef.

Definition Na0 : nat -> Ens.
intros H.
induction H.
exact Vide.
Check Class_succ.
exact (Paire IHnat (Sing IHnat)).
Defined. 

Definition Omega : Ens := sup nat Nat.

Check Ens.
(*Inductive Ens2 : Type :=
    sup2 : forall A : Type, (A -> Ens2) -> Ens2.
Fixpoint f (x:Ens2):Ens.
destruct x.
eapply (sup A).
intro a. exact (f (e a)).
Defined.
Definition what_is_it : Ens := sup Ens (fun x => f x).*)

(*
Set Universe Polymorphism.
Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.
 Definition what_is_it : Ens := sup Ens (fun x => x).
*)
Check true.
Inductive fm := 
| Atom  : nat->fm
| Impl  : fm->fm->fm
.
Check Nat.
Check Couple.
(* Task1: inject formulas into Ens. *)
(* Strings of symbols are functions from the initial fragment of omega.
Need orpairs. (Couple)
[IN w A*] means there exists n in On such that [w:n->A]
*)
Check functional. (* is for metaformulas *)
(* Simple encoding of the implicative fragment of formulas. *)
Theorem transl : fm -> Ens.
Proof.
intro f; induction f.
exact (Nat n).
exact (Couple IHf1 IHf2).
Defined.
(* Set of formulas: *)
Definition Fm := sup fm transl.
(* Let's define the set of valuations. *)
Definition valuations := nat -> bool.
Definition translb : bool -> Ens.
Proof.
intro b; destruct b.
exact (Nat 1).
exact (Nat 0).
Defined.

Definition transl_val : valuations -> Ens.
Proof.
intro v.
unfold valuations in v.
Print Comp.
(* { <(Nat n),b> | aeOmega & EQ b (translb (v n)) *)
Abort.
Check Nat.
Check Omega.

Section exist2sig.
Context (exist2sig : forall A P,
 (EXType A (fun x:A=>P x))->(sig A (fun x:A=>P x))).
(* inverse to Nat *)
Theorem taN : forall x:Ens, IN x Omega -> nat.
Proof.
intros x H.
simpl in H.
Fail destruct H.
Fail fail "test".
apply exist2sig in H.
destruct H as [n K].
exact n.
Defined. (*Abort.*)
End exist2sig.

(**)

(*
Inductive Ens : Type :=
    sup : forall A : Type, (A -> Ens) -> Ens.
*)

Definition mysing : Ens := sup Un (fun x => Vide).
Goal IN Vide mysing.
Proof.
unfold mysing.
unfold IN.
exists .
constructor.
apply EQ_refl.
Defined.

Section tranfinite_induction.
Context (s:Ens->Prop).
Check sup.
Context (lcase:forall (A:Type) (f:A->Ens),
 (forall a:A, s (f a))-> s (sup A f)).
Theorem tr_ind : forall x:Ens, (s x).
Proof.
intro x.
induction x.
apply lcase.
exact H.
Defined.
End tranfinite_induction.


Definition Power (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun P : A -> Prop =>
         sup _
           (fun c : depprod A (fun a : A => P a) =>
            match c with
            | dep_i a p => f a
            end))
  end.

(* TODO: intersection of classes *)
(*
Definition Na1 : nat -> Ens.
intros H.
elim H.
exact Vide. (*empty set*)
intros a b.
simple induction 1.
exact 1.
 intros a b. exact (H+a+b).
Defined.
Compute Na 4.

Definition Omega:Ens.
Context (PropVars:Ens).
Context ()
*)
End inddef.
(** GD END **)