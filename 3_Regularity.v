(* PUBLIC DOMAIN
The main source of the proofs:
https://math.stackexchange.com/questions/452809/epsilon-induction-implies-axiom-of-foundation-or-regularity
Author: Georgy Dunaev, georgedunaev@gmail.com
*)
Add LoadPath "/home/user/0my/GITHUB/".

Require Import ZFC.Sets.
Require Import Setoid.

(* Requires for ClassicRegularity module. *)
Require Classical_Prop.
Require Classical_Pred_Type.

(* Epsilon induction. *)
Theorem eps_ind (R:Ens->Prop)
(Sou_R:forall a b, EQ a b -> (R a <-> R b))
: (forall x:Ens, (forall y, IN y x -> R y) -> R x)
-> forall z, R z.
Proof.
intros.
induction z.
apply H.
simpl.
intros y q.
destruct q as [a G].
rewrite  (Sou_R y (e a)).
apply H0.
exact G.
Defined.

(* (P x) means "Every set that contains x as an element is regular." *)
Definition P x := forall u : Ens, (IN x u -> exists y,
IN y u /\ forall z, IN z u -> ~ IN z y).

Definition epsmin a b := IN a b /\ forall c, IN c b -> ~ IN c a.

(* Soundness of the definition of P. *)
Theorem sou_P : forall a b : Ens, EQ a b -> P a <-> P b.
Proof.
intros.
unfold P.
split; intros.
+ apply IN_sound_left with (E':=a) in H1.
  apply H0. apply H1.
  apply EQ_sym. exact H.
+ apply IN_sound_left with (E':=b) in H1.
  apply H0. apply H1.
  exact H.
Defined.

(* Here I follow Zuhair's proof from source.
https://math.stackexchange.com/users/489784/zuhair *)

(* Unending chain *)
Definition UC c := forall m, IN m c -> exists n, IN n m /\ IN n c.
Definition WF x := ~(exists c, UC c /\ IN x c).

(* Inductive step *)
Theorem Zuhair_1 (a:Ens): (forall x, IN x a -> WF x) -> WF a.
Proof.
unfold WF.
intros H K0.
pose (K:=K0).
destruct K as [c [M1 M2]].
unfold UC in M1.
pose (B:=M1 a M2).
destruct B as [n [nina ninc]].
apply (H n nina).
exists c.
split.
exact M1.
exact ninc.
Defined.

(* Soundness of WF *)
Theorem sou_WF : forall a b : Ens, EQ a b -> WF a <-> WF b.
Proof.
intros.
unfold WF.
* split.
+ intros A B.
  apply A.
  destruct B as [c [a1 a2]].
  exists c.
  split. exact a1.
  apply IN_sound_left with (E:=b).
  apply EQ_sym. exact H.
  exact a2.
+ intros A B.
  apply A.
  destruct B as [c [a1 a2]].
  exists c.
  split. exact a1.
  apply IN_sound_left with (E:=a).
  exact H.
  exact a2.
Defined.

(* Induction. "Every set is well-founded." *)
Theorem Zuhair_2 (y:Ens): WF y.
Proof.
apply eps_ind.
- exact sou_WF.
- intros a. exact (Zuhair_1 a).
Defined.

(* Formalization of Andreas Blass variant of proof. 
https://math.stackexchange.com/users/48510/andreas-blass *)
Module ClassicRegularity.

Import Classical_Prop.
Import Classical_Pred_Type.
Theorem Blass x : P x.
Proof.
unfold P.
pose (A:=Zuhair_2 x); unfold WF in A.
intros u xinu.
(* Series of the equivalent tranformations.*)
apply not_ex_all_not with (n:=u) in A.
apply not_and_or in A.
 destruct A as [H1|H2].
 2 : destruct (H2 xinu).
 unfold UC in H1.
apply not_all_ex_not in H1.
 destruct H1 as [yy yH].
 exists yy.
apply imply_to_and in yH.
 destruct yH as [Ha Hb].
 split. exact Ha.
 intro z.
apply not_ex_all_not with (n:=z) in Hb.
apply not_and_or in Hb.
 intro v.
 destruct Hb as [L0|L1]. exact L0.
 destruct (L1 v).
Defined.

(* Standard formulation of the regularity axiom. *)
Theorem axreg (x:Ens) :
(exists a, IN a x)->(exists y, IN y x /\ ~ exists z, IN z y /\ IN z x)
.
Proof.
pose (Q:= Blass).
unfold P in Q.
intro e.
destruct e as [z zinx].
pose (f:= Q z x zinx).
destruct f as [g G].
exists g.
destruct G as [G1 G2].
split.
+ exact G1.
+ intro s.
  destruct s as [w [W1 W2]].
  exact (G2 w W2 W1).
Defined.

End ClassicRegularity.

(* Other theorems *)

Theorem axExt : forall x y : Ens,
   EQ x y <-> forall z, (IN z x <-> IN z y).
Proof.
intros.
split.
+ intros.
  split.
  - apply IN_sound_right. exact H.
  - apply IN_sound_right. apply EQ_sym. exact H.
+ induction x as [A f], y as [B g].
  intro K.
  simpl in * |- *.
  split.
  - intro x.
    apply K.
    exists x.
    apply EQ_refl.
  - intro y.
    assert (Q:EXType B (fun y0 : B => EQ (g y) (g y0))).
    * exists y.
      apply EQ_refl.
    * destruct (proj2 (K (g y)) Q).
      exists x.
      apply EQ_sym.
      exact H0.
Defined.

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

Require Import ZFC.Axioms.

(* class must respect extensional equality
   sree is a witness of the soundness of class' definition *)
Section TheoremsAboutClasses.
Context (s:Ens->Prop)
        (sree : forall (w1 w2:Ens), EQ w1 w2 -> s w1 <-> s w2).

Theorem rewr (w1 w2:Ens) (J:s w1) (H : EQ w1 w2) : s w2.
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
    apply (rewr _ _  K H).
  * exact y.
  * exact u.
+ intro u.
  Check IN_Comp_P m.
  apply (IN_Comp_P m).
  exact rewr.
  exact u.
Defined.

End TheoremsAboutClasses.

Theorem INC_antisym : forall E E' : Ens,
  INC E E' -> INC E' E -> EQ E E'.
Proof.
unfold INC in |- *; auto with zfc.
Show Proof.
Defined.

Require Import ZFC.Cartesian.
Require Import ZFC.Replacement.




