Add LoadPath "/home/user/0my/GITHUB/".
Require Import ZFC.Sets.
Require Import ZFC.Axioms.

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

(** GD END **)