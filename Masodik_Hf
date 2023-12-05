(*1,2*)
Structure ComGroup : Type := mk_ComGroup
{
A :> Set;

op : A -> A -> A ;
inv : A -> A ;
z : A ;

op_assoc : forall a b c, op a (op b c) = op (op a b) c;
op_z : forall a, op a z = a /\ op z a = a ;
op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z;
op_com : forall a b, op a b = op b a
}.

Inductive Z_3 : Set :=
  | n3 : Z_3 
  | a3 : Z_3
  | b3 : Z_3.

Definition ope x y :=
  match x , y with
  | n3 , y => y
  | x , n3 => x
  | a3 , b3 => n3
  | b3 , a3 => n3 
  | a3 , a3 => b3
  | b3 , b3 => a3
  end.

Definition inve x :=
  match x with
  | n3 => n3
  | a3 => b3
  | b3 => a3
  end.

Theorem Z_3_eq_dec : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto; right; discriminate.
Defined.

Theorem Z_3_ComGroup : ComGroup.
Proof.
  apply (mk_ComGroup Z_3 ope inve n3).
  induction a, b, c; compute; auto.
  induction a; auto. 
  induction a; auto.
  induction a; auto.
  induction b; auto.
Defined.


Inductive Z_6 : Set :=
  | n : Z_6 
  | a : Z_6
  | b : Z_6
  | c : Z_6 
  | d : Z_6
  | e : Z_6.

Definition inv_Z_6 x :=
  match x with
  | n => n
  | a => e
  | b => d
  | c => c
  | d => b
  | e => a 
  end.

Definition z_Z_6 :=n.

Require Import Coq.Arith.PeanoNat.

Definition Z_6_to_nat (x : Z_6) : nat :=
    match x with
    |n => 0
    |a => 1
    |b => 2
    |c => 3
    |d => 4
    |e => 5
    end.

Definition nat_mod_to_Z_6 (x y : nat) : Z_6 :=
  let w := (x + y) mod 6 in
  match w with
  | 0 => n
  | 1 => a
  | 2 => b
  | 3 => c
  | 4 => d
  | 5 => e
  | _ => n (* default eset *)
  end.

Definition op_Z_6 x y :=
  nat_mod_to_Z_6 (Z_6_to_nat x)(Z_6_to_nat y).

Theorem Z_6_eq_dec : forall (x y: Z_6), x = y \/ x <> y.
Proof. 
  induction x, y.
  all: auto.
  all:right. 
  all:discriminate.
Defined.

Theorem Z_6_ComGroup : ComGroup.
Proof.
  apply (mk_ComGroup Z_6 op_Z_6 inv_Z_6 n).
  induction a0, b0, c0; compute; auto.
  induction a0; compute; auto. 
  induction a0; compute; auto.
  intros a b.
  unfold op_Z_6, nat_mod_to_Z_6.
  destruct a, b; auto.
Defined.

Definition ComGroupMorphism (G:ComGroup) (H:ComGroup) (f:G->H) : Prop :=  
    f(z G)=z H /\
    forall a:G, f(inv G a)=inv H (f(a)) /\
    forall a b : G, f(op G a b) = op H (f(a)) (f(b)).


Definition Z_6_Z_3 : Z_6->Z_3 := 
  fun (x:Z_6) => match x with
  | n => n3
  | a => a3
  | b => b3
  | c => n3
  | d => a3
  | e => b3
  end.


Theorem h : ComGroupMorphism (Z_6_ComGroup) (Z_3_ComGroup) Z_6_Z_3.
Proof.
  unfold ComGroupMorphism.
  split.
  compute; auto.
  split.
  induction a0.
  all:compute; auto.
  induction a0, b0.
  all:induction a0.
  all:compute; auto.
Defined.


(*egyenlosege eldontheto*)
Definition eq_Z_6 (x y : Z_6) : bool :=
  match x, y with
  | n, n => true
  | a, a => true
  | b, b => true
  | c, c => true
  | d, d => true
  | e, e => true
  | _, _ => false
  end.
Theorem h_epimorphism : forall y : Z_3,
  exists x : Z_6, Z_6_Z_3  x = y.
Proof.
intros.
elim y.
exists n.
reflexivity.
exists a.
reflexivity.
exists b.
reflexivity.
Defined.



(*3*)


Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint subtract_from_list (l : list nat) (n : nat) : list (option nat) :=
  match l with
  | [] => []
  | x :: xs =>
    match Nat.sub n x with
    | 0 => None :: subtract_from_list xs n
    | result => Some result :: subtract_from_list xs n
    end
  end.



(*4*)


Fixpoint safe_subtract_chain (l : list nat) : option nat :=
  match l with
  | [] => Some 0
  | x :: xs =>
    match safe_subtract_chain xs with
    | Some result =>
      if x <=? result then Some (result - x)
      else None
    | None => None
    end
  end.


(*5,6*)


Class Conj_logic := mk_conj_logic {

  (*szort*)
  Fm : Set;

  (*műveletek*)
  Top : Fm;
  Pf : Fm -> Set;
  Cnj : Fm -> Fm -> Fm;
  TopInt : Pf Top;
  CnjInt : forall A B : Fm, Pf A -> Pf B -> Pf (Cnj A B);
  CnjEli : forall A B C : Fm, Pf (Cnj A B) -> (Pf A -> Pf B -> Pf C) ->
  Pf C;

  Imp : Fm -> Fm -> Fm;
  ImpInt : forall A B : Fm, (Pf A -> Pf B) -> Pf (Imp A B);
  ImpEli : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B;
  
  Dis : Fm -> Fm -> Fm;
  DisInt1 : forall A B : Fm,  Pf A -> Pf (Dis A B);
  DisInt2 : forall A B : Fm,  Pf B -> Pf (Dis A B);
  DisEli : forall A B C : Fm, Pf (Dis A B) -> (Pf A -> Pf C) -> (Pf B -> Pf C) -> Pf C;
}.

Infix "∧" := Cnj (at level 100, right associativity). 
Infix "→" := Imp (at level 90, right associativity). 
Infix "∨" := Dis (at level 80, right associativity). 

Context (CL : Conj_logic).


(*5*)


Lemma dist : forall A B C : Fm,  
          Pf ((A ∧ B) ∨ C) -> Pf ((A ∨ C) ∧ (B ∨ C)).
Proof.
  intros.
  apply DisEli with (A:=(A0 ∧ B)) (B:=C) (C:=(A0 ∨ C) ∧ (B ∨ C)).
  - auto.
  - intros.
    apply CnjEli with (A:=A0) (B:=B) (C:= (A0 ∨ C ∧ B ∨ C)).
    auto.
    intros.
    assert (K : Pf (A0 ∨ C)). { apply DisInt1. auto. }
    assert (L : Pf (B ∨ C)). { apply DisInt1. auto. }
    apply CnjInt; assumption.
  - intros.
    assert (K : Pf (A0 ∨ C)). { apply DisInt2. auto. }
    assert (L : Pf (B ∨ C)). { apply DisInt2. auto. }
    apply CnjInt; assumption.
Qed.



(*6*)



Lemma Currying : forall A B C : Fm,  
          Pf (A → B → C) -> Pf ((A ∧ B) → C).
Proof.
intros.
apply ImpInt.
intro.
apply CnjEli with (A := A0) (B := B) (C := C).
auto.
intros. 
assert (K : Pf (B → C)).
apply ImpEli with (A:=A0) (B:=(B → C)).
auto. auto. 
apply ImpEli with (A:=B) (B:=C).
auto. auto. 
Qed.
Lemma unCurrying : forall A B C : Fm,  
          Pf ((A ∧ B) → C) -> Pf (A → B → C).
Proof.
intros.
apply ImpInt.
intros.
apply ImpInt.
intros.
assert (K : Pf (A0 ∧ B)).
apply CnjInt.
all:auto.
apply (CnjEli A0 B C) in K.
apply K.
Admitted.
 (*elakadtam ennel*) 
