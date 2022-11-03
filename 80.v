(*Prove que |rev(l)| = |l|, qualquer que seja a lista l.*)

Require Import List.
Require Import Lia.

Fixpoint concat (l1 l2 : list nat) : list nat :=
  match l1 with
    | nil => l2
    | cons h l' => cons h (concat l' l2)
  end.

Fixpoint rev (l : list nat) : list nat :=
  match l with
    | nil => l
    | cons h l' => concat (rev l') (cons h nil)
  end.

Fixpoint len (l : list nat) : nat :=
  match l with
    | nil => 0
    | cons h l' => 1 + len l'
  end.

Lemma concat_nil_commutative: forall l : list nat, concat l nil = l.
Proof.
  induction l.
  - simpl concat.
    reflexivity.
  - simpl concat.
    rewrite IHl.
    reflexivity.
Qed.

Lemma concat_sum_len : forall l1 l2, len (concat l1 l2) = len l1 + len l2.
Proof.
  induction l1, l2.
  - simpl concat.
    simpl len.
    reflexivity.
  - simpl concat.
    simpl (len nil).
    reflexivity.
  - simpl (len nil).
    assert (concat l1 nil = l1).
    -- apply concat_nil_commutative.
    -- simpl concat.
       rewrite H.
       lia.
  - simpl len.
    rewrite IHl1.
    simpl len.
    reflexivity.
Qed.

Lemma reverse_list_size : forall l, len (rev l) = len l.
Proof.
  induction l.
  - simpl rev.
    reflexivity.
  - simpl rev.
    assert (len (concat (rev l) (a :: nil)) = len (rev l) + len (a :: nil)).
    -- apply concat_sum_len.
    -- rewrite H.
       rewrite IHl.
       simpl.
       lia.
Qed.
