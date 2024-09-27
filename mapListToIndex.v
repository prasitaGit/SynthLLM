Require Import VST.floyd.proofauto.


Fixpoint generate_list (n : nat) : list Z :=
  match n with
  | 0%nat => []
  | S n' => (Z.of_nat n') :: generate_list n'
  end.

Lemma generateListLengthN : forall n, Zlength (generate_list n) = Z.of_nat n. 
Proof.
  induction n; intros; simpl. list_solve. 
  list_solve.
Qed.

Lemma generateFirstN : forall n ind, 0 <= ind < Zlength (generate_list n)  -> Znth ind (generate_list n) = Zlength (generate_list n) - (ind + 1).
Proof.
  induction n; intros; simpl.  
  rewrite generateListLengthN in H. simpl in H. inversion H. assert (~ (ind < 0)) by lia. 
  contradiction. rewrite generateListLengthN in *. rewrite Zlength_cons. rewrite generateListLengthN. 
  destruct (ind =? 0) eqn:Hind. assert (ind = 0) by lia. subst.  list_solve. 
  assert (ind > 0) by lia.  rewrite Znth_pos_cons by lia. assert (0 <= ind - 1 < Z.of_nat n) by lia. 
  apply IHn with (ind - 1) in H1. rewrite H1. lia. 
Qed.  

Lemma generateFirstNNil: forall n, n = 0 -> generate_list (Z.to_nat n) = [].
Proof.
  intros. subst. simpl. reflexivity.
Qed.

Lemma generateFirstNSplit: forall n: nat, (n > 0)%nat-> generate_list n = [Z.of_nat (n - 1)] ++ (generate_list (n - 1)).
Proof.
  induction n; intros. 
  inversion H.  
  unfold generate_list; fold generate_list. destruct n eqn:Hnn. 
  simpl. list_solve. rewrite IHn at 1. replace (Z.of_nat (S (S n0) - 1)) with (Z.of_nat (S n0)) by lia. 
  simpl. f_equal. replace (n0 - 0)%nat with n0 by lia. reflexivity. lia.
Qed.