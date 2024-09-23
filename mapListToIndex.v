Require Import VST.floyd.proofauto.

Fixpoint generate_list (n : nat) : list Z :=
  match n with
  | 0%nat => [0]
  | S n' => generate_list n' ++ [Z.of_nat n]
  end.

Lemma generateListLengthN : forall n, Zlength (generate_list n) = Z.of_nat n + 1. 
Proof.
  induction n; intros; simpl. list_solve. 
  list_solve.
Qed.

Lemma generateFirstN : forall ind n, 0 <= ind < Zlength (generate_list n)  -> Znth ind (generate_list n) = ind.
Proof.
  induction n; intros; simpl.  
  rewrite generateListLengthN in H. simpl in H. assert (ind = 0) by lia. 
  list_solve. rewrite generateListLengthN in *.  rewrite Zpos_P_of_succ_nat.
  destruct (ind <=? Z.of_nat n) eqn:Hin. assert (ind <= Z.of_nat n) by lia. 
  rewrite Znth_app1. apply IHn. lia. rewrite generateListLengthN. lia. 
  assert (ind = Z.of_nat (S n)) by lia. rewrite Znth_app2. rewrite generateListLengthN. 
  rewrite H0. rewrite Nat2Z.inj_succ. list_solve. rewrite generateListLengthN. lia.
Qed.  