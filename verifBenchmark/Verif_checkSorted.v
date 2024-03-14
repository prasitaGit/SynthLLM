Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.checkSorted.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition sorted l := forall x y : Z, 0 <= y < (Zlength l) -> 0 <= x <= y -> (Znth x l <= Znth y l).

Lemma sorted_app : forall l i j, 0 <= j <= (Zlength l) -> 0 <= i < j ->
sorted (sublist 0 i l ++ sublist i j l) <-> sorted (sublist 0 (i + 1) l) /\ sorted (sublist i j l).
Proof.
  intros; split. intros.
  rewrite <- sublist_split in H1. 
  unfold sorted in H1. split. 
  unfold sorted. rewrite Zlength_sublist by lia. replace (i + 1 - 0) with (i + 1) by lia. 
  rewrite Zlength_sublist in H1 by lia. replace (j - 0) with j in H1 by lia. 
  intros.  rewrite Znth_sublist by lia. rewrite Znth_sublist by lia. 
  specialize H1 with x y. rewrite Znth_sublist in H1 by lia. rewrite Znth_sublist in H1 by lia. 
  apply H1; try lia. 
  (*second case*)
  unfold sorted. intros. rewrite Zlength_sublist in H2 by lia. rewrite Znth_sublist by lia.
  rewrite Znth_sublist by lia. rewrite Zlength_sublist in H1 by lia. replace (j - 0) with j in H1 by lia. 
  specialize H1 with (x + i) (y + i). rewrite Znth_sublist in H1 by lia.  rewrite Znth_sublist in H1 by lia.  
  replace (x + i + 0) with (x + i) in H1 by lia. replace (y + i + 0) with (y + i) in H1 by lia.
  apply H1. lia. lia. lia. lia. intros. destruct H1 as [? ?].
  (*other side*)
  rewrite <- sublist_split by lia. unfold sorted. rewrite Zlength_sublist by lia. 
  replace (j - 0) with j by lia. intros.  rewrite sublist_split with 0 i j l by lia. 
  destruct (y <? i) eqn:Hy. assert (y < i) by lia. assert (x < i) by lia. 
  rewrite Znth_app1. rewrite Znth_app1. unfold sorted in H1. specialize H1 with x y.
  rewrite Zlength_sublist in H1 by lia. replace (i - 0) with i in H1 by lia. 
  rewrite Znth_sublist in H1 by lia. rewrite Znth_sublist in H1 by lia. 
  rewrite Znth_sublist by lia. rewrite Znth_sublist by lia. 
  apply H1; lia. rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia. 
  assert (y >= i) by lia.  destruct (x >=? i) eqn:Hxi. assert (x >= i) by lia. 
  rewrite <- sublist_split. rewrite Znth_sublist by lia. rewrite Znth_sublist by lia.
  replace (x + 0) with x by lia. replace (y + 0) with y by lia. 
  unfold sorted in H2. specialize H2 with (x - i) (y - i). rewrite Zlength_sublist in H2 by lia. 
  rewrite Znth_sublist in H2 by lia. rewrite Znth_sublist in H2 by lia.
  replace (x - i + i) with x in H2 by lia. replace (y - i + i) with y in H2 by lia. 
  apply H2; try lia. lia. lia. 
  (*most difficult part?*) 
  assert (x < i) by lia. 
  (*i - 1, i ?*)
  rewrite Znth_app1. rewrite Znth_app2. rewrite Zlength_sublist by lia. 
  replace (i - 0) with i by lia. rewrite Znth_sublist by lia. rewrite Znth_sublist by lia. 
  replace (x + 0) with x by lia. replace (y - i + i) with y by lia.
  assert (Znth x l <= Znth i l). {
    unfold sorted in H1. specialize H1 with x i. rewrite Zlength_sublist in H1 by lia. 
    rewrite Znth_sublist in H1 by lia. rewrite Znth_sublist in H1 by lia. 
    replace (x + 0) with x in H1 by lia. replace (i + 0) with i in H1 by lia. 
    apply H1; try lia.
  }
  assert (Znth i l <= Znth y l). {
    unfold sorted in H2. specialize H2 with 0 (y - i). rewrite Zlength_sublist in H2 by lia. 
    rewrite Znth_sublist in H2 by lia. rewrite Znth_sublist in H2 by lia. 
    replace (0 + i) with i in H2 by lia. replace (y - i + i) with y in H2 by lia. 
    apply H2; try lia.
  }
  lia. rewrite Zlength_sublist by lia. lia. rewrite Zlength_sublist by lia. lia.
Qed. 



(*full functional correctness - requires ii*)
Definition checkSorted_spec : ident * funspec :=
  DECLARE _checkSorted
   WITH a: val, sh : share, ind : Z, length : Z, contents : list Z
   PRE [ tptr tint, tuint, tuint ]
    PROP  (readable_share sh; Zlength contents = length;
    0 <= length <= Int.max_signed;
    0 <= ind < length; (sorted (sublist 0 (ind + 1) contents));
    Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS (a; Vint(Int.repr ind); Vint (Int.repr length))
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
   POST [ tbool ]
    EX b : bool,
    PROP ((sorted contents) -> b = true )(*else b = false) *)
    RETURN (bool2val b)
    SEP(
      data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a
    ).

(*sorted - returns true*)
Definition Gprog := [checkSorted_spec].

Lemma spec_proof: semax_body Vprog Gprog f_checkSorted checkSorted_spec.
Proof. (*map true to 1, false to 0*)
  start_function.
  forward_if. forward. entailer!. apply repr_inj_signed in H4. 
  rewrite H4 in H2. replace (Zlength contents - 1 + 1) with (Zlength contents) in H2 by lia. 
  rewrite sublist_same in H2 by lia. 
  (*rewrite <- simplify_bool2val_case1. *)     
  Exists true. entailer!. destruct H0, H1.  
  unfold repable_signed; split.  assert (0 >= Int.min_signed). {
    compute. intros. discriminate H9.
  }
  (*Int.min_signed <= 0 && 0 <= ind -> *)
  apply Z.ge_le in H9. lia. lia. unfold repable_signed. split. destruct H0.
  assert (-1 <= Zlength contents - 1) by lia. 
  assert (Int.min_signed <= -1). { compute. intros. discriminate H9. }
  lia. lia. forward. 
  assert (0 <= ind + 1 < Zlength (map Int.repr contents)). {
    rewrite <- H in H1. destruct H1. split. lia.  rewrite sub_repr in H4. 
    apply repr_neq_e in H4. rewrite Zlength_map. lia.
  }
  assert (0 <= ind + 1 < Zlength contents). { rewrite Zlength_map in H5. assumption. }
  forward. forward_if. forward. do 2 rewrite Int.signed_repr in H7.   
  Exists false. entailer!. unfold sorted in H10. specialize H10 with ind (ind + 1).
  apply H10 in H6. assert (0 <= ind <= ind + 1) by lia. apply H10 in H11. 
  apply Z.le_ge in H11. contradiction. lia. lia.
  (*Forall_forall*)
  rewrite Forall_forall in H3. apply H3.  apply Znth_In. assumption.
  rewrite Forall_forall in H3. apply H3.  apply Znth_In. assumption.
  rewrite Forall_forall in H3. apply H3.  apply Znth_In. assumption.
  forward_call. split. lia. 
  (*sorted part proof*)
  replace (ind + 1 + 1) with (ind + 2) by lia. 
  rewrite sublist_split with 0 ind (ind + 2) contents by lia. 
  apply sorted_app. lia. lia.   split; try assumption. replace (sublist ind (ind + 2) contents) with (Znth ind contents :: [Znth (ind + 1) contents]) by list_solve.
  unfold sorted. do 2 rewrite Int.signed_repr in H7. replace (Zlength [Znth ind contents; Znth (ind + 1) contents]) with 2 by list_solve.
  intros. destruct (x =? y) eqn:Hxeq. assert (x = y) by lia; subst. lia. 
  assert (x < y) by lia. assert (y = 1) by lia. assert (x = 0) by lia.  subst.
  list_solve. rewrite Forall_forall in H3; apply H3; apply Znth_In. lia. 
  rewrite Forall_forall in H3; apply H3; apply Znth_In. lia. 
  rewrite Forall_forall in H3; apply H3; apply Znth_In. lia. 
  Intros vret. forward.
  Exists vret. entailer!!. destruct vret eqn:Hvret. 
  simpl. try reflexivity.
  simpl. try reflexivity.
Qed.




