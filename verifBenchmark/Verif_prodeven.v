Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.prodeven.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition mul_Z : list Z -> Z := fold_right Z.mul 1.

Lemma all_odd : forall l, Zodd (mul_Z l) <-> Forall (fun x => Zodd x) l. 
Proof.
  induction l. simpl. split. intros. apply Forall_nil. auto. 
  split. intros. (*apply Forall_cons.*) unfold mul_Z in H. 
  rewrite fold_right_cons in H. 
  apply Zodd_bool_iff in H. rewrite Z.odd_mul in H.
  apply andb_true_iff in H. destruct H as [? ?].
  apply Zodd_bool_iff in H,H0. apply Forall_cons. assumption. apply IHl. unfold mul_Z. assumption.
  intros. unfold mul_Z. rewrite fold_right_cons.
  apply Zodd_bool_iff. rewrite Z.odd_mul. apply andb_true_iff. split. 
  apply Zodd_bool_iff. apply Forall_inv in H. assumption. apply Forall_inv_tail in H.
  apply IHl in H. apply Zodd_bool_iff. unfold mul_Z in H. assumption.
Qed.

Lemma one_even : forall l, Zeven (mul_Z l) <-> Exists (fun x => Zeven x) l. 
Proof.
  induction l. simpl. split. intros. inversion H. 
  intros. inversion H. 
  split. intros. unfold mul_Z in H. rewrite fold_right_cons in H. 
  apply Zeven_bool_iff in H.
  rewrite Z.even_mul in H. apply orb_prop in H. 
  destruct H. apply Exists_cons_hd. apply Zeven_bool_iff in H. assumption.
  apply Exists_cons_tl. apply IHl. unfold mul_Z. apply Zeven_bool_iff in H. assumption.
  intros. apply Exists_cons in H. destruct H. unfold mul_Z. rewrite fold_right_cons. apply Zeven_bool_iff.
  rewrite Z.even_mul. apply orb_true_iff. left. apply Zeven_bool_iff. assumption.
  unfold mul_Z. rewrite fold_right_cons. apply Zeven_bool_iff.
  rewrite Z.even_mul. apply orb_true_iff. right. apply Zeven_bool_iff. 
  unfold mul_Z in IHl. apply IHl. assumption.
Qed.

Lemma fold_rightmul : forall (l : list Z) (a : Z), (fold_right Z.mul 1 l) * a =  fold_right Z.mul a l.
Proof.
  induction l. simpl. lia. 
  intros.  do 2 rewrite fold_right_cons. specialize IHl with a0. 
  rewrite <- IHl.  rewrite Z.mul_assoc. reflexivity.
Qed.
(*product of the all numbers in an array - if even, return 0*)
Definition prodeven_spec : ident * funspec :=
    DECLARE _prodeven
      WITH a : val, sh : share, prodn : Z, ind : Z, length : Z, contents : list Z
       PRE [ tptr tuint, tuint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        0 <= prodn <= Int.max_unsigned;
        prodn = mul_Z (sublist 0 ind contents);
        Forall (fun x => 0 <= x <= Int.max_unsigned) contents;
        (*Forall (fun x => 0 <= prodn * x <= Int.max_unsigned) contents;*)
        forall i : Z, 0 <= i <= length -> 0 <= mul_Z (sublist 0 i contents) <= Int.max_unsigned;
        (*0 <= mul_Z contents <= Int.max_unsigned; *) 0 <= Z.modulo (mul_Z contents) 2 <= Int.max_unsigned)
        PARAMS (a; Vint (Int.repr prodn); Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tuint length) (map Vint (map Int.repr contents)) a)
       POST [ tbool ]
        EX bret : bool,
        (*if there exists one even element, then the product is even*)
        PROP (Exists (fun x => Zeven x) contents -> bret = true )
        RETURN (bool2val bret)
        SEP(data_at sh (tarray tuint length) (map Vint (map Int.repr contents)) a).

(*blah*)
Definition Gprog := [ prodeven_spec].

Lemma spec_proof: semax_body Vprog Gprog f_prodeven prodeven_spec.
Proof.
  start_function. forward_if. forward_if. forward. rewrite sublist_same in H8 by lia.
  apply repr_inj_unsigned in H8. 2:{ lia. } 2:{ lia. }
  Exists true. entailer!!. forward. apply repr_neq_e in H8. 
  Exists false. entailer!!. rewrite Zmod_odd in H8. 
  destruct (Z.odd (mul_Z (sublist 0 (Zlength contents) contents))) eqn:Hzodd. 
  apply Zodd_bool_iff in Hzodd. unfold mul_Z in Hzodd. 
  rewrite sublist_same in Hzodd by lia. apply all_odd in Hzodd. 
  apply Exists_exists in H3. 
  inversion H3; subst. destruct H7 as [? ?]. rewrite Forall_forall in Hzodd. 
  specialize Hzodd with x. apply Hzodd in H7. apply Zodd_not_Zeven in H7. contradiction.
  contradiction. assert (ind < length) by lia. forward. forward_call. split; try lia. 
  split. rewrite Int.unsigned_repr. rewrite H3. 
  split. apply Z.mul_nonneg_nonneg. lia. rewrite Forall_forall in H4. 
  assert (In (Znth ind contents) contents). { apply Znth_In. lia. }
  apply H4 in H9. lia. assert (0 <= ind + 1 <= length ) by lia. specialize H5 with (ind + 1).
  apply H5 in H9. rewrite sublist_split with 0 ind (ind + 1) contents in H9 by lia. 
  unfold mul_Z in H9. rewrite fold_right_app in H9. rewrite sublist_one in H9 by lia. 
  simpl in H9. replace (Znth ind contents * 1) with (Znth ind contents) in H9 by lia. 
  unfold mul_Z. rewrite fold_rightmul. lia.   
  rewrite Forall_forall in H4. apply H4. apply Znth_In. lia. 
  rewrite Int.unsigned_repr. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
  unfold mul_Z. rewrite fold_right_app. rewrite sublist_one by lia. simpl. 
  replace (Znth ind contents * 1) with (Znth ind contents) by lia. rewrite H3. 
  unfold mul_Z. rewrite fold_rightmul. reflexivity.
  rewrite Forall_forall in H4. apply H4. apply Znth_In; lia. 
  Intros vret. forward.
  destruct (Z.even (mul_Z contents)) eqn:Hev. destruct H9. apply Zeven_bool_iff in Hev. 
  apply one_even. assumption. destruct vret eqn:Hv. Exists true. entailer!!.
  Exists false. entailer!!. assert (~ Zeven (mul_Z contents)). {
     unfold not. intros. apply Zeven_bool_iff in H3. rewrite H3 in Hev. 
     discriminate Hev.
  }
  destruct vret eqn:Her. Exists true. entailer!!. 
  Exists false. entailer!!.
Qed.


