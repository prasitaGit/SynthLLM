Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.diffMinMax.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
(*as of now - full functional*)
Definition diffMinMax_spec : ident * funspec :=
    DECLARE _diffMinMax
      WITH a : val, sh : share, min : Z, max : Z, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tint, tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        1 <= length <= Int.max_unsigned; 1 <= ind <= length;
        Int.min_signed <= min <= Int.max_signed;
        Int.min_signed <= max <= Int.max_signed;
        0 <= max - min <= Int.max_signed;
        Forall (fun x => min <= x) (sublist 0 ind contents);
        Forall (fun x => max >= x) (sublist 0 ind contents);
        forall x y : Z, 0 <= x < length -> 0 <= y < length -> Int.min_signed <= (Znth x contents - Znth y contents) <= Int.max_signed;
        forall x y : Z, 0 <= x < ind -> 0 <= y < ind -> (max - min) >= (Znth x contents - Znth y contents);
        Exists (fun x => x = max) (sublist 0 ind contents);
        Exists (fun x => x = min) (sublist 0 ind contents);
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint(Int.repr min); Vint(Int.repr max); 
        Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
        EX i : Z,
        PROP (forall x y : Z, 0 <= x < length -> 0 <= y < length -> i >= (Znth x contents - Znth y contents)) 
        RETURN (Vint (Int.repr i))
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [ diffMinMax_spec].

Lemma spec_proof: semax_body Vprog Gprog f_diffMinMax diffMinMax_spec.
Proof.
  start_function. 
  forward_if. forward. Exists (max - min). entailer!!. 
  forward. apply semax_if_seq. forward_if. forward. forward.
  apply semax_if_seq. forward_if. forward. forward_call.
  rewrite Int.signed_repr in H13. assert (max - min < 0) by lia. destruct H4.
  apply Z.le_ge in H4. contradiction.
  rewrite Forall_forall in H11. apply H11. apply Znth_In. lia.
  (*again contradiction*)
  rewrite Int.signed_repr in H13. assert (max - min < 0) by lia. destruct H4.
  apply Z.le_ge in H4. contradiction. 
  rewrite Forall_forall in H11. apply H11. apply Znth_In. lia.
  forward_call. split. lia. split. rewrite Forall_forall in H11. apply H11. apply Znth_In. lia.
  rewrite Int.signed_repr in H13, H14. split. (*invert Exists of max*)
  apply Exists_exists in H9. inversion H9. destruct H15 as [? ?]; subst. 
  Search In Znth. apply In_Znth in H15. inversion H15; subst. rewrite Zlength_sublist in H by lia. 
  replace (ind - 0) with ind in H by lia. destruct H as [? ?]. Search Znth sublist.
  rewrite Znth_sublist in H16 by lia. replace (x + 0) with x in H16 by lia. rewrite <- H16. 
  specialize H7 with x ind. lia. split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
  Search Forall app. apply Forall_app; split. rewrite Forall_forall in H5 by lia. 
  rewrite Forall_forall by lia. intros. specialize H5 with x. apply H5 in H15. lia. 
  Search sublist Znth. rewrite sublist_one by lia. rewrite Forall_forall by lia. 
  intros. inversion H15; subst. lia. contradiction. 
  split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
  apply Forall_app; split. rewrite Forall_forall in H6 by lia. 
  rewrite Forall_forall by lia. intros. specialize H6 with x. apply H6 in H15. lia. 
  rewrite sublist_one by lia. rewrite Forall_forall by lia. 
  intros. inversion H15; subst. lia. contradiction. split.
  (*eleminate trivial case: when max = Znth ind contents*)
  destruct (max =? Znth ind contents) eqn:Hmax. assert (max = Znth ind contents) by lia. 
  rewrite <- H15 in H13. assert (max - min < 0) by lia. destruct H4. apply Z.le_ge in H4. contradiction.
  assert (max > Znth ind contents) by lia.  intros. 
  destruct (x =? ind) eqn:Hxind, (y =? ind) eqn:Hyind. assert (x = ind) by lia; subst. 
  assert (y = ind) by lia; subst. lia. 
  assert (x = ind) by lia; subst. assert (y < ind) by lia. (*H6*)
  apply Exists_exists in H9. inversion H9. destruct H18 as [? ?]; subst. 
  apply In_Znth in H18. inversion H18; subst. destruct H19 as [? ?].
  rewrite Zlength_sublist in H19 by lia.  replace (ind - 0) with ind in H19 by lia. 
  rewrite Znth_sublist in H20 by lia. replace (x + 0) with x in H20 by lia. subst. 
  specialize H8 with x y. (*min <= znth y contens; min > Znth ind contents*)
  assert (0 <= y < ind) by lia. apply H8 in H20; try assumption.  assert (min <= Znth y contents) by lia.
  move H13 after H21. lia. assert (x < ind) by lia. assert (y  = ind) by lia; subst.
  Search (_ - _). apply Z.le_ge. apply Z.sub_le_mono_r. apply Z.ge_le. rewrite Forall_forall in H6.
  apply H6. apply In_Znth_iff. exists x. split. rewrite Zlength_sublist by lia. lia. 
  rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity. 
  assert (x < ind) by lia. assert (y < ind) by lia. assert (max - Znth ind contents > 0) by lia. 
  destruct (Znth x contents =? Znth y contents) eqn:Hxy. assert (Znth x contents = Znth y contents) by lia; subst. lia. 
  destruct (Znth x contents <? Znth y contents) eqn:Hxly. assert (Znth x contents < Znth y contents) by lia. lia. 
  assert (Znth x contents > Znth y contents) by lia. 
  assert (Znth y contents >= min). {
    apply Z.le_ge. rewrite Forall_forall in H5. apply H5. 
    Search In Znth. apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  } 
  assert (Znth y contents > Znth ind contents) by lia.
  assert (max >= Znth x contents). {
    rewrite Forall_forall in H6. apply H6. 
    apply In_Znth_iff. exists x. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity.
  }
 lia. split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
 Search Exists app. apply Exists_app. left. assumption.
 rewrite sublist_split with 0 ind (ind + 1) contents by lia. apply Exists_app. right. 
 rewrite sublist_one by lia. auto. 
 rewrite Forall_forall in H11; apply H11; apply Znth_In. lia.
 rewrite Forall_forall in H11; apply H11; apply Znth_In. lia.
 (*next one*)
 Intros vret. forward. Exists vret. entailer!!. 
 (*last?*)
 forward. apply semax_if_seq. forward_if. forward. forward_call.
 rewrite Int.signed_repr in H13, H14.
  split. lia. split. rewrite Forall_forall in H11. apply H11. apply Znth_In. lia.
  split. (*invert Exists of min*)
  apply Exists_exists in H10. inversion H10. destruct H15 as [? ?]; subst. 
  apply In_Znth in H15. inversion H15; subst. rewrite Zlength_sublist in H by lia. 
  replace (ind - 0) with ind in H by lia. destruct H as [? ?]. 
  rewrite Znth_sublist in H16 by lia. replace (x + 0) with x in H16 by lia. rewrite <- H16. 
  specialize H7 with ind x. lia. split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
  apply Forall_app; split. rewrite Forall_forall in H5 by lia. 
  rewrite Forall_forall by lia. intros. specialize H5 with x. apply H5 in H15. lia. 
  rewrite sublist_one by lia. rewrite Forall_forall by lia. 
  intros. inversion H15; subst. lia. contradiction. 
  split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
  apply Forall_app; split. rewrite Forall_forall in H6 by lia. 
  rewrite Forall_forall by lia. intros. specialize H6 with x. apply H6 in H15. lia. 
  rewrite sublist_one by lia. rewrite Forall_forall by lia. 
  intros. inversion H15; subst. lia. contradiction. split.
  (*eleminate trivial case: when max = Znth ind contents*)
  destruct (min =? Znth ind contents) eqn:Hmin. assert (min = Znth ind contents) by lia. 
  rewrite <- H15 in H14. assert (max - min < 0) by lia. destruct H4. apply Z.le_ge in H4. contradiction.
  assert (min < Znth ind contents) by lia. intros. 
  destruct (x =? ind) eqn:Hxind, (y =? ind) eqn:Hyind. assert (x = ind) by lia; subst. 
  assert (y = ind) by lia; subst. lia. 
  assert (x = ind) by lia; subst. assert (y < ind) by lia. (*H6*)
  apply Z.le_ge. Search (_ - _). apply Z.sub_le_mono_l. rewrite Forall_forall in H5.
  apply H5. apply In_Znth_iff. exists y. split. rewrite Zlength_sublist by lia. lia. 
  rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  assert (x < ind) by lia. assert (y  = ind) by lia; subst. 
  assert (max >= Znth x contents). { rewrite Forall_forall in H6. apply H6. 
  apply In_Znth_iff. exists x. split. rewrite Zlength_sublist by lia. lia. 
  rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity.
  }
  lia. assert (x < ind) by lia. assert (y < ind) by lia. 
  assert (Znth y contents >= min). {
    apply Z.le_ge. rewrite Forall_forall in H5. apply H5. 
    apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  } 
  (*assert (Znth y contents < Znth ind contents) by lia.*)
  assert (max >= Znth x contents). {
    rewrite Forall_forall in H6. apply H6. 
    apply In_Znth_iff. exists x. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity.
  }
  assert (Znth x contents < Znth ind contents) by lia. lia.
 split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
  apply Exists_app. right. rewrite sublist_one by lia. auto. 
 rewrite sublist_split with 0 ind (ind + 1) contents by lia. apply Exists_app. left. assumption. 
 rewrite Forall_forall in H11; apply H11; apply Znth_In. lia.
 rewrite Forall_forall in H11; apply H11; apply Znth_In. lia.
 Intros vret. forward. Exists vret. entailer!!. forward_call.
 split. lia. split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
 apply Forall_app. split. assumption. rewrite sublist_one by lia. rewrite Forall_forall. 
 intros. inversion H15; subst. rewrite Int.signed_repr in H13. lia. 
 rewrite Forall_forall in H11; apply H11; apply Znth_In. lia. contradiction. 
 split. rewrite sublist_split with 0 ind (ind + 1) contents by lia. 
 apply Forall_app. split. assumption. rewrite sublist_one by lia. rewrite Forall_forall. 
 intros. inversion H15; subst. rewrite Int.signed_repr in H14. lia. 
 rewrite Forall_forall in H11; apply H11; apply Znth_In. lia. contradiction.
 rewrite Int.signed_repr in H13, H14. split. intros. assert (max - min >= 0) by lia.
 destruct (x <? ind) eqn:Hxind, (y <? ind) eqn:Hyind. assert (x < ind) by lia. assert (y < ind) by lia. 
 apply H8. lia. lia. assert (y = ind) by lia; subst.  assert (x < ind) by lia.
 destruct (max - min =? 0) eqn:Hmaxmin. assert (max = min) by lia. 
 assert (max = Znth ind contents) by lia. assert (min = Znth ind contents) by lia. subst. 
 replace (Znth ind contents - Znth ind contents) with 0 by lia. 
 assert (Znth ind contents >= Znth x contents ). { 
  rewrite Forall_forall in H6. apply H6. apply In_Znth_iff. exists x. 
  rewrite Zlength_sublist by lia. split. lia. rewrite Znth_sublist by lia. 
  replace (x + 0) with x by lia. reflexivity. } lia. 
  assert (max > min) by lia. destruct (min =? Znth ind contents) eqn:Hmin. 
  assert (min = Znth ind contents) by lia; subst. apply Z.le_ge. apply Z.sub_le_mono_r.
  apply Z.ge_le. rewrite Forall_forall in H6. apply H6. apply In_Znth_iff. exists x. rewrite Zlength_sublist by lia. 
  split. lia. rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity.
  assert (min < Znth ind contents) by lia.  destruct (max =? Znth ind contents) eqn:Hmaxc.
  assert (max = Znth ind contents) by lia; subst. 
  assert (Znth ind contents >= Znth x contents). { rewrite Forall_forall in H6. apply H6. apply In_Znth_iff. exists x. rewrite Zlength_sublist by lia. 
  split. lia. rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity. } lia. 
  assert (max > Znth ind contents) by lia. 
  assert (min <= Znth x contents). {
   rewrite Forall_forall in H5. apply H5. apply In_Znth_iff. exists x. rewrite Zlength_sublist by lia. 
   split. lia. rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity.
  }
  assert (max >= Znth x contents). {
    rewrite Forall_forall in H6. apply H6. apply In_Znth_iff. exists x. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (x + 0) with x by lia. reflexivity.
  } lia.
  assert (x = ind) by lia; subst. assert (y < ind) by lia. 
  destruct (max =? min) eqn:Hmaxmin. assert (max = min) by lia. subst. 
  assert (min = Znth ind contents) by lia; subst. replace (Znth ind contents - Znth ind contents) with 0 by lia. 
  assert (Znth ind contents <= Znth y contents). {
   rewrite Forall_forall in H5. apply H5. apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
   split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  }
  assert (Znth ind contents >= Znth y contents). {
    rewrite Forall_forall in H6. apply H6. apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  } lia.
  assert (max > min) by lia. destruct (max =? Znth ind contents) eqn:Hmax. assert (max = Znth ind contents) by lia; subst. 
  apply Z.le_ge. apply Z.sub_le_mono_l. rewrite Forall_forall in H5. apply H5. 
  apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
  split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  assert (max > Znth ind contents) by lia. destruct (min =? Znth ind contents) eqn:Hmmin. 
  assert (min = Znth ind contents) by lia; subst. 
  assert (Znth ind contents <= Znth y contents). {
   rewrite Forall_forall in H5. apply H5. apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
   split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  } lia. 
  assert (min < Znth ind contents) by lia.
  assert (min <= Znth y contents). {
   rewrite Forall_forall in H5. apply H5. apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
   split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  }
  assert (max >= Znth y contents). {
    rewrite Forall_forall in H6. apply H6. apply In_Znth_iff. exists y. rewrite Zlength_sublist by lia. 
    split. lia. rewrite Znth_sublist by lia. replace (y + 0) with y by lia. reflexivity.
  } lia.
  assert (x = ind) by lia; subst. assert (y = ind) by lia; subst. lia. split.
  rewrite sublist_split with 0 ind (ind + 1) contents by lia. apply Exists_app. left. assumption.
  rewrite sublist_split with 0 ind (ind + 1) contents by lia. apply Exists_app. left. assumption.
  rewrite Forall_forall in H11; apply H11; apply Znth_In. lia.
  rewrite Forall_forall in H11; apply H11; apply Znth_In. lia.
  Intros vret. forward. Exists vret. entailer!!.
Qed.




