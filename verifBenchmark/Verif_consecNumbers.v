Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.containsConsecutiveNumbers.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*consecutive specification - weaker*)
Definition containsConsecutiveNumbers_spec : ident * funspec :=
  DECLARE _containsConsecutiveNumbers
    WITH a: val, sh : share, ind : Z, length : Z, contents : list Z
     PRE [ tptr tint, tuint, tuint ]
     PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind < length;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
        Forall (fun x => Int.min_signed <= x + 1 <= Int.max_signed) contents)
     PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
     SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
     POST [ tbool ]
     EX i : Z, EX bret : bool,
     PROP (if (Z.eq_dec i (length - 1)) then bret = false else bret = true) 
     RETURN (bool2val bret) 
     SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [containsConsecutiveNumbers_spec].

Lemma spec_proof: semax_body Vprog Gprog f_containsConsecutiveNumbers containsConsecutiveNumbers_spec.
Proof. (*map true to 1, false to 0*)
  start_function.
  forward_if. forward. Exists (Zlength contents - 1). Exists false. 
  destruct (Z.eq_dec (Zlength contents - 1) (Zlength contents - 1)) eqn:Hedec. entailer!.
  unfold not in n. destruct n; reflexivity.
  forward. rewrite sub_repr in H4. apply repr_neq_e in H4. 
  assert (ind + 1 < length) by lia. forward. forward_if. rewrite Int.signed_repr.
  rewrite Int.signed_repr. entailer!!. rewrite Forall_forall in H3. apply H3. apply Znth_In. lia. 
  compute. split. intros. discriminate H9. intros. discriminate H9.
  rewrite Forall_forall in H2. apply H2. apply Znth_In. lia. 
  forward. Exists ind. Exists true. destruct (Z.eq_dec ind (Zlength contents - 1)) eqn:Hdec.
  unfold not in H4. destruct H4. assumption. entailer!!. 
  forward_call. lia.  Intros vret. forward. 
  (*last part*)
  Exists (fst vret). Exists (snd vret). destruct (Z.eq_dec (fst vret) (Zlength contents - 1)) eqn:Hedec. 
  rewrite H7. entailer!!. rewrite H7. entailer!!.
Qed.



