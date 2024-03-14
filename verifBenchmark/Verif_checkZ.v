Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.checkZ.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*swap specification: (a[ind] == 122 || a[ind] == 90)
 weaker
*)
Definition checkZ_spec : ident * funspec :=
  DECLARE _checkZ
   WITH a: val, sh : share, ind : Z, length : Z, contents : list Z
   PRE [ tptr tint, tuint, tuint ]
    PROP  (readable_share sh; Zlength contents = length;
    0 <= length <= Int.max_unsigned; 0 <= ind <= length; 
    Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents(*;
    Forall (fun x => ~(x = 122) /\ ~(x = 90)) (sublist 0 (ind + 1) contents)*)
    )
    PARAMS (a; Vint(Int.repr ind); Vint (Int.repr length))
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
   POST [ tbool ]
    EX i : Z, EX b : bool,
    PROP (if (Z.eq_dec i length) then b = false else b = true) 
    RETURN (bool2val b)
    SEP(
      data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a
    ).

(*sorted - returns true*)
Definition Gprog := [checkZ_spec].

Lemma spec_proof: semax_body Vprog Gprog f_checkZ checkZ_spec.
Proof.
  start_function. forward_if. forward. Exists (Zlength contents). Exists false. entailer!!.  
  destruct (Z.eq_dec (Zlength contents) (Zlength contents)) eqn:Hedec. reflexivity. 
  unfold not in n. destruct n. reflexivity. forward. apply semax_if_seq. forward_if.
  forward. forward_if. forward. Exists ind. Exists true. destruct (Z.eq_dec ind (Zlength contents)) eqn:Hedec.
  unfold not in H3. destruct H3. assumption. entailer!. 
  forward_call. inversion H5. inversion H5.
  forward. forward. forward_if. forward. Exists ind. Exists true. destruct (Z.eq_dec ind (Zlength contents)) eqn:Hedec.
  unfold not in H3. destruct H3. assumption. entailer!. 
  forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret).
  entailer!!. destruct (Z.eq_dec (fst vret) (Zlength contents)) eqn:Hl. rewrite H6. 
  simpl. reflexivity.
  rewrite H6. simpl. reflexivity.
Qed.


