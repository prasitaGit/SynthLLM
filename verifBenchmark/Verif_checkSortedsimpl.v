Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.checkSorted.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*ii not required - weaker postc.*)
Definition checkSorted_spec : ident * funspec :=
  DECLARE _checkSorted
   WITH a: val, sh : share, ind : Z, length : Z, contents : list Z
   PRE [ tptr tint, tuint, tuint ]
    PROP  (readable_share sh; Zlength contents = length;
    0 <= length <= Int.max_signed;
    0 <= ind < length;
    Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS (a; Vint(Int.repr ind); Vint (Int.repr length))
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
   POST [ tbool ]
    EX i : Z, EX b : bool,
    PROP (if (Z.eq_dec i (length - 1)) then b = true else b = false)
    RETURN (bool2val b)
    SEP(
      data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a
    ).

(*sorted - returns true*)
Definition Gprog := [checkSorted_spec].

Lemma spec_proof: semax_body Vprog Gprog f_checkSorted checkSorted_spec.
Proof. (*map true to 1, false to 0*)
  start_function.
  forward_if. forward. Exists (Zlength contents - 1). Exists true. 
  destruct (Z.eq_dec (Zlength contents - 1) (Zlength contents - 1)) eqn:Hedec. entailer!.
  unfold not in n. destruct n; reflexivity.
  forward. rewrite sub_repr in H3. apply repr_neq_e in H3. 
  assert (ind + 1 < length) by lia. forward. forward_if. forward.
  Exists ind. Exists false. destruct (Z.eq_dec ind (Zlength contents - 1)) eqn:Hedec. 
  unfold not in H3; destruct H3; assumption. entailer!!. forward_call.
  lia. Intros vret. forward. 
  (*last part*)
  Exists (fst vret). Exists (snd vret). destruct (Z.eq_dec (fst vret) (Zlength contents - 1)) eqn:Hedec. 
  rewrite H6. entailer!!. rewrite H6. entailer!!.
Qed.




