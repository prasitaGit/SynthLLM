Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.isOddAtIndexOdd.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
(*checking that ith index is odd*)
Definition isOddAtIndexOdd_spec : ident * funspec :=
    DECLARE _isOddAtIndexOdd
      WITH a : val, sh : share, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tbool ]
        EX i : Z,EX b : bool,
        PROP (if (i =? length) then b = true else b = false) 
        RETURN (bool2val b)
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*odd at odd places - returns true*)
Definition Gprog := [ isOddAtIndexOdd_spec].

Lemma spec_proof: semax_body Vprog Gprog f_isOddAtIndexOdd isOddAtIndexOdd_spec.
Proof. 
  start_function. forward_if. forward. Exists (Zlength contents). rewrite Z.eqb_refl. 
  Exists true. entailer!!. assert (ind < length) by lia. apply semax_if_seq. 
  forward_if. forward. forward. entailer!. destruct H8 as [? ?]. inversion H9. 
  forward_if. forward. Exists ind. Exists false. apply Z.eqb_neq in H3. rewrite H3. entailer!!.
  forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret). 
  destruct (fst vret =? Zlength contents) eqn:Heq. rewrite H7. entailer!!. rewrite H7. entailer!!. 
  forward. forward_if. unfold not in H6'. destruct H6'. reflexivity. forward_call. lia.
  Intros vret. forward. Exists (fst vret). Exists (snd vret). 
  destruct (fst vret =? Zlength contents) eqn:Heq. rewrite H7. entailer!!. rewrite H7. entailer!!. 
Qed.




