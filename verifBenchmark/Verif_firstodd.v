Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.firstodd.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
(*checking that ith index is odd*)
Definition firstoddIndex_spec : ident * funspec :=
    DECLARE _firstoddIndex
      WITH a : val, sh : share, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
        EX i : Z,EX tind : Z,
        PROP (if (Z.eq_dec tind length) then i = -1 else i = tind) 
        RETURN (Vint (Int.repr i))
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*sorted - returns true*)
Definition Gprog := [ firstoddIndex_spec].

Lemma spec_proof: semax_body Vprog Gprog f_firstoddIndex firstoddIndex_spec.
Proof. 
  start_function. forward_if. forward. Exists (-1). Exists (Zlength contents). entailer!!.
  destruct (Z.eq_dec (Zlength contents) (Zlength contents)) eqn:Heqdec. reflexivity. 
  unfold not in n. destruct n. reflexivity.
  forward. forward_if. entailer!!. destruct H7 as [? ?]. inversion H8. 
  forward. Exists ind. Exists ind. entailer!!.  destruct (Z.eq_dec ind (Zlength contents)) eqn:Heqdec. 
  unfold not in H3. destruct H3. assumption. reflexivity.
  forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret).
  destruct (Z.eq_dec (snd vret) (Zlength contents)) eqn:Heqdec. entailer!!. entailer!!.
Qed.




