Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.nIsGreater.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Check if index equals length*)
Definition checkGreaterthanAll_spec : ident * funspec :=
    DECLARE _checkGreaterthanAll
      WITH a : val, sh : share, n : Z, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind <= length; 
        Int.min_signed <= n <= Int.max_signed;
        Forall (fun x =>  Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr n); Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tbool ]
        EX tind: Z, EX bret : bool,
        PROP (if (Z.eq_dec tind length) then bret = true else bret = false)
        RETURN (bool2val bret)
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*sorted - returns true*)
Definition Gprog := [ checkGreaterthanAll_spec].

Lemma spec_proof: semax_body Vprog Gprog f_checkGreaterthanAll checkGreaterthanAll_spec.
Proof.
  start_function. forward_if. forward. Exists (Zlength contents). Exists true.
  destruct (Z.eq_dec (Zlength contents) (Zlength contents)) eqn:Heqdec. entailer!!. 
  unfold not in n0. destruct n0. reflexivity.
  assert (ind < length) by lia. forward. forward_if. forward. 
  Exists ind. Exists false. destruct (Z.eq_dec ind (Zlength contents)) eqn:Heqdec. contradiction.
  entailer!!. forward_call. lia. 
  Intros vret. forward. Exists (fst vret). Exists (snd vret). 
  destruct (Z.eq_dec (fst vret) (Zlength contents)) eqn:Heq_dec; subst; entailer!!.
  rewrite H7. simpl. reflexivity. rewrite H7. simpl. reflexivity.
Qed.


