Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.allNumsSame.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Check if index equals length*)
Definition allNumsSame_spec : ident * funspec :=
    DECLARE _allNumsSame
      WITH a : val, sh : share, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind < length; 
        Forall (fun x =>  Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tbool ]
        EX tind: Z, EX bret : bool,
        PROP (if (tind <? (length - 1)) then bret = false else bret = true)
        RETURN (bool2val bret)
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*sorted - returns true*)
Definition Gprog := [ allNumsSame_spec].

Lemma spec_proof: semax_body Vprog Gprog f_allNumsSame allNumsSame_spec.
Proof.
  start_function. forward_if. forward. Exists ind. Exists true. 
  destruct (ind <? Zlength contents - 1) eqn:Hind.
  apply Zlt_is_lt_bool in Hind. contradiction.  entailer!!.
  forward. forward. forward_if. forward. Exists ind. Exists false. 
  destruct (ind <? Zlength contents - 1) eqn:Hind. entailer!!.  
  apply Z.ltb_ge in Hind.  apply Z.le_ge in Hind. contradiction.
  forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret).
  destruct (fst vret <? Zlength contents - 1) eqn:Hv. entailer!!. 
  rewrite H5. simpl. reflexivity.
  entailer!!. rewrite H5. simpl. reflexivity.
Qed.


