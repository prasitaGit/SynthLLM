Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.findFirstRepeatedNum.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*Check if index equals length*)
Definition findFirstRepeatedNum_spec : ident * funspec :=
    DECLARE _findFirstRepeatedNum
      WITH a : val, sh : share, indi : Z, indj : Z, length : Z, contents : list Z
       PRE [ tptr tint, tuint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= indi < length;  indi < indj <= length;  
        Forall (fun x =>  Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr indi); Vint (Int.repr indj); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
        EX tind: Z, EX i : Z,
        PROP (if (tind =? (length - 1)) then i = -1 else i = tind)
        RETURN (Vint (Int.repr i))
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*-1 if no nums repeat, else index of the first repeated number*)
Definition Gprog := [ findFirstRepeatedNum_spec].

Lemma spec_proof: semax_body Vprog Gprog f_findFirstRepeatedNum findFirstRepeatedNum_spec.
Proof.
  start_function. forward_if. forward. Exists (Zlength contents - 1). Exists (-1).
  Search (_ =? _). rewrite Z.eqb_refl. entailer!!.
  forward_if. forward_call. Search Int.repr. rewrite sub_repr in H4. 
  apply repr_neq_e in H4. assert (indi < length - 1) by lia. split. lia. lia. 
  Intros vret. forward. Exists (fst vret). Exists (snd vret). destruct (fst vret =? Zlength contents - 1) eqn:Hv.
  entailer!!. entailer!!. 
  rewrite sub_repr in H4. apply repr_neq_e in H4.  assert (indi < length - 1) by lia. 
  assert (indj < length) by lia. forward. forward. forward_if. forward. 
  Exists indi. Exists indi.  Search (_ =? _ = false). apply Z.eqb_neq in H4. rewrite H4. 
  entailer!!. forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret).
  destruct (fst vret =? Zlength contents - 1) eqn:Hret. entailer!!. entailer!!.
Qed.




