Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.lastelempos.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Check Z_lt_ge_dec.

(*last position of the element if it exists - weaker*)
Definition lastelempos_spec : ident * funspec :=
    DECLARE _lastelempos
      WITH a : val, sh : share, ele : Z, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tint, tint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; Int.min_signed <= ind <= Int.max_signed;
        -1 <= ind < length; Int.min_signed <= ele <= Int.max_signed;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr ele); Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
        EX i : Z,EX tind : Z,
        PROP (if (Z_lt_ge_dec tind 0) then i = -1 else i = tind) 
        RETURN (Vint (Int.repr i))
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [ lastelempos_spec].

Lemma spec_proof: semax_body Vprog Gprog f_lastelempos lastelempos_spec.
Proof. 
  start_function. forward_if. forward. Exists (-1). Exists (-1). entailer!!.
  forward. forward_if. forward. Exists ind. Exists ind. entailer!!.  
  destruct (Z_lt_ge_dec ind 0) eqn:Hltdec.  contradiction. reflexivity.
  forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret).
  destruct (Z_lt_ge_dec (snd vret) 0) eqn:Hltdec. rewrite H7. entailer!!. entailer!!.
Qed.




