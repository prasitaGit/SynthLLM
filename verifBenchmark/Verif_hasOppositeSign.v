Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.hasOppositeSign.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*boolean: returnstrue if a and b have opposite signs*)
Definition hasOppositeSign_spec : ident * funspec :=
    DECLARE _hasOppositeSign
      WITH a : Z, b : Z 
       PRE [ tint, tint ]
        PROP  (
        Int.min_signed <= a <= Int.max_signed; 
        Int.min_signed <= b <= Int.max_signed
        )
        PARAMS (Vint (Int.repr a); Vint (Int.repr b))
        SEP (TT)
       POST [ tbool ]
        EX bret : bool,
        PROP ( if andb (a <? 0) (b >? 0) then bret = true 
              else if andb (b <? 0) (a >? 0) then bret = true else bret = false)
        RETURN (bool2val bret)
        SEP(TT).

(*opposite signs return true, else false*)
Definition Gprog := [ hasOppositeSign_spec].

Lemma spec_proof: semax_body Vprog Gprog f_hasOppositeSign hasOppositeSign_spec.
Proof.
      start_function. unfold MORE_COMMANDS, abbreviate. (*joint postc. here*) forward_if (True \/ False).
      forward. entailer!!. forward. entailer!!. apply semax_if_seq.
Admitted.




