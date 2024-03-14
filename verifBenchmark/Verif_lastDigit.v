Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.lastDigit.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(*returns last digit of n: n >= 0*)
Definition lastDigit_spec : ident * funspec :=
    DECLARE _lastDigit
      WITH n : Z 
       PRE [ tuint ]
        PROP  ( 0 <= n <= Int.max_unsigned)
        PARAMS (Vint (Int.repr n))
        SEP (TT)
       POST [ tuint ]
        EX i : Z,
        PROP (i = Z.modulo n 10)
        RETURN (Vint (Int.repr i))
        SEP(TT).


Definition Gprog := [ lastDigit_spec].

Lemma spec_proof: semax_body Vprog Gprog f_lastDigit lastDigit_spec.
Proof. 
  start_function. forward. Exists (Z.modulo n 10). entailer!!.
Qed.


