Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.mulTwoNums.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition mulTwoNums_spec : ident * funspec :=
    DECLARE _mulTwoNums
      WITH a : Z, b : Z
       PRE [tint, tint ]
        PROP  (Int.min_signed <= a <= Int.max_signed;
        Int.min_signed <= b <= Int.max_signed; Int.min_signed <= (Z.mul a b) <= Int.max_signed)
        PARAMS (Vint (Int.repr a); Vint (Int.repr b))
        SEP (TT)
       POST [ tint ]
        PROP ()
        RETURN (Vint (Int.repr (Z.mul a b)))
        SEP(TT).

(*int - multiplication of 2 numbers*)
Definition Gprog := [ mulTwoNums_spec].

Lemma spec_proof: semax_body Vprog Gprog f_mulTwoNums mulTwoNums_spec.
Proof.
  start_function. forward.
Qed.


