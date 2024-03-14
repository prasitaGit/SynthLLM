Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.minTwo.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition minTwo_spec : ident * funspec :=
    DECLARE _minTwo
      WITH a : Z, b : Z
       PRE [tint, tint ]
        PROP  (Int.min_signed <= a <= Int.max_signed;
        Int.min_signed <= b <= Int.max_signed)
        PARAMS (Vint (Int.repr a); Vint (Int.repr b))
        SEP (TT)
       POST [ tint ]
        PROP ()
        RETURN (Vint (Int.repr (Z.min a b)))
        SEP(TT).

(*int - minimum of 2 numbers*)
Definition Gprog := [ minTwo_spec].

Lemma spec_proof: semax_body Vprog Gprog f_minTwo minTwo_spec.
Proof.
  start_function. forward_if. forward.  f_equal. f_equal. lia. 
  forward. f_equal. f_equal. lia.
Qed.


