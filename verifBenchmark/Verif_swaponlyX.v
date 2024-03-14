Require VC.Preface.  (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.swaponlyX.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)

(*swap specification*)
Definition swaponlyX_spec : ident * funspec :=
  DECLARE _swaponlyX
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr b)) y).


Definition Gprog := [swaponlyX_spec].

Lemma swapaddSynth: semax_body Vprog Gprog f_swaponlyX swaponlyX_spec.
Proof.
  start_function. fastforward. entailer!.
Qed.

