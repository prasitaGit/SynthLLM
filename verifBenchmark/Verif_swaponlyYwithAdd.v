Require VC.Preface.  (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.swaponlyYwithAdd.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)

(*swap specification*)
Definition swaponlyYwithAdd_spec : ident * funspec :=
  DECLARE _swaponlyYwithAdd
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= Int.signed (Int.repr a) + Int.signed (Int.repr 3) <= Int.max_signed
    )
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr (a + 3))) y).


Definition Gprog := [swaponlyYwithAdd_spec].

Lemma swapaddSynth: semax_body Vprog Gprog f_swaponlyYwithAdd swaponlyYwithAdd_spec.
Proof.
  start_function. fastforward. entailer!.
Qed.

