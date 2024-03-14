Require VC.Preface.  (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.swapif.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)

(*swap specification*)
Definition swapif_spec : ident * funspec :=
  DECLARE _swapif
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= a <= Int.max_signed;
    Int.min_signed <= b <= Int.max_signed;
    Int.min_signed <= Int.signed (Int.repr b) + Int.signed (Int.repr 5) <= Int.max_signed;
    Int.min_signed <= Int.signed (Int.repr a) + Int.signed (Int.repr 5) <= Int.max_signed
    )
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (SEPx(
      if Z_lt_ge_dec a b then 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr a)) y :: nil)) 
      else 
      (data_at sh1 tint (Vint (Int.repr (b + 5))) x :: (data_at sh2 tint (Vint (Int.repr (a + 5))) y :: nil))
      )
    ).


Definition Gprog := [swapif_spec].

Lemma swapaddSynth: semax_body Vprog Gprog f_swapif swapif_spec.
Proof.
  start_function. fastforward. 
  destruct (Z_lt_ge_dec a b) eqn:Hzlt. entailer!. 
  contradiction. 
  destruct (Z_lt_ge_dec a b) eqn:Hzlt. contradiction. entailer!.
Qed.

