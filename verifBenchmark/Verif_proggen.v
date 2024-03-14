Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.proggen.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)

(*swap specification*)
Definition swapadd_spec : ident * funspec :=
  DECLARE _swapadd
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= a <= Int.max_signed;
    Int.min_signed <= b <= Int.max_signed;
    Int.min_signed <= Int.signed (Int.repr b) + Int.signed (Int.repr 1) <= Int.max_signed;
    Int.min_signed <= Int.signed (Int.repr a) + Int.signed (Int.repr 2) <= Int.max_signed
    )
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (SEPx(
      (data_at sh1 tint (Vint (Int.repr (b + 1))) x :: (data_at sh2 tint (Vint (Int.repr (a + 2))) y :: nil))
      )
    ).


Definition Gprog := [swapadd_spec].


(*rules:*)
(*Ltac - to check progress*)
Ltac progltac :=
  match goal with
  | |- semax _ _ (Sloop _)  _ => idtac "Error - not supported"
  | |- semax _ _ (Sifthenelse _ _ _)  _ => idtac "Error - not supported"
  | |- semax _ _ (Ssequence (Sloop _) _)  _ => idtac "Error - not supported"
  | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _)  _ => idtac "Error - not supported"
  | |- semax _ _ ?c  _ => forward; progltac
  | |- ?Pr |-- ?Po => entailer!
  end.

Lemma swapaddSynth: semax_body Vprog Gprog f_swapadd swapadd_spec.
Proof.
  start_function. progltac.
Qed.

