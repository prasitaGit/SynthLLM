Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.perfectsquare.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(*if number is a perfect square: returns true*)
Definition perfectsquare_spec : ident * funspec :=
    DECLARE _perfectsquare
      WITH num : Z, val : Z
       PRE [ tuint, tuint ]
        PROP  (0 <= num <= Int.max_unsigned; 0 <= val <= Int.max_unsigned;
        0 <= val * val <= Int.max_unsigned)
        PARAMS ( Vint (Int.repr num); Vint (Int.repr val))
        SEP (TT)
       POST [ tbool ]
        EX v : Z, EX b : bool,
        PROP (if (v >? num) then b = false else b = true)
        RETURN (bool2val b)
        SEP(TT).

Definition Gprog := [ perfectsquare_spec].

Lemma spec_proof: semax_body Vprog Gprog f_perfectsquare perfectsquare_spec.
Proof.
  start_function. forward_if. forward. Exists val. 
  rewrite Z.gtb_ltb. Search (_ <? _) true.  apply Zaux.Zlt_bool_true in H2.
  rewrite H2. Exists false. entailer!!. 
  forward_if. forward. Exists num. rewrite  Z.gtb_ltb.
  rewrite Z.ltb_irrefl. Exists true. entailer!!.
  forward_call. split; try lia. 
  
Admitted.




