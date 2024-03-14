Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.commonElement.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*common element specification - simple; no ii required*)
Definition commonElementOne_spec : ident * funspec :=
  DECLARE _commonElementOne
   WITH a: val, b : val, sh1 : share, sh2 : share, 
     indA : Z, indB : Z, lengthA : Z, lengthB : Z, contentsA : list Z, contentsB : list Z
   PRE [ tptr tint, tptr tint, tuint, tuint, tuint, tuint ]
    PROP  (readable_share sh1; readable_share sh2; 
    Zlength contentsA = lengthA; Zlength contentsB = lengthB;
    0 <= lengthA <= Int.max_unsigned; 0 <= lengthB <= Int.max_unsigned;
    0 <= indA <= lengthA; 0 <= indB <= lengthB;
    Forall (fun x => Int.min_signed <= x <= Int.max_signed) contentsA;
    Forall (fun x => Int.min_signed <= x <= Int.max_signed) contentsB
    )
    PARAMS (a; b; Vint(Int.repr indA); Vint(Int.repr indB); Vint (Int.repr lengthA); Vint (Int.repr lengthB))
    SEP (data_at sh1 (tarray tint lengthA) (map Vint (map Int.repr contentsA)) a;
    data_at sh2 (tarray tint lengthB) (map Vint (map Int.repr contentsB)) b)
   POST [ tbool ]
    EX i : Z, EX bret : bool,
    PROP (if (Z.eq_dec i lengthA) then bret = false else bret = true) 
    RETURN (bool2val bret)
    SEP(
      data_at sh1 (tarray tint lengthA) (map Vint (map Int.repr contentsA)) a;
    data_at sh2 (tarray tint lengthB) (map Vint (map Int.repr contentsB)) b
    ).

(*sorted - returns true*)
Definition Gprog := [commonElementOne_spec].

Lemma spec_proof: semax_body Vprog Gprog f_commonElementOne commonElementOne_spec.
Proof.
  start_function. forward_if. forward.
  Exists (Zlength contentsA). Exists false. entailer!!. destruct (Z.eq_dec (Zlength contentsA) (Zlength contentsA)) eqn:Hedec. 
  reflexivity. unfold not in n. destruct n. reflexivity.
  (*next*)
  forward_if. forward_call. lia. Intros vret. forward.
  Exists (fst vret). Exists (snd vret). destruct (Z.eq_dec (fst vret) (Zlength contentsA)) eqn:Hedec. 
  entailer!!. rewrite H9. simpl. reflexivity. 
  entailer!!. rewrite H9. simpl. reflexivity.
  forward. forward. forward_if. forward. Exists indA. Exists true. entailer!!.
  destruct (Z.eq_dec indA (Zlength contentsA)) eqn:Heqd. unfold not in H7. destruct H7. assumption. reflexivity.
  forward_call. lia. Intros vret. forward. 
  (*last entailment*)
  Exists (fst vret). Exists (snd vret). destruct (Z.eq_dec (fst vret) (Zlength contentsA)) eqn:Hedec. 
  entailer!!. rewrite H10. simpl. reflexivity. 
  entailer!!. rewrite H10. simpl. reflexivity.
Qed.



