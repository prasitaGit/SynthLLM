Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.prod_firstevenodd.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*product of the first even and odd number in an array*)
Definition prod_firsteveodd_spec : ident * funspec :=
    DECLARE _prod_firsteveodd
      WITH a : val, sh : share, prodn : Z, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        Int.min_signed <= prodn <= Int.max_signed;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
        Forall (fun x => Int.min_signed <= prodn * x <= Int.max_signed) contents;)
        PARAMS (a; Vint (Int.repr prodn); Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
        EX EX i : Z,
        PROP (if (Z.eq_dec ind length) then i = -1 else Zeven i)
        RETURN (Vint (Int.repr i))
        SEP(
          data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*sorted - returns true*)
Definition Gprog := [ prod_firsteveodd_spec].


