Require VC.Preface.  (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VC.swap.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)
 
(*swap specification*)
Definition swap_spec : ident * funspec :=
  DECLARE _swap
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr a)) y).

(*swap-skip specification - point to the same variable*)
Definition swapskip_spec : ident * funspec :=
  DECLARE _swapskip
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y).


Definition Gprog := [swapskip_spec; swap_spec].
(*auxiliary start function 1: the function specific lemmas are commented out*)
Ltac start_aux1 := 
  (*leaf_function;*)
  lazymatch goal with
  | |- semax_body ?V ?G ?F ?spec =>
      (*check_normalized F; function_body_unsupported_features F;*)
         let s := fresh "spec" in
          pose (s := spec); hnf in s; cbn zeta in s;
           repeat
            lazymatch goal with
            | s:=(_, NDmk_funspec _ _ _ _ _):_ |- _ => fail
            | s:=(_, mk_funspec _ _ _ _ _ _ _):_ |- _ => fail
            | s:=(_, ?a _ _ _ _):_ |- _ => unfold a in s
            | s:=(_, ?a _ _ _):_ |- _ => unfold a in s
            | s:=(_, ?a _ _):_ |- _ => unfold a in s
            | s:=(_, ?a _):_ |- _ => unfold a in s
            | s:=(_, ?a):_ |- _ => unfold a in s
            end;
           lazymatch goal with
           | s:=(_, WITH _ : globals PRE [ ] main_pre _ _ _ POST [tint] _):_
             |- _ => idtac
           | s:=?spec':_ |- _ => check_canonical_funspec spec'
           end; change (semax_body V G F s); subst s; 
           unfold NDmk_funspec'
  end;
  let DependedTypeList := fresh "DependedTypeList" in
   unfold NDmk_funspec;
    match goal with
    | |- semax_body _ _ _ (_, mk_funspec _ _ _ ?Pre _ _ _) =>
          split3; [ check_parameter_types' | check_return_type |  ];
           match Pre with
           | fun _ => convertPre _ _ (fun i => _) =>
               intros Espec DependedTypeList i
           | fun _ x => match _ with
                        | (a, b) => _
                        end =>
               intros Espec DependedTypeList [a b]
           | fun _ i => _ => intros Espec DependedTypeList i
           end; simpl fn_body; simpl fn_params; simpl fn_return
    end;
    (*eliminates the rho environ part*)
    try
     match goal with
     | |- semax _ (fun rho => (?A rho * ?B rho)%logic) _ _ =>
           change (fun rho => (?A rho * ?B rho)%logic) with (A * B)%logic
     end; 
    simpl functors.MixVariantFunctor._functor in *;
    simpl rmaps.dependent_type_functor_rec; clear DependedTypeList;
    rewrite_old_main_pre;
    repeat
     match goal with
     | |- semax _ (match ?p with
                   | (a, b) => _
                   end * _)%logic _ _ => destruct p as [a b]
     | |-
       semax _
         (close_precondition _ match ?p with
                               | (a, b) => _
                               end * _)%logic _ _ => 
       destruct p as [a b]
     | |- semax _ (match ?p with
                   | (a, b) => _
                   end eq_refl * _)%logic _ _ => 
       destruct p as [a b]
     | |-
       semax _
         (close_precondition _ (match ?p with
                                | (a, b) => _
                                end eq_refl) * _)%logic _ _ =>
           destruct p as [a b]
     | |-
       semax _
         (close_precondition _
            (fun ae =>
             !! (Datatypes.length (snd ae) = ?A) &&
             ?B (make_args ?C (snd ae) (mkEnviron (fst ae) _ _))) * _)%logic
         _ _ =>
           match B with
           | match ?p with
             | (a, b) => _
             end => destruct p as [a b]
           end
     end; try start_func_convert_precondition.

(*auxiliary start function2: This is exactly same as start_function2*)
Ltac start_aux2 :=
  first
    [ erewrite compute_close_precondition_eq; [  | reflexivity | reflexivity ]
    | rewrite close_precondition_main ].

(*used in place of abbreviate_semax for start_aux3 to put POSTC. in apt. form*)
Ltac abbreviate_semaxaux :=
  match goal with
  | |- semax _ FF _ _ => apply semax_ff
  | |- semax _ (PROPx (False::_) _) _ _ => Intros; contradiction
  | |- semax _ _ _ _ =>
      simplify_Delta;
      repeat match goal with
      | MC := @abbreviate statement _ |- _ => unfold abbreviate in MC; subst MC
      end;
      (*force sequential is modified to support expansion*)
      apply sequential; simpl_ret_assert;
      match goal with |- semax _ _ _ ?Q =>
          abbreviate Q : ret_assert as POSTCONDITION
      end;
      match goal with |- semax _ _ ?C _ =>
        match C with
        | Ssequence ?C1 ?C2 =>
          (* use the next 3 lines instead of "abbreviate"
          in case C1 contains an instance of C2 *)
          let MC := fresh "MORE_COMMANDS" in
          pose (MC := @abbreviate _ C2);
          change C with (Ssequence C1 MC);
          match C1 with
          | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
          | _ => idtac
          end
        | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
        | _ => idtac
        end
        end
  | |- _ |-- _ => unfold_abbrev_ret
  end;
  clear_abbrevs;
  simpl typeof.


Ltac start_aux3 :=
  simpl app;
  simplify_func_tycontext;
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
  | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
  end;
  try expand_main_pre;
  process_stackframe_of;
  repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
  repeat rewrite <- data_at__offset_zero;
  try simple apply start_function_aux1; (*apply semax_extract_PROP.*)
  repeat (apply semax_extract_PROP;
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH
                 | Share.t => intros ?SH
                 | _ => intro
                 end
               | |- _ => intro
               end);
  abbreviate_semaxaux;
  lazymatch goal with 
  | |- semax ?Delta (PROPx _ (LOCALx ?L _)) _ _ => check_parameter_vals Delta L
  | _ => idtac
  end;
  try match goal with DS := @abbreviate (PTree.t funspec) ?DS1 |- _ =>
     unify DS1 (PTree.empty funspec); clearbody DS
  end;
  start_function_hint.


From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Definition _a2 : ident := $"a2".
Definition _b2 : ident := $"b2".
(*generic body of swap with temporary variables*)
Definition f_swap (s : statement) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
  fn_body := s
|}.
      
(*swap synthesis*)
Lemma body_swapfullsynthesis: exists s, semax_body Vprog Gprog (f_swap s)  swap_spec.
Proof.
  eexists. start_aux1; start_aux2; start_aux3.
  (*copy swap synthesis*)
  (*read*)
  eapply semax_seq' with (c1 := (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))). 
  apply semax_later_trivial. load_tac. simpl.
  (*second read*)
  eapply semax_seq' with (c1 := (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))).
  apply semax_later_trivial. load_tac. simpl.
  (*first write*)
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))).
  apply semax_later_trivial. store_tac. simpl.
  (*second write*)
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)))(c2 := Sskip).
  apply semax_later_trivial. store_tac. simpl.
  (*Skip*)
  unfold POSTCONDITION. unfold abbreviate.
  unfold stackframe_of. simpl map. rewrite fold_right_nil. 
  rewrite sepcon_emp. simpl.
  eapply semax_post. 5:{ eapply semax_skip. }
  apply derives_ENTAIL. simpl. intros.  entailer!.   
  eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O).
  eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). simpl. 
  intros. entailer!.
  apply derives_ENTAIL.
  simpl. intros. entailer!.
  simpl. intros. entailer!. simpl. intros. entailer!. 
Qed.



