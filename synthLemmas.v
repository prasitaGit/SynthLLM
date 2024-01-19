Require VC.Preface.  (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

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

(*start function*)
Ltac start_functionaux := start_aux1; start_aux2; start_aux3.

(*determine if read is possible - if so, then read*)
Ltac matchReadLoc l a idG idT :=
  match l with 
  | nil => eapply semax_seq' with (c1 := (Sset idG (Ederef (Etempvar idT (tptr tint)) tint)))
  | temp ?t a  :: ?l' => fail (*read fails, as pre and post are the same*)
  | _ :: ?l' => matchReadLoc l' a idG idT
  end.

(*traverse the SEPx list and determine value of aå**)
Ltac matchReadSepAndTac s l v idG idT :=
  match s with 
  | nil => simpl
  | data_at ?sh tint ?a v  :: ?t => matchReadLoc l a idG idT
  | _ :: ?t => matchReadSepAndTac t l v idG idT
  end.

(*read tactic - ltac; calls the ltacs above*)
Ltac readtac v idG idT  :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ _ => matchReadSepAndTac Sx Lx v idG idT
  end.

(*apply write lemma if write is possible*)
Ltac matchWriteLoc l a idV :=
  match l with 
  | nil => fail (*write not possible*)
  | temp ?t a  :: ?l' => eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar idV (tptr tint)) tint) (Etempvar t tint)))
  | _ :: ?l' => matchWriteLoc l' a idV
  end.

(*determine if the placeholder is a constant or a variable*)
Ltac detConstantOrVariable l a :=
  match l with
  | nil => false
  | temp _ a :: _ => true
  | _ :: ?t => detConstantOrVariable t a
  end.

(*fetch the identifier that is pointing to the variable*)
Ltac fetchVariable l a  :=
  match l with
  | nil => default
  | temp ?t a :: ?l' => t
  | _ :: ?l' => fetchVariable l' a
  end.

(*fetch the operator name: specific for operations involved in a op b*)
Ltac fetchOperator Op :=
  match Op with
  |Z.add _ _ => Oadd
  |Z.sub _ _ => Osub
  |Z.mul _ _ => Omul
  |Z.eq_dec _ _ => Oeq
  |Z_lt_ge_dec _ _ => Olt 
  |Z_gt_le_dec _ _ => Ogt
  |Z_le_gt_dec _ _ => Ole
  |Z_ge_lt_dec _ _ => Oge
  end.

(*different cases to consider for write*)
Ltac matchWriteSepAndTac s l v idV :=
  match s with
  | nil =>  fail
  | data_at ?sh tint (Vint (Int.repr (?o' ?a' ?b'))) v  :: ?t => 
      let ac := (detConstantOrVariable l (Vint (Int.repr a'))) in 
      let bc := (detConstantOrVariable l (Vint (Int.repr b'))) in
      let va := (fetchVariable l (Vint (Int.repr a'))) in 
      let vb := (fetchVariable l (Vint (Int.repr b'))) in
      let opbin := (fetchOperator (o' a' b')) in
      match ac with
      | true => match bc with
                | true =>  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar idV (tptr tint)) tint) (*both variables*)
                          (Ebinop opbin (Etempvar va tint) (Etempvar vb tint) tint))) 
                | false => eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar idV (tptr tint)) tint) (*a var, b const.*)
                          (Ebinop opbin (Etempvar va tint) (Econst_int (Int.repr b') tint) tint)))
                end 
      | false => match bc with
                 | true =>  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar idV (tptr tint)) tint) (*a const. b var*)
                          (Ebinop opbin (Econst_int (Int.repr a') tint) (Etempvar vb tint) tint)))
                 | false => eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar idV (tptr tint)) tint) (*both const.*)
                          (Ebinop opbin (Econst_int (Int.repr a') tint) (Econst_int (Int.repr b') tint) tint)))
                 end 
      end
  | data_at ?sh tint (Vint (Int.repr ?a)) v  :: ?t => matchWriteLoc l (Vint (Int.repr a)) idV
  | _ :: ?t =>  matchWriteSepAndTac t l v idV 
  end. 

(*x _x; x -> b *)
Ltac writetac v idV :=
  match goal with 
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ 
        (normal_ret_assert (PROPx _ (LOCALx _ (SEPx ?Spx)) * _)%logic) => matchWriteSepAndTac Spx Lx v idV
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ 
  (normal_ret_assert (fun rho : environ => ((PROPx _ (LOCALx _ (SEPx ?Spx))) rho * _ rho)%logic)) => matchWriteSepAndTac Spx Lx v idV
  end.

Ltac ifAndTac l comp v1 v2 :=
  let op := (fetchOperator (comp v1 v2)) in 
  let ac := (fetchVariable l (Vint (Int.repr v1))) in 
  let bc := (fetchVariable l (Vint (Int.repr v2))) in
  apply semax_later_trivial; eapply semax_ifthenelse_PQR' with (b := (Ebinop op (Etempvar ac tint) (Etempvar bc tint) tint)).

(*Ltac for if tactic*)
Ltac conditional_writetac v idV b :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _  (normal_ret_assert (PROPx _ (LOCALx _ 
              (SEPx (if ?comp ?a' ?b' then ?Spifx else ?Spex))) * _)%logic) => match b with
                                                                               | true => matchWriteSepAndTac Spifx Lx v idV
                                                                               | false => matchWriteSepAndTac Spex Lx v idV
                                                                              end 
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ (normal_ret_assert 
               (fun rho : environ => ((PROPx _ (LOCALx _ 
               (SEPx (if ?comp ?a' ?b' then ?Spifx else ?Spex)))) 
               rho * _ rho)%logic)) => match b with
                                       | true => matchWriteSepAndTac Spifx Lx v idV
                                       | false => matchWriteSepAndTac Spex Lx v idV
                                       end 
  end.

(*Ltac for if tactic*)
Ltac iftac :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _  (normal_ret_assert (PROPx _ (LOCALx _ 
              (SEPx (if ?comp ?a' ?b' then ?Spifx else ?Spex))) * _)%logic) => ifAndTac Lx comp a' b'
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ (normal_ret_assert 
               (fun rho : environ => ((PROPx _ (LOCALx _ (SEPx (if ?comp ?a' ?b' then ?Spifx else ?Spex)))) 
                rho * _ rho)%logic)) => ifAndTac Lx comp a' b'
  end.