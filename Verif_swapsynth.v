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

  Search Int.repr.  

(*math - x is assigned to y + 1*)
Definition swapmath_spec : ident * funspec :=
  DECLARE _swapmath
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (readable_share sh1; writable_share sh2; 
    Int.min_signed <= Int.signed (Int.repr a) + Int.signed (Int.repr 1) <= Int.max_signed)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr (a + 1))) y). 

(*if spec: *)
Definition swapif_spec : ident * funspec :=
  DECLARE _swapif
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= a <= Int.max_signed; Int.min_signed <= b <= Int.max_signed)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN () 
    (SEPx(
      if Z_lt_ge_dec a b then 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr a)) y :: nil)) 
      else 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr b)) y :: nil))
      )
    ).
    
    

Definition Gprog := [swapskip_spec; swap_spec; swapmath_spec; swapif_spec].

Lemma swapifSynth: semax_body Vprog Gprog f_swapif swapif_spec.
Proof.
  start_function. fastforward. 
  destruct (Z_lt_ge_dec a b) eqn:Hzlt. entailer!.
  contradiction. 
  destruct (Z_lt_ge_dec a b) eqn:Hzlt. contradiction. entailer!.
Qed.

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
Definition _default : ident := $"default".
(*generic body of swap with temporary variables*)
Definition f_swap (s : statement) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
  fn_body := s
|}.

Ltac start_functionaux := start_aux1; start_aux2; start_aux3.

(*all the maps*)
Definition total_map (A : Type) := string -> A.
(*empty maps to nil, as they are total maps*)
Definition map_empty {A : Type} (v : A) : total_map A := (fun _ => v).
(*update function*)
Definition map_update {A : Type} (m : total_map A) (x : string) (v : A) := fun x' => if String.eqb x x' then v else m x'.
(*check if an element belongs to a map*)
(*Define ident map (string to ident) with default as the default element*)
Definition id_map := map_update (map_update (map_update (map_update (map_empty default) "_x" _x) "_y" _y) "_a2" _a2) "_b2" _b2.
(*Define variable (given + ghost) to identifier string*)
Definition var_map := map_update (map_update (map_empty "nil") "x" "_x") "y" "_y".
(*map identifiers of temp. variables to variables*)
Definition ident_map := map_update (map_update (map_empty "nil") "_x" "x") "_y" "y".
(*Map for precc.*)
Definition precc_map := map_update (map_update (map_empty "nil") "x" "a") "y" "b".
(*Map for postc.*)
Definition postc_map := map_update (map_update (map_empty "nil") "x" "b") "y" "a".
(*Algorithm: 
 1. Map : Precc. Map : Postc.
 2. Check: for every variable: if precc. maps to a ghost variable and not identifier -> read the variable into identifier
 3. Once all reading is done: Check that all precc. variables point to identifiers -> check for write
 4. Pre and Post same -> Exit
*)
Check (Sset (id_map (precc_map "x")) (Ederef (Etempvar (id_map (var_map "x")) (tptr tint)) tint)). 
Check (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)).

Definition conc (s : string) := append (append "_" s) "2". (*used for variable names*)

Definition vars := ["x";"y"].
(*(String.eqb (ident_map (precc_map "x")) "nil").*)
(*v1 : a; v2 : _a2 : returns new postcondition map*)
Fixpoint updMap (varin : list string) (v1 v2 : string) (post_mcmap : total_map string) :=
  match varin with
  | nil => post_mcmap
  | h :: t => if String.eqb (post_mcmap h) v1 then (updMap t v1 v2 (map_update post_mcmap h v2)) 
              else (updMap t v1 v2 post_mcmap)
  end. 

(*read: checks for a variable if read is applicable and does updates to the maps acco*)
Definition read_identmap (x : string) := 
  let v := (precc_map x) in (if (String.eqb (ident_map v) "nil") then 
  (let iden := conc v in  
   let idmp1 := map_update ident_map iden v in 
   let idpmp1 := map_update precc_map x iden in updMap vars v iden postc_map  
   )    
else ident_map).


(*required for read - first update is to identity map*)
Definition upd_ident (idmap : total_map string) (x v : string) := 
  let iden := conc v in map_update idmap iden v.

(*required for read - second update is to precc. map*)
Definition upd_premap (pre_map : total_map string) (x iden : string) := 
  map_update pre_map x iden.

(*required for read - third update is for postc. map*)
Definition upd_postmap (post_map : total_map string) (v iden : string) := 
  updMap vars v iden post_map.


(*write map: for a variable; check if its pre and postc. are both identifiers and both different identifiers
map the pre id. to post*)
Definition write_identmap (iden_map prec_map post_map : total_map string) (x : string) := 
  let v1 := (prec_map x) in 
  let v2 := (post_map x) in 
  if (String.eqb (iden_map v1) "nil") then prec_map (*Read needs to happen*) 
  else if (String.eqb (iden_map v2) "nil") then prec_map  (*Read needs to happen*)
  else if (String.eqb v1 v2) then prec_map (*both are equal: frame*)
  else map_update prec_map x v2 (*update precc_map for x to point to v2*)
.

(* x -> a; y -> b | x -> b; y -> a     |  y -> _a2 |  y -> _a2*) 
Fixpoint readSynth (iden_map prec_map post_map : total_map string) (l : list string) :=
  match l with 
  | nil => (iden_map, (prec_map, post_map))
  | h :: t => let v := (prec_map h) in (if (String.eqb (iden_map v) "nil") then 
              (let iden := conc v in  
              let idmp := map_update iden_map iden v in 
              let idprmp := map_update prec_map h iden in 
              let idpomp := updMap vars v iden post_map in 
              readSynth idmp idprmp idpomp t  
              )    
             else readSynth iden_map prec_map post_map t)
  end.

Fixpoint writeSynth (iden_map prec_map post_map : total_map string) (l : list string) :=
  match l with
  | nil => prec_map (*only prec. map can change for write*)
  | h :: t => writeSynth iden_map (write_identmap iden_map prec_map post_map h) post_map t
end. 

Definition readRes := readSynth ident_map precc_map postc_map vars.


Ltac matchReadLoc l a idG idT :=
  match l with 
  | nil => eapply semax_seq' with (c1 := (Sset idG (Ederef (Etempvar idT (tptr tint)) tint)))
  | temp ?t a  :: ?l' => simpl
  | _ :: ?l' => matchReadLoc l' a idG idT
  end.

Ltac matchReadSepAndTac s l v idG idT :=
  match s with 
  | nil => simpl
  | data_at ?sh tint ?a v  :: ?t => (*match => call ltac loc*) matchReadLoc l a idG idT
  | _ :: ?t => matchReadSepAndTac t l v idG idT
  end.


Ltac readtac v idG idT  :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ _ => matchReadSepAndTac Sx Lx v idG idT
  end.


Ltac matchWriteLoc l a idV :=
  match l with 
  | nil => simpl
  | temp ?t a  :: ?l' => eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar idV (tptr tint)) tint) (Etempvar t tint)))
  | _ :: ?l' => matchWriteLoc l' a idV
  end.

Ltac matchWriteSepAndTac s l v idV :=
  match s with
  | nil => simpl
  | data_at ?sh tint ?a v  :: ?t => matchWriteLoc l a idV 
  | _ :: ?t => matchWriteSepAndTac t l v idV 
  end. 

(*x _x; x -> b; Check pre Loc. *)
Ltac writetac v idV :=
  match goal with 
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ 
        (normal_ret_assert (PROPx _ (LOCALx _ (SEPx ?Spx)) * _)%logic) => matchWriteSepAndTac Spx Lx v idV
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ 
  (normal_ret_assert (fun rho : environ => ((PROPx _ (LOCALx _ (SEPx ?Spx))) rho * _ rho)%logic)) => matchWriteSepAndTac Spx Lx v idV
  end.

Ltac foldtac :=
  match goal with 
  | |- semax _ (PROPx _ (LOCALx ?Lx (SEPx ?Sx))) _ 
          (normal_ret_assert ?N) => change (normal_ret_assert N) with abbreviate
  end.


Lemma body_swapsynthesisLtacs: exists s, semax_body Vprog Gprog (f_swap s)  swap_spec.
Proof.
  eexists. start_functionaux.
  readtac x _a2 _x. apply semax_later_trivial. load_tac. simpl.
  (*readtac y _b2 _y.*) 
  readtac y _b2 _y. apply semax_later_trivial. load_tac. simpl.
  (*write - unfold*)
  unfold POSTCONDITION. unfold abbreviate.
  writetac y _y. apply semax_later_trivial. store_tac. simpl.
  (*second write*)
  writetac x _x.
  apply semax_later_trivial. store_tac. simpl. 
  (*skip part*)
  unfold stackframe_of. simpl map. rewrite fold_right_nil. simpl.
  (*rewrite sepcon_emp.*)
  eapply semax_post. 5:{ eapply semax_skip. }
  apply derives_ENTAIL. eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). 
  eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). simpl. 
  intros. entailer!.
  apply derives_ENTAIL.
  simpl. intros. entailer!.
  simpl. intros. entailer!. simpl. intros. entailer!.
Qed.

Lemma body_swapsynthesisRules: exists s, semax_body Vprog Gprog (f_swap s)  swap_spec.
Proof.
  eexists. start_functionaux.
  (*check if read x is possible*)
  Definition readResult := readSynth ident_map precc_map postc_map vars.
  Definition pread_idmap := fst readResult.
  Definition pre_rmap := fst (snd readResult).
  Definition post_rmap := snd (snd readResult).
  (*Set commands after read*)
  (*Check precc. x -> _a2; get identifer -> idmap (_a2); var_map *)
  (*first read - (c1 := (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))).*)
  eapply semax_seq' with (c1 := ((Sset (id_map (pre_rmap "x")) (Ederef (Etempvar (id_map (var_map "x")) (tptr tint)) tint)))).
  apply semax_later_trivial. load_tac. simpl.
  (*second read*)
  eapply semax_seq' with (c1 := ((Sset (id_map (pre_rmap "y")) (Ederef (Etempvar (id_map (var_map "y")) (tptr tint)) tint)))).
  apply semax_later_trivial. load_tac. simpl.
  (*write*)
  Definition pre_writemap := writeSynth pread_idmap pre_rmap post_rmap vars.
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar (id_map (var_map "x")) (tptr tint)) tint) (Etempvar (id_map (pre_writemap "x")) tint))).
  apply semax_later_trivial. store_tac. simpl. 
  (*write second*)
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar (id_map (var_map "y")) (tptr tint)) tint) (Etempvar (id_map (pre_writemap "y")) tint)))(c2 := Sskip).
  apply semax_later_trivial. store_tac. simpl. 
  simpl. forward. entailer!.
Qed.
 

(*rules: Pre and Post -> decide*)
(*swap synthesis*)
Lemma body_swapfullsynthesis: exists s, semax_body Vprog Gprog (f_swap s)  swap_spec.
Proof.
  eexists. start_functionaux.
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
  apply semax_later_trivial. store_tac. simpl. forward. entailer!.
Qed.


Definition f_swapmath (s : statement) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
  fn_body := s
|}.

Lemma body_swapmathsynthesis: exists s, semax_body Vprog Gprog (f_swapmath s)  swapmath_spec.
Proof.
  eexists. start_functionaux.
  (*read*)
  eapply semax_seq' with (c1 := (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))).
  apply semax_later_trivial. load_tac. simpl. 
  (*second read*)
  eapply semax_seq' with (c1 := (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))).
  apply semax_later_trivial. load_tac. simpl.
  (*write*)
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _y (tptr tint)) tint)
  (Ebinop Oadd (Etempvar _a2 tint) (Econst_int (Int.repr 1) tint) tint)))(c2 := Sskip).
  apply semax_later_trivial. store_tac. simpl. forward. entailer!.
Qed.



Definition f_swapif (s : statement) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
  fn_body := s
|}.

Lemma body_swapifsynthesis: exists s, semax_body Vprog Gprog (f_swapif s)  swapif_spec.
Proof.
  eexists. start_functionaux.
  (*read a and b*)
  (*read*)
  eapply semax_seq' with (c1 := (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))).
  apply semax_later_trivial. load_tac. simpl. 
  (*second read*)
  eapply semax_seq' with (c1 := (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))).
  apply semax_later_trivial. load_tac. simpl.
  (*if-else*)
  apply semax_later_trivial. eapply semax_ifthenelse_PQR' with (b := (Ebinop Olt (Etempvar _a2 tint) (Etempvar _b2 tint) tint)).
  simpl. reflexivity. entailer!. entailer!. 
  (*semax_seq: both c1; c2*)
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))).
  apply semax_later_trivial. store_tac. simpl.
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)))(c2 := Sskip).
  apply semax_later_trivial. store_tac. simpl. forward.
  (*prove entailment part*)
  destruct (Z_lt_ge_dec a b) eqn:Hzlt. entailer!. entailer!.
  (*false part*)
  eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)))(c2 := Sskip).
  apply semax_later_trivial. store_tac. simpl. forward.
  destruct (Z_lt_ge_dec a b) eqn:Hzlt. entailer!. entailer!.
Qed.




