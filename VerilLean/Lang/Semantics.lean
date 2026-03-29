/- # Formal Semantics of Verilog
   Expression evaluation, statement execution, module-level transition function construction.
-/

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Analysis

namespace VerilLean.Lang.Semantics

open VerilLean.Lang.Syntax
open VerilLean.Lang.Analysis (getIOIds)
open VerilLean.Lib

-- ## SF monad infrastructure

inductive TrsFail where
  | fatal
  | undeclared
  | undriven
  | notSupported
  | notUnfoldable
  deriving Inhabited, Repr, BEq

abbrev trsOk (A : Type) := Except TrsFail A

-- Lift an `Option` into `trsOk`, mapping `none` to the given failure.
def liftOption (o : Option A) (f : TrsFail) : trsOk A :=
  match o with
  | some a => .ok a
  | none => .error f

-- Fallback bind: if `sf` fails, use `default` instead; then continue with `cont`.
def sfWithDefault (sf : trsOk A) (default : A) (cont : A → trsOk B) : trsOk B :=
  match sf with
  | .ok a => cont a
  | .error _ => cont default

-- Fallback return: if `sf` fails, return `ret`; otherwise continue with `cont`.
def sfOrReturn (sf : trsOk A) (ret : trsOk B) (cont : A → trsOk B) : trsOk B :=
  match sf with
  | .ok a => cont a
  | .error _ => ret

-- ## List operations on trsOk

def sfListMap (f : A → trsOk S) : List A → trsOk (List S)
  | [] => .ok []
  | a :: rest => do let s ← f a; let ss ← sfListMap f rest; pure (s :: ss)

def sfListMap2 (f : A → B → trsOk S) : List A → List B → trsOk (List S)
  | [], _ => .ok []
  | _, [] => .ok []
  | a :: as_, b :: bs => do let s ← f a b; let ss ← sfListMap2 f as_ bs; pure (s :: ss)

def iterate (f : T → A → trsOk A) : List T → A → trsOk A
  | [], a => .ok a
  | t :: ts, a => do let a' ← f t a; iterate f ts a'

def iterateResume (f : T → A → trsOk A) : List T → A → trsOk A
  | [], a => .ok a
  | t :: ts, a => sfWithDefault (f t a) a (iterateResume f ts)

def iterateUpdate (fitr : T → A → trsOk B) (fba : B → A) (nilb : B)
    (upda : A → A → A) (updb : B → B → B) : List T → A → trsOk B
  | [], _ => .ok nilb
  | t :: ts, a => do
    let b ← fitr t a
    let a' := upda a (fba b)
    let brest ← iterateUpdate fitr fba nilb upda updb ts a'
    pure (updb b brest)

-- ## Core types

abbrev Value := HMap
abbrev State := Value
abbrev Flops := State
abbrev Decls := State
abbrev NW := State      -- new wire values
abbrev IFW := State     -- inputs + flops + wires
abbrev IFF := IFW × Flops

structure MTrs where
  inputVids  : List VId
  outputVids : List VId
  func       : State → State → (State × State)

structure Func where
  inputVids : List VId
  func      : State → Value

abbrev TrsFMap (A : Type) := VId → trsOk A

def fmapEmpty : TrsFMap A := fun _ => .error .undeclared

def fmapSingle (k : VId) (v : A) : TrsFMap A :=
  fun k' => if k == k' then .ok v else .error .undeclared

def fmapMerge (m1 m2 : TrsFMap A) : TrsFMap A :=
  fun k => match m1 k with
    | .ok v => .ok v
    | .error _ => m2 k

abbrev MTrss := TrsFMap MTrs
abbrev Funcs := TrsFMap Func

-- ## Helpers

-- Try to find a path in `h1` first, then `h2`.
def hfind2 (p : HPath) (h1 h2 : HMap) : Option HMap :=
  let v := hfind h1 p
  if v == HMap.empty then
    let v2 := hfind h2 p
    if v2 == HMap.empty then none else some v2
  else some v

-- Build a state from parallel lists of variable ids and values.
def buildFInputState (vids : List VId) (args : List Value) : State :=
  HMap.str (vids.zip args)

-- ## Literal evaluation

def evalPriLiteral : primary_literal → Value
  | .number (.integral (.decimal (.unsigned v))) =>
      HMap.bits (SZ.mk' v sz_int32 false)
  | .number (.integral (.decimal (.base_unsigned none v))) =>
      HMap.bits (SZ.mk' v sz_int32 false)
  | .number (.integral (.decimal (.base_unsigned (some sz) v))) =>
      HMap.bits (SZ.mk' v sz false)
  | .number (.integral (.binary none v)) =>
      HMap.bits (SZ.mk' (binaryZtoZ sz_int32 v) sz_int32 false)
  | .number (.integral (.binary (some sz) v)) =>
      HMap.bits (SZ.mk' (binaryZtoZ sz v) sz false)
  | .number (.integral (.octal none v)) =>
      HMap.bits (SZ.mk' (octalZtoZ sz_int32 v) sz_int32 false)
  | .number (.integral (.octal (some sz) v)) =>
      HMap.bits (SZ.mk' (octalZtoZ sz v) sz false)
  | .number (.integral (.hex none v)) =>
      HMap.bits (SZ.mk' v sz_int32 false)
  | .number (.integral (.hex (some sz) v)) =>
      HMap.bits (SZ.mk' v sz false)
  | .unbased_unsized .zeros => HMap.bits (SZ.mk' 0 1 false)
  | .unbased_unsized .ones => HMap.bits (SZ.mk' 1 1 false)

-- ## Operator function dispatch

def uniOpFunc : unary_operator → SZ → SZ
  | .plus  => id
  | .minus => SZ.uMinus
  | .not   => SZ.uNot
  | .neg   => SZ.uNeg
  | .and   => SZ.uAnd
  | .nand  => SZ.uNand
  | .or    => SZ.uOr
  | .nor   => SZ.uNor
  | .xor   => SZ.uXor
  | .xnor  => SZ.uXnor

def binOpFunc : binary_operator → SZ → SZ → SZ
  | .add   => SZ.bAdd
  | .sub   => SZ.bSub
  | .mul   => SZ.bMul
  | .div   => SZ.bDiv
  | .rem   => SZ.bRem
  | .eq    => SZ.bEq
  | .neq   => SZ.bNEq
  | .feq   => SZ.bFEq
  | .fneq  => SZ.bFNEq
  | .weq   => SZ.bWEq
  | .wneq  => SZ.bWNEq
  | .land  => SZ.bLAnd
  | .lor   => SZ.bLOr
  | .pow   => SZ.bPow
  | .lt    => SZ.bLt
  | .le    => SZ.bLe
  | .gt    => SZ.bGt
  | .ge    => SZ.bGe
  | .band  => SZ.bAnd
  | .bor   => SZ.bOr
  | .bxor  => SZ.bXor
  | .bxnor => SZ.bXnor
  | .shr   => SZ.bShr
  | .shl   => SZ.bShl
  | .sar   => SZ.bSar
  | .sal   => SZ.bSal

-- ## Assign operator to binary operator

def assignOpToBinOp : assign_op → Option binary_operator
  | .eq   => none
  | .add  => some .add
  | .sub  => some .sub
  | .mul  => some .mul
  | .div  => some .div
  | .rem  => some .rem
  | .band => some .band
  | .bor  => some .bor
  | .bxor => some .bxor
  | .shl  => some .shl
  | .shr  => some .shr
  | .sal  => some .sal
  | .sar  => some .sar

-- ## Declaration size helpers

/- Evaluate packed dimensions to get the declaration size (as HMap).
   Returns `none` for `nil`. -/
def evalPackedDims (evalE : expression → trsOk Value) : packed_dims → trsOk (Option Value)
  | .nil => .ok none
  | .one (.range lr rr) => do
      let lv ← evalE lr
      let rv ← evalE rr
      let lsz := hbits lv
      let rsz := hbits rv
      let w := (lsz.norm - rsz.norm).toNat + 1
      pure (some (HMap.bits (SZ.mk' 0 w false)))
  | .one (.one de) => do
      let dv ← evalE de
      let dsz := hbits dv
      let w := dsz.norm.toNat
      pure (some (HMap.bits (SZ.mk' 0 w false)))
  | .cons pd pds => do
      let _ ← match pd with
        | .range lr rr => do
            let lv ← evalE lr
            let rv ← evalE rr
            let lsz := hbits lv
            let rsz := hbits rv
            let w := (lsz.norm - rsz.norm).toNat + 1
            pure (some (HMap.bits (SZ.mk' 0 w false)))
        | .one de => do
            let dv ← evalE de
            let dsz := hbits dv
            let w := dsz.norm.toNat
            pure (some (HMap.bits (SZ.mk' 0 w false)))
      evalPackedDims evalE pds

-- Get the default value for a data type.
def declDataType (evalE : expression → trsOk Value) : data_type → trsOk Value
  | .int_vec _ pds => do
      let ov ← evalPackedDims evalE pds
      match ov with
      | some v => pure v
      | none => pure (HMap.bits (SZ.mk' 0 1 false))
  | .int_atom .byte => pure (HMap.bits (SZ.mk' 0 8 false))
  | .int_atom .short_int => pure (HMap.bits (SZ.mk' 0 16 true))
  | .int_atom .long_int => pure (HMap.bits (SZ.mk' 0 64 true))
  | .int_atom .integer => pure (HMap.bits (SZ.mk' 0 32 true))
  | .int_atom .time => pure (HMap.bits (SZ.mk' 0 64 false))

def declDataTypeOrImplicit (evalE : expression → trsOk Value) : data_type_or_implicit → trsOk Value
  | .data dt => declDataType evalE dt
  | .implicit pds => do
      let ov ← evalPackedDims evalE pds
      match ov with
      | some v => pure v
      | none => pure (HMap.bits (SZ.mk' 0 1 false))

def declPortType (evalE : expression → trsOk Value) : port_type → trsOk Value
  | .port _ pds => do
      let ov ← evalPackedDims evalE pds
      match ov with
      | some v => pure v
      | none => pure (HMap.bits (SZ.mk' 0 1 false))

-- ## declfind / wfind — looking up declarations and values

-- Find the path to a variable in declarations.
def declfind (decls : Decls) (vid : VId) : trsOk HPath :=
  liftOption (hpos vid (hstr decls)) .undeclared

-- Find a variable value: look in nw, then ifw, falling back through decls path.
def wfind (decls : Decls) (ifw : IFW) (nw : NW) (vid : VId) : trsOk Value := do
  let p ← declfind decls vid
  match hfind2 p nw ifw with
  | some v => pure v
  | none => .error .undriven

-- ## getAccessVid — extract vid from a "child" expression

def getAccessVid : expression → trsOk VId
  | .ident vid => .ok vid
  | _ => .error .notSupported

-- ## Expression evaluation (mutual recursion with evalExprList and lvposfind)

mutual

def evalExpr (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : expression → trsOk Value
  | .primary_literal pl => pure (evalPriLiteral pl)
  | .ident vid => wfind decls ifw nw vid
  | .hierarchical_ident pe ce => do
      let pv ← evalExpr decls funcs ctxs cpos ifw nw pe
      let cvid ← getAccessVid ce
      pure (haccess pv cvid)
  | .select te se => do
      let tv ← evalExpr decls funcs ctxs cpos ifw nw te
      let sv ← evalExpr decls funcs ctxs cpos ifw nw se
      pure (hselect tv (hbits sv))
  | .select_const_range se lr rr => do
      let sv ← evalExpr decls funcs ctxs cpos ifw nw se
      let lv ← evalExpr decls funcs ctxs cpos ifw nw lr
      let rv ← evalExpr decls funcs ctxs cpos ifw nw rr
      pure (hrange sv (hbits lv) (hbits rv))
  | .select_indexed_range_add se lr rr => do
      let sv ← evalExpr decls funcs ctxs cpos ifw nw se
      let lv ← evalExpr decls funcs ctxs cpos ifw nw lr
      let rv ← evalExpr decls funcs ctxs cpos ifw nw rr
      let lsz := hbits lv
      let rsz := hbits rv
      let hi := SZ.bAdd lsz (SZ.bSub rsz (SZ.mk' 1 rsz.width false))
      pure (hrange sv hi lsz)
  | .select_indexed_range_sub se lr rr => do
      let sv ← evalExpr decls funcs ctxs cpos ifw nw se
      let lv ← evalExpr decls funcs ctxs cpos ifw nw lr
      let rv ← evalExpr decls funcs ctxs cpos ifw nw rr
      let lsz := hbits lv
      let rsz := hbits rv
      let lo := SZ.bSub lsz (SZ.bSub rsz (SZ.mk' 1 rsz.width false))
      pure (hrange sv lsz lo)
  | .concat es => do
      let vs ← evalExprList decls funcs ctxs cpos ifw nw es
      pure (harray vs)
  | .mult_concat ne ces => do
      let nv ← evalExpr decls funcs ctxs cpos ifw nw ne
      let cvs ← evalExprList decls funcs ctxs cpos ifw nw ces
      let count := (hbits nv).norm.toNat
      let repeated := (List.replicate count cvs).flatten
      pure (harray repeated)
  | .tf_call tfid aes => do
      let f ← funcs tfid
      let avs ← evalExprList decls funcs ctxs cpos ifw nw aes
      let inputState := buildFInputState f.inputVids avs
      pure (f.func inputState)
  | .system_tf_call .signed aes =>
      match aes with
      | [ae] => do
          let av ← evalExpr decls funcs ctxs cpos ifw nw ae
          pure (HMap.bits (hbits av).toSigned)
      | _ => .error .notSupported
  | .system_tf_call .unsigned aes =>
      match aes with
      | [ae] => do
          let av ← evalExpr decls funcs ctxs cpos ifw nw ae
          pure (HMap.bits (hbits av).toUnsigned)
      | _ => .error .notSupported
  | .cast sze e => do
      let szv ← evalExpr decls funcs ctxs cpos ifw nw sze
      let ev ← evalExpr decls funcs ctxs cpos ifw nw e
      pure (HMap.bits (SZ.castV (hbits szv) (hbits ev)))
  | .unary_op op e => do
      let ev ← evalExpr decls funcs ctxs cpos ifw nw e
      pure (HMap.bits (uniOpFunc op (hbits ev)))
  | .inc_or_dec (.inc vid) => do
      let v ← wfind decls ifw nw vid
      pure (HMap.bits (SZ.bAdd (hbits v) (SZ.mk' 1 (hbits v).width false)))
  | .inc_or_dec (.dec vid) => do
      let v ← wfind decls ifw nw vid
      pure (HMap.bits (SZ.bSub (hbits v) (SZ.mk' 1 (hbits v).width false)))
  | .binary_op op le re => do
      let lv ← evalExpr decls funcs ctxs cpos ifw nw le
      let rv ← evalExpr decls funcs ctxs cpos ifw nw re
      pure (HMap.bits (binOpFunc op (hbits lv) (hbits rv)))
  | .cond ce te fe => do
      let cv ← evalExpr decls funcs ctxs cpos ifw nw ce
      let tv ← evalExpr decls funcs ctxs cpos ifw nw te
      let fv ← evalExpr decls funcs ctxs cpos ifw nw fe
      if (hbits cv).isZero then pure fv else pure tv
  | .inside ie res => do
      let iv ← evalExpr decls funcs ctxs cpos ifw nw ie
      let rvs ← evalExprList decls funcs ctxs cpos ifw nw res
      let isz := hbits iv
      let isMatch := rvs.any (fun rv => SZ.equiv isz (hbits rv))
      if isMatch
        then pure (HMap.bits (SZ.mk' 1 1 false))
        else pure (HMap.bits (SZ.mk' 0 1 false))

def evalExprList (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : List expression → trsOk (List Value)
  | [] => .ok []
  | e :: es => do
      let v ← evalExpr decls funcs ctxs cpos ifw nw e
      let vs ← evalExprList decls funcs ctxs cpos ifw nw es
      pure (v :: vs)

def lvposfind (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : expression → trsOk HPath
  | .ident vid => declfind decls vid
  | .hierarchical_ident pe ce => do
      let pp ← lvposfind decls funcs ctxs cpos ifw nw pe
      let cvid ← getAccessVid ce
      pure (pp ++ [HElt.vid cvid])
  | .select te se => do
      let pp ← lvposfind decls funcs ctxs cpos ifw nw te
      let sv ← evalExpr decls funcs ctxs cpos ifw nw se
      pure (pp ++ [HElt.ind (hbits sv)])
  | _ => .error .notSupported

end

-- ## nfupds / pnfupds — state update helpers

-- Update (nw, flops) triple using result of an assignment.
def nfupds (nfr1 nfr2 : NW × Flops) : NW × Flops :=
  (hupds nfr1.1 nfr2.1, hupds nfr1.2 nfr2.2)

-- Predicate-filtered update of (nw, flops).
def pnfupds (p : VId → Bool) (nfr1 nfr2 : NW × Flops) : NW × Flops :=
  (phupds p nfr1.1 nfr2.1, phupds p nfr1.2 nfr2.2)

-- ## Assignment processing

def trsVAssign (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : assign → trsOk NW
  | .net lv e => do
      let p ← lvposfind decls funcs ctxs cpos ifw nw lv
      let v ← evalExpr decls funcs ctxs cpos ifw nw e
      let dv := hfind decls p
      let cv := HMap.bits (SZ.castD (hbits dv) (hbits v))
      pure (hadd nw p cv)

def trsVAssigns (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : assigns → trsOk NW
  | .one a => trsVAssign decls funcs ctxs cpos ifw nw a
  | .cons a as_ => do
      let nw' ← trsVAssign decls funcs ctxs cpos ifw nw a
      trsVAssigns decls funcs ctxs cpos ifw nw' as_

def trsVContAssign (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : cont_assign → trsOk NW
  | .net nas => trsVAssigns decls funcs ctxs cpos ifw nw nas

-- ## For-loop step helper (non-partial: only calls evalExpr/lvposfind)

def trsVForStep (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : for_step → trsOk NW
  | .op_assign (.op lv aop e) => do
      let p ← lvposfind decls funcs ctxs cpos ifw nw lv
      let ev ← evalExpr decls funcs ctxs cpos ifw nw e
      let dv := hfind decls p
      match assignOpToBinOp aop with
      | none =>
          let cv := HMap.bits (SZ.castD (hbits dv) (hbits ev))
          pure (hadd nw p cv)
      | some bop => do
          let lval ← match hfind2 p nw ifw with
            | some v => pure v
            | none => .error .undriven
          let result := binOpFunc bop (hbits lval) (hbits ev)
          let cv := HMap.bits (SZ.castD (hbits dv) result)
          pure (hadd nw p cv)
  | .inc_or_dec (.inc vid) => do
      let p ← declfind decls vid
      let v ← wfind decls ifw nw vid
      let dv := hfind decls p
      let result := SZ.bAdd (hbits v) (SZ.mk' 1 (hbits v).width false)
      let cv := HMap.bits (SZ.castD (hbits dv) result)
      pure (hadd nw p cv)
  | .inc_or_dec (.dec vid) => do
      let p ← declfind decls vid
      let v ← wfind decls ifw nw vid
      let dv := hfind decls p
      let result := SZ.bSub (hbits v) (SZ.mk' 1 (hbits v).width false)
      let cv := HMap.bits (SZ.castD (hbits dv) result)
      pure (hadd nw p cv)

-- ## Statement execution (mutual recursion)

mutual

/- Main statement interpreter.
   Returns (new wire values, flop updates, return value). -/
def trsVStatementItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (isComb : Bool) : statement_item → NW → trsOk (NW × Flops × Value)
  | .blocking_assign_normal lv e, nw => do
      let p ← lvposfind decls funcs ctxs cpos ifw nw lv
      let v ← evalExpr decls funcs ctxs cpos ifw nw e
      let dv := hfind decls p
      let cv := HMap.bits (SZ.castD (hbits dv) (hbits v))
      pure (hadd nw p cv, HMap.empty, HMap.empty)
  | .nonblocking_assign lv e, nw => do
      let p ← lvposfind decls funcs ctxs cpos ifw nw lv
      let v ← evalExpr decls funcs ctxs cpos ifw nw e
      let dv := hfind decls p
      let cv := HMap.bits (SZ.castD (hbits dv) (hbits v))
      if isComb
        then pure (hadd nw p cv, HMap.empty, HMap.empty)
        else pure (nw, hsingle p cv, HMap.empty)
  | .case _ ce css, nw => do
      let cv ← evalExpr decls funcs ctxs cpos ifw nw ce
      trsVStatementCaseV decls funcs ctxs cpos ifw isComb cv css nw
  | .cond cp ts fs, nw => do
      let cv ← evalExpr decls funcs ctxs cpos ifw nw cp
      if (hbits cv).isZero then
        match fs with
        | none => pure (nw, HMap.empty, HMap.empty)
        | some none => pure (nw, HMap.empty, HMap.empty)
        | some (some fsi) => trsVStatementItem decls funcs ctxs cpos ifw isComb fsi nw
      else
        match ts with
        | none => pure (nw, HMap.empty, HMap.empty)
        | some tsi => trsVStatementItem decls funcs ctxs cpos ifw isComb tsi nw
  | .forever _, nw => pure (nw, HMap.empty, HMap.empty)  -- skip
  | .repeat _ _, nw => pure (nw, HMap.empty, HMap.empty)  -- skip
  | .while _ _, nw => pure (nw, HMap.empty, HMap.empty)  -- skip
  | .do_while _ _, nw => pure (nw, HMap.empty, HMap.empty)  -- skip
  | .for (.var_assigns fias) ce step body, nw => do
      let nw' ← trsVAssigns decls funcs ctxs cpos ifw nw fias
      trsVStatementForLoop decls funcs ctxs cpos ifw isComb
        ce step body 32 nw' HMap.empty HMap.empty
  | .return re, nw => do
      let rv ← evalExpr decls funcs ctxs cpos ifw nw re
      pure (nw, HMap.empty, rv)
  | .proc_timing_control _ si, nw =>
      trsVStatementItem decls funcs ctxs cpos ifw isComb si nw
  | .seq_block stis, nw =>
      trsVStatementSeqBlock decls funcs ctxs cpos ifw isComb stis nw HMap.empty HMap.empty

-- Process a case statement: find matching case item and execute.
def trsVStatementCaseV (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (isComb : Bool)
    (cv : Value) : List (case_item statement_item) → NW → trsOk (NW × Flops × Value)
  | [], nw => pure (nw, HMap.empty, HMap.empty)
  | (.default st) :: _, nw => trsVStatementItem decls funcs ctxs cpos ifw isComb st nw
  | (.case ce st) :: rest, nw => do
      let cev ← evalExpr decls funcs ctxs cpos ifw nw ce
      if SZ.equiv (hbits cv) (hbits cev)
        then trsVStatementItem decls funcs ctxs cpos ifw isComb st nw
        else trsVStatementCaseV decls funcs ctxs cpos ifw isComb cv rest nw

-- Evaluate a for-loop with bounded unrolling (max 2^5 = 32 iterations).
def trsVStatementForLoop (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (isComb : Bool)
    (ce : expression) (step : for_step) (body : statement_item)
    (fuel : Nat) (nw : NW) (flops : Flops) (retv : Value) : trsOk (NW × Flops × Value) :=
  match fuel with
  | 0 => pure (nw, flops, retv)
  | fuel' + 1 => do
    let cv ← evalExpr decls funcs ctxs cpos ifw nw ce
    if (hbits cv).isZero
      then pure (nw, flops, retv)
      else do
        let (nw', fl', rv') ← trsVStatementItem decls funcs ctxs cpos ifw isComb body nw
        let nw'' := hupds nw nw'
        let flops' := hupds flops fl'
        let retv' := if rv' == HMap.empty then retv else rv'
        -- apply step
        let nw''' ← trsVForStep decls funcs ctxs cpos ifw nw'' step
        trsVStatementForLoop decls funcs ctxs cpos ifw isComb ce step body
          fuel' nw''' flops' retv'

-- Execute a sequence of statements.
def trsVStatementSeqBlock (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (isComb : Bool) : List statement_item → NW → Flops → Value → trsOk (NW × Flops × Value)
  | [], nw', fl', rv' => pure (nw', fl', rv')
  | si :: rest, nw', fl', rv' => do
      let (nw'', fl'', rv'') ← trsVStatementItem decls funcs ctxs cpos ifw isComb si nw'
      let nwAcc := hupds nw' nw''
      let flAcc := hupds fl' fl''
      let rvAcc := if rv'' == HMap.empty then rv' else rv''
      trsVStatementSeqBlock decls funcs ctxs cpos ifw isComb rest nwAcc flAcc rvAcc

end

-- ## Declaration assignment processing

def trsVNetDeclAssign (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : net_decl_assign → trsOk NW
  | .net vid (some e) => do
      let p ← declfind decls vid
      let v ← evalExpr decls funcs ctxs cpos ifw nw e
      let dv := hfind decls p
      let cv := HMap.bits (SZ.castD (hbits dv) (hbits v))
      pure (hadd nw p cv)
  | .net _ none => pure nw

def trsVNetDeclAssigns (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : net_decl_assigns → trsOk NW
  | .one nda => trsVNetDeclAssign decls funcs ctxs cpos ifw nw nda
  | .cons nda ndas => do
      let nw' ← trsVNetDeclAssign decls funcs ctxs cpos ifw nw nda
      trsVNetDeclAssigns decls funcs ctxs cpos ifw nw' ndas

def trsVVarDeclAssign (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : var_decl_assign → trsOk NW
  | .var vid _ (some e) => do
      let p ← declfind decls vid
      let v ← evalExpr decls funcs ctxs cpos ifw nw e
      let dv := hfind decls p
      let cv := HMap.bits (SZ.castD (hbits dv) (hbits v))
      pure (hadd nw p cv)
  | .var _ _ none => pure nw

def trsVVarDeclAssigns (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : var_decl_assigns → trsOk NW
  | .one vda => trsVVarDeclAssign decls funcs ctxs cpos ifw nw vda
  | .cons vda vdas => do
      let nw' ← trsVVarDeclAssign decls funcs ctxs cpos ifw nw vda
      trsVVarDeclAssigns decls funcs ctxs cpos ifw nw' vdas

def trsVParamAssign (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : param_assign → trsOk NW
  | .param pid (.min_typ_max ce) => do
      let p ← declfind decls pid
      let v ← evalExpr decls funcs ctxs cpos ifw nw ce
      let dv := hfind decls p
      let cv := HMap.bits (SZ.castD (hbits dv) (hbits v))
      pure (hadd nw p cv)

def trsVParamAssigns (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : param_assigns → trsOk NW
  | .one pa => trsVParamAssign decls funcs ctxs cpos ifw nw pa
  | .cons pa pas => do
      let nw' ← trsVParamAssign decls funcs ctxs cpos ifw nw pa
      trsVParamAssigns decls funcs ctxs cpos ifw nw' pas

-- ## Package / generate item declaration processing

def trsVPkgGenItemDecl (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : pkg_gen_item_decl → trsOk NW
  | .net (.net _ _ ndas) => trsVNetDeclAssigns decls funcs ctxs cpos ifw nw ndas
  | .data (.var_decl (.var _ vdas)) => trsVVarDeclAssigns decls funcs ctxs cpos ifw nw vdas
  | .param (.data _ pas) => trsVParamAssigns decls funcs ctxs cpos ifw nw pas
  | .local_param (.local _ pas) => trsVParamAssigns decls funcs ctxs cpos ifw nw pas
  | _ => pure nw

def trsVModuleCommonItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (isComb : Bool) : module_common_item → NW → trsOk (NW × Flops)
  | .decl (.pkg pgid), nw => do
      let nw' ← trsVPkgGenItemDecl decls funcs ctxs cpos ifw nw pgid
      pure (nw', HMap.empty)
  | .cont_assign ca, nw => do
      let nw' ← trsVContAssign decls funcs ctxs cpos ifw nw ca
      pure (nw', HMap.empty)
  | .always _ (.stmt si), nw => do
      let (nw', fl, _) ← trsVStatementItem decls funcs ctxs cpos ifw isComb si nw
      pure (nw', fl)
  | .initial (.stmt si), nw => do
      let (nw', fl, _) ← trsVStatementItem decls funcs ctxs cpos ifw isComb si nw
      pure (nw', fl)
  | .assert _, nw => pure (nw, HMap.empty)

-- ## Module instantiation

private def trsVModuleInsMTrsArgsOne (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) (mtrs : MTrs) : named_port_conn → trsOk (List Value)
  | .wildcard =>
      sfListMap (fun vid => sfOrReturn (wfind decls ifw nw vid) (pure HMap.empty) pure)
        mtrs.inputVids
  | .ident pid =>
      sfListMap (fun vid =>
        if vid == pid then sfOrReturn (wfind decls ifw nw pid) (pure HMap.empty) pure
        else pure HMap.empty) mtrs.inputVids
  | .expr pid e =>
      sfListMap (fun vid =>
        if vid == pid then sfOrReturn (evalExpr decls funcs ctxs cpos ifw nw e) (pure HMap.empty) pure
        else pure HMap.empty) mtrs.inputVids

def trsVModuleInsMTrsArgs (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) (mtrs : MTrs) : named_port_conns → trsOk (List Value)
  | .one npc => trsVModuleInsMTrsArgsOne decls funcs ctxs cpos ifw nw mtrs npc
  | .cons npc npcs => do
      let args1 ← trsVModuleInsMTrsArgsOne decls funcs ctxs cpos ifw nw mtrs npc
      let args2 ← trsVModuleInsMTrsArgs decls funcs ctxs cpos ifw nw mtrs npcs
      pure (args1.zipWith hupds args2)

def trsVModuleInsMTrs (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) : module_ins → NW → trsOk (NW × Flops)
  | .module mid _ (.hier iid (.named npcs)), nw => do
      let mtrs ← mtrss mid
      let args ← trsVModuleInsMTrsArgs decls funcs ctxs cpos ifw nw mtrs npcs
      let inputState := buildFInputState mtrs.inputVids args
      let flopState := haccess flops iid
      let (newWires, newFlops) := mtrs.func inputState flopState
      -- write outputs to enclosing nw
      let nw' := mtrs.outputVids.foldl (fun acc ovid =>
        let ov := haccess newWires ovid
        match hpos ovid (hstr decls) with
        | some p => hadd acc p ov
        | none => acc) nw
      pure (nw', HMap.str [(iid, newFlops)])

def trsVModuleIns (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) : module_ins → NW → trsOk (NW × Flops)
  | mi, nw => trsVModuleInsMTrs decls funcs mtrss ctxs cpos ifw flops mi nw

def trsVModuleOrGenerateItem (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) (isComb : Bool) : module_or_generate_item → NW → trsOk (NW × Flops)
  | .common ci, nw => trsVModuleCommonItem decls funcs ctxs cpos ifw isComb ci nw
  | .ins mi, nw => trsVModuleIns decls funcs mtrss ctxs cpos ifw flops mi nw

-- ## iffupds — update IFW and flops

def iffupds (iff1 iff2 : IFF) : IFF :=
  (hupds iff1.1 iff2.1, hupds iff1.2 iff2.2)

-- ## Generate module items

mutual
def trsVGenerateModuleItem (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) (isComb : Bool) : generate_module_item → NW → trsOk (NW × Flops)
  | .module mogi, nw => trsVModuleOrGenerateItem decls funcs mtrss ctxs cpos ifw flops isComb mogi nw
  | .cond ce tgmi fgmi, nw => do
      let cv ← evalExpr decls funcs ctxs cpos ifw nw ce
      if (hbits cv).isZero then
        match fgmi with
        | none => pure (nw, HMap.empty)
        | some fgmi' => trsVGenerateModuleItem decls funcs mtrss ctxs cpos ifw flops isComb fgmi' nw
      else
        trsVGenerateModuleItem decls funcs mtrss ctxs cpos ifw flops isComb tgmi nw
  | .block gmis, nw =>
      trsVGenerateModuleItemList decls funcs mtrss ctxs cpos ifw flops isComb gmis nw

def trsVGenerateModuleItemList (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) (isComb : Bool) : List generate_module_item → NW → trsOk (NW × Flops)
  | [], _ => .ok (HMap.empty, HMap.empty)
  | gmi :: rest, nw => do
      let b ← trsVGenerateModuleItem decls funcs mtrss ctxs cpos ifw flops isComb gmi nw
      let nw' := hupds nw b.1
      let brest ← trsVGenerateModuleItemList decls funcs mtrss ctxs cpos ifw flops isComb rest nw'
      pure (nfupds b brest)
end

-- ## Non-port module items / module items

def trsVNonPortModuleItem (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) (isComb : Bool) : non_port_module_item → NW → trsOk (NW × Flops)
  | .generated_module_ins (.generated gmi), nw =>
      trsVGenerateModuleItem decls funcs mtrss ctxs cpos ifw flops isComb gmi nw
  | .module_or_generate_item mogi, nw =>
      trsVModuleOrGenerateItem decls funcs mtrss ctxs cpos ifw flops isComb mogi nw

def trsVModuleItem (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) (isComb : Bool) : module_item → NW → trsOk (NW × Flops)
  | .port_decl _, nw => pure (nw, HMap.empty)
  | .non_port np, nw => trsVNonPortModuleItem decls funcs mtrss ctxs cpos ifw flops isComb np nw

def trsVModuleItems (decls : Decls) (funcs : Funcs) (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops) (isComb : Bool) : module_items → NW → trsOk (NW × Flops)
  | .one mi, nw => trsVModuleItem decls funcs mtrss ctxs cpos ifw flops isComb mi nw
  | .cons mi mis, nw => do
      let (nw', fl') ← trsVModuleItem decls funcs mtrss ctxs cpos ifw flops isComb mi nw
      let (nw'', fl'') ← trsVModuleItems decls funcs mtrss ctxs cpos ifw flops isComb mis (hupds nw nw')
      pure (hupds nw' nw'', hupds fl' fl'')

-- ## Parameter port processing

def trsVParamDecl (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : param_decl → trsOk NW
  | .data _ pas => trsVParamAssigns decls funcs ctxs cpos ifw nw pas

def trsVParamPorts (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (nw : NW) : param_ports → trsOk NW
  | .nil => pure nw
  | .one pd => trsVParamDecl decls funcs ctxs cpos ifw nw pd
  | .cons pd pds => do
      let nw' ← trsVParamDecl decls funcs ctxs cpos ifw nw pd
      trsVParamPorts decls funcs ctxs cpos ifw nw' pds

-- ## Module declaration — building the transition function

def trsVModuleDecl (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl) : State → State → trsOk (NW × Flops) :=
  match m with
  | .ansi _ pps _ mitems => fun ifw flops => do
      let nw0 ← trsVParamPorts decls funcs ctxs cpos ifw HMap.empty pps
      trsVModuleItems decls funcs mtrss ctxs cpos ifw flops true mitems nw0

-- Build the IFF (combined IFW × Flops) transition.
def trsVModuleDecl_IFF (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl) : IFF → trsOk IFF :=
  fun (ifw, flops) => do
    let (nw, fl) ← trsVModuleDecl mtrss ctxs cpos decls funcs m ifw flops
    pure (hupds ifw nw, hupds flops fl)

-- ## Fixed-point iteration (trsM_iff_rep)

-- Apply the IFF transition `n` times, feeding output back as input.
def trsM_iff_rep (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl) : Nat → IFF → trsOk IFF
  | 0, iff_ => pure iff_
  | n + 1, iff_ => do
      let iff' ← trsVModuleDecl_IFF mtrss ctxs cpos decls funcs m iff_
      trsM_iff_rep mtrss ctxs cpos decls funcs m n iff'

-- Build the final MTrs for a module: iterate until convergence (5 iterations).
def trsM_IFF (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl) : IFF → trsOk IFF :=
  trsM_iff_rep mtrss ctxs cpos decls funcs m 5

-- ## trsNext / trsT — compute next state and extract output

def trsNext (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl)
    (inputs : State) (flops : Flops) : trsOk (State × Flops) := do
  let ifw := hupds flops inputs
  let (ifw', flops') ← trsM_IFF mtrss ctxs cpos decls funcs m (ifw, flops)
  pure (ifw', flops')

def trsT (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl)
    (outputVids : List VId) (inputs : State) (flops : Flops) : trsOk (State × Flops) := do
  let (ifw', flops') ← trsNext mtrss ctxs cpos decls funcs m inputs flops
  pure (hfilter outputVids ifw', flops')

-- ## Declaration collection

def declsVNetDeclAssigns (evalE : expression → trsOk Value) (pd : packed_dims) :
    net_decl_assigns → trsOk (List (VId × Value))
  | .one (.net vid _) => do
      let dv ← declPortType evalE (.port (some .wire) pd)
      pure [(vid, dv)]
  | .cons (.net vid _) ndas => do
      let dv ← declPortType evalE (.port (some .wire) pd)
      let rest ← declsVNetDeclAssigns evalE pd ndas
      pure ((vid, dv) :: rest)

def declsVVarDeclAssign (evalE : expression → trsOk Value) (dt : data_type) :
    var_decl_assign → trsOk (VId × Value)
  | .var vid vd _ => do
      let basev ← declDataType evalE dt
      -- handle unpacked dimensions
      let dv ← match vd with
        | .nil => pure basev
        | _ => pure basev  -- simplified: unpacked dims not fully handled
      pure (vid, dv)

def declsVVarDeclAssigns (evalE : expression → trsOk Value) (dt : data_type) :
    var_decl_assigns → trsOk (List (VId × Value))
  | .one vda => do let r ← declsVVarDeclAssign evalE dt vda; pure [r]
  | .cons vda vdas => do
      let r ← declsVVarDeclAssign evalE dt vda
      let rest ← declsVVarDeclAssigns evalE dt vdas
      pure (r :: rest)

def declsVParamAssign (evalE : expression → trsOk Value) (dti : data_type_or_implicit) :
    param_assign → trsOk (VId × Value)
  | .param pid _ => do
      let dv ← declDataTypeOrImplicit evalE dti
      pure (pid, dv)

def declsVParamAssigns (evalE : expression → trsOk Value) (dti : data_type_or_implicit) :
    param_assigns → trsOk (List (VId × Value))
  | .one pa => do let r ← declsVParamAssign evalE dti pa; pure [r]
  | .cons pa pas => do
      let r ← declsVParamAssign evalE dti pa
      let rest ← declsVParamAssigns evalE dti pas
      pure (r :: rest)

def declsVPkgGenItemDecl (evalE : expression → trsOk Value) : pkg_gen_item_decl → trsOk (List (VId × Value))
  | .net (.net _ pd ndas) => declsVNetDeclAssigns evalE pd ndas
  | .data (.var_decl (.var dt vdas)) => declsVVarDeclAssigns evalE dt vdas
  | .param (.data dti pas) => declsVParamAssigns evalE dti pas
  | .local_param (.local dti pas) => declsVParamAssigns evalE dti pas
  | _ => pure []

def declsVModuleCommonItem (evalE : expression → trsOk Value) : module_common_item → trsOk (List (VId × Value))
  | .decl (.pkg pgid) => declsVPkgGenItemDecl evalE pgid
  | _ => pure []

def declsVModuleOrGenerateItem (evalE : expression → trsOk Value) : module_or_generate_item → trsOk (List (VId × Value))
  | .common ci => declsVModuleCommonItem evalE ci
  | .ins _ => pure []

mutual
def declsVGenerateModuleItem (evalE : expression → trsOk Value) : generate_module_item → trsOk (List (VId × Value))
  | .module mogi => declsVModuleOrGenerateItem evalE mogi
  | .cond _ tgmi fgmi => do
      let td ← declsVGenerateModuleItem evalE tgmi
      let fd ← match fgmi with
        | none => pure []
        | some fgmi' => declsVGenerateModuleItem evalE fgmi'
      pure (td ++ fd)
  | .block gmis => declsVGenerateModuleItemList evalE gmis

def declsVGenerateModuleItemList (evalE : expression → trsOk Value) : List generate_module_item → trsOk (List (VId × Value))
  | [] => pure []
  | gmi :: rest => do
      let d ← declsVGenerateModuleItem evalE gmi
      let rest' ← declsVGenerateModuleItemList evalE rest
      pure (d ++ rest')
end

def declsVNonPortModuleItem (evalE : expression → trsOk Value) : non_port_module_item → trsOk (List (VId × Value))
  | .generated_module_ins (.generated gmi) => declsVGenerateModuleItem evalE gmi
  | .module_or_generate_item mogi => declsVModuleOrGenerateItem evalE mogi

def declsVModuleItem (evalE : expression → trsOk Value) : module_item → trsOk (List (VId × Value))
  | .port_decl _ => pure []
  | .non_port np => declsVNonPortModuleItem evalE np

def declsVModuleItems (evalE : expression → trsOk Value) : module_items → trsOk (List (VId × Value))
  | .one mi => declsVModuleItem evalE mi
  | .cons mi mis => do
      let d ← declsVModuleItem evalE mi
      let rest ← declsVModuleItems evalE mis
      pure (d ++ rest)

def declsVParamDecl (evalE : expression → trsOk Value) : param_decl → trsOk (List (VId × Value))
  | .data dti pas => declsVParamAssigns evalE dti pas

def declsVParamPorts (evalE : expression → trsOk Value) : param_ports → trsOk (List (VId × Value))
  | .nil => pure []
  | .one pd => declsVParamDecl evalE pd
  | .cons pd pds => do
      let d ← declsVParamDecl evalE pd
      let rest ← declsVParamPorts evalE pds
      pure (d ++ rest)

def declsVAnsiPortDecl (evalE : expression → trsOk Value) : ansi_port_decl → trsOk (List (VId × Value))
  | .net (some (.net _ pt)) pid => do
      let dv ← declPortType evalE pt
      pure [(pid, dv)]
  | .net none pid => pure [(pid, HMap.bits (SZ.mk' 0 1 false))]
  | .var (some (.var _ dt)) pid => do
      let dv ← declDataType evalE dt
      pure [(pid, dv)]
  | .var none pid => pure [(pid, HMap.bits (SZ.mk' 0 1 false))]

def declsVAnsiPortDecls (evalE : expression → trsOk Value) : ansi_port_decls → trsOk (List (VId × Value))
  | .nil => pure []
  | .one apd => declsVAnsiPortDecl evalE apd
  | .cons apd apds => do
      let d ← declsVAnsiPortDecl evalE apd
      let rest ← declsVAnsiPortDecls evalE apds
      pure (d ++ rest)

def declsVModuleDecl (evalE : expression → trsOk Value) : module_decl → trsOk Decls
  | .ansi _ pps pdecls mitems => do
      let ppd ← declsVParamPorts evalE pps
      let apd ← declsVAnsiPortDecls evalE pdecls
      let mid ← declsVModuleItems evalE mitems
      pure (HMap.str (ppd ++ apd ++ mid))

-- ## Function collection

def funcsVFuncDecl (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    func_decl → trsOk (VId × Func)
  | .func _dti fid ports (.stmt si) => do
      -- Build input vid list from ports
      let inputVids := funcsPortVids ports
      -- Build the function
      let f : Func := {
        inputVids := inputVids
        func := fun inputState =>
          let ifw := hupds decls inputState
          match trsVStatementItem decls funcs ctxs cpos ifw true si HMap.empty with
          | .ok (_, _, rv) => rv
          | .error _ => HMap.empty
      }
      pure (fid, f)
where
  funcsPortVids : ansi_port_decls → List VId
    | .nil => []
    | .one (.net _ pid) => [pid]
    | .one (.var _ pid) => [pid]
    | .cons (.net _ pid) rest => pid :: funcsPortVids rest
    | .cons (.var _ pid) rest => pid :: funcsPortVids rest

def funcsVPkgGenItemDecl (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    pkg_gen_item_decl → trsOk (List (VId × Func))
  | .func fd => do let r ← funcsVFuncDecl decls funcs ctxs cpos fd; pure [r]
  | _ => pure []

def funcsVModuleCommonItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    module_common_item → trsOk (List (VId × Func))
  | .decl (.pkg pgid) => funcsVPkgGenItemDecl decls funcs ctxs cpos pgid
  | _ => pure []

def funcsVModuleOrGenerateItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    module_or_generate_item → trsOk (List (VId × Func))
  | .common ci => funcsVModuleCommonItem decls funcs ctxs cpos ci
  | .ins _ => pure []

mutual
def funcsVGenerateModuleItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    generate_module_item → trsOk (List (VId × Func))
  | .module mogi => funcsVModuleOrGenerateItem decls funcs ctxs cpos mogi
  | .cond _ tgmi fgmi => do
      let td ← funcsVGenerateModuleItem decls funcs ctxs cpos tgmi
      let fd ← match fgmi with
        | none => pure []
        | some fgmi' => funcsVGenerateModuleItem decls funcs ctxs cpos fgmi'
      pure (td ++ fd)
  | .block gmis => funcsVGenerateModuleItemList decls funcs ctxs cpos gmis

def funcsVGenerateModuleItemList (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    List generate_module_item → trsOk (List (VId × Func))
  | [] => pure []
  | gmi :: rest => do
      let d ← funcsVGenerateModuleItem decls funcs ctxs cpos gmi
      let rest' ← funcsVGenerateModuleItemList decls funcs ctxs cpos rest
      pure (d ++ rest')
end

def funcsVNonPortModuleItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    non_port_module_item → trsOk (List (VId × Func))
  | .generated_module_ins (.generated gmi) => funcsVGenerateModuleItem decls funcs ctxs cpos gmi
  | .module_or_generate_item mogi => funcsVModuleOrGenerateItem decls funcs ctxs cpos mogi

def funcsVModuleItem (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    module_item → trsOk (List (VId × Func))
  | .port_decl _ => pure []
  | .non_port np => funcsVNonPortModuleItem decls funcs ctxs cpos np

def funcsVModuleItems (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath) :
    module_items → trsOk (List (VId × Func))
  | .one mi => funcsVModuleItem decls funcs ctxs cpos mi
  | .cons mi mis => do
      let d ← funcsVModuleItem decls funcs ctxs cpos mi
      let rest ← funcsVModuleItems decls funcs ctxs cpos mis
      pure (d ++ rest)

def funcsVModuleDecl (decls : Decls) (ctxs : State) (cpos : HPath) (m : module_decl) : Funcs :=
  match m with
  | .ansi _ _ _ mitems =>
      let funcList := match funcsVModuleItems decls fmapEmpty ctxs cpos mitems with
        | .ok fl => fl
        | .error _ => []
      funcList.foldl (fun acc (vid, f) => fmapMerge (fmapSingle vid f) acc) fmapEmpty

-- ## Parameter ports — with module-level context

def declsVParamPortsM (evalE : expression → trsOk Value) (m : module_decl) : trsOk (List (VId × Value)) :=
  match m with
  | .ansi _ pps _ _ => declsVParamPorts evalE pps

def trsVParamPortsM (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (m : module_decl) : trsOk NW :=
  match m with
  | .ansi _ pps _ _ => trsVParamPorts decls funcs ctxs cpos ifw HMap.empty pps

end VerilLean.Lang.Semantics
