/- # STF Semantic Bridge.
   Connects abstract `stf_iterate` to concrete `trsVModuleItems`. -/

import VerilLean.Lib.Lib
import VerilLean.Lib.HMapLemmas
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Analysis
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame
import VerilLean.Lang.Equiv.Confluence
import VerilLean.Lang.Equiv.StfTopological

namespace VerilLean.Lang.Equiv.Bridge

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck
  (CombProcess getProcessesFromModuleItem getProcessesFromModuleItems)
open VerilLean.Lang.Equiv.Standard (ExecProcess ProcExec)
open VerilLean.Lang.Equiv.EvalFrame (CompatUpdate)
open VerilLean.Lang.Equiv.StfTopological (stf_iterate stf_iterate_n stf_converges)
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

-- ## Part 1: Building ExecProcess list from module_items

/- Convert a single module_item to an ExecProcess.

    The `proc` field merges all CombProcess entries returned by
    `getProcessesFromModuleItem` (which may return multiple processes for
    e.g. multiple continuous assigns within a single module_item).

    The `exec` field wraps `trsVModuleItem`: given the current wire state
    `nw`, it returns the delta (new wire values) produced by this item.
    The flop updates are discarded since we target combinational logic only. -/
def moduleItemToExecProcess (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    (mi : module_item) : ExecProcess :=
  let procs := getProcessesFromModuleItem mi
  { proc := { reads := procs.flatMap (·.reads)
              writes := procs.flatMap (·.writes)
              isComb := procs.any (·.isComb) }
    exec := fun nw =>
      match trsVModuleItem decls funcs mtrss ctxs cpos ifw flops true mi nw with
      | .ok (delta_nw, _fl) => .ok delta_nw
      | .error e => .error e }

-- Convert module_items to a list of ExecProcess.
def buildExecProcessesFromItems (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    : module_items → List ExecProcess
  | .one mi => [moduleItemToExecProcess decls funcs mtrss ctxs cpos ifw flops mi]
  | .cons mi mis =>
      moduleItemToExecProcess decls funcs mtrss ctxs cpos ifw flops mi
        :: buildExecProcessesFromItems decls funcs mtrss ctxs cpos ifw flops mis

/- Extract all ExecProcesses from a module declaration.
    Parameter ports are evaluated first to produce the initial nw0, which is
    threaded through as the initial state in the STF iteration. -/
def buildExecProcesses (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    (m : module_decl) : List ExecProcess :=
  match m with
  | .ansi _ _ _ mitems =>
    buildExecProcessesFromItems decls funcs mtrss ctxs cpos ifw flops mitems

-- ## Part 2: Accumulating version of trsVModuleItems

/- Accumulating version of `trsVModuleItems` that returns the accumulated
    state (not the delta). This matches the behavior of `stf_iterate`.

    trsVModuleItems_acc ... items acc = .ok (acc', fl)
    where acc' = hupds (hupds ... (hupds acc d1) d2) ... dn
    and the di are the per-item deltas. -/
def trsVModuleItems_acc (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops) (isComb : Bool)
    : module_items → NW → trsOk (NW × Flops)
  | .one mi, acc => do
      let (d, f) ← trsVModuleItem decls funcs mtrss ctxs cpos ifw flops isComb mi acc
      pure (hupds acc d, f)
  | .cons mi mis, acc => do
      let (d, f) ← trsVModuleItem decls funcs mtrss ctxs cpos ifw flops isComb mi acc
      let (acc', f') ← trsVModuleItems_acc decls funcs mtrss ctxs cpos ifw flops isComb mis (hupds acc d)
      pure (acc', hupds f f')

-- ## Part 3: Single-iteration equivalence — helper lemmas

/- Helper: the exec field of moduleItemToExecProcess relates to trsVModuleItem.
    This factors out the match-on-result pattern. -/
private theorem exec_eq_map_fst (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    (mi : module_item) (nw : NW) :
    (moduleItemToExecProcess decls funcs mtrss ctxs cpos ifw flops mi).exec nw =
    (trsVModuleItem decls funcs mtrss ctxs cpos ifw flops true mi nw).map Prod.fst := by
  simp only [moduleItemToExecProcess]
  cases h : trsVModuleItem decls funcs mtrss ctxs cpos ifw flops true mi nw with
  | error e => simp [Except.map]
  | ok val => obtain ⟨d, f⟩ := val; simp [Except.map]

-- Helper: stf_iterate on a singleton list.
private theorem stf_iterate_singleton (ep : ExecProcess) (s : State) :
    stf_iterate [ep] s = (do let u ← ep.exec s; pure (hupds s u)) := by
  show [ep].foldlM (fun acc ep => do let u ← ep.exec acc; pure (hupds acc u)) s = _
  simp only [List.foldlM]
  cases ep.exec s with
  | error e => rfl
  | ok u => rfl

-- Helper: stf_iterate on a cons list unfolds to one step then the rest.
private theorem stf_iterate_cons (ep : ExecProcess) (rest : List ExecProcess) (s : State) :
    stf_iterate (ep :: rest) s =
      (do let u ← ep.exec s; stf_iterate rest (hupds s u)) := by
  show (ep :: rest).foldlM (fun acc ep => do let u ← ep.exec acc; pure (hupds acc u)) s = _
  simp only [List.foldlM]
  cases ep.exec s with
  | error e => rfl
  | ok u => rfl

-- ## Part 3: Single-iteration equivalence (using accumulating version)

/- Single-iteration equivalence between abstract stf_iterate and concrete
    trsVModuleItems_acc (the accumulating version).

    stf_iterate returns the accumulated state, and so does trsVModuleItems_acc.
    The relationship is direct:

      stf_iterate procs acc = (trsVModuleItems_acc ... items acc).map Prod.fst

    Proof by induction on module_items. No hupds_assoc needed! -/
theorem stf_iterate_eq_trsVModuleItems_acc
    (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    (items : module_items) (acc : NW) :
    stf_iterate
      (buildExecProcessesFromItems decls funcs mtrss ctxs cpos ifw flops items) acc =
    (trsVModuleItems_acc decls funcs mtrss ctxs cpos ifw flops true items acc).map
      Prod.fst := by
  induction items generalizing acc with
  | one mi =>
    rw [buildExecProcessesFromItems, stf_iterate_singleton, exec_eq_map_fst]
    simp only [trsVModuleItems_acc]
    cases h : trsVModuleItem decls funcs mtrss ctxs cpos ifw flops true mi acc with
    | error e => simp [bind, Except.bind, Except.map]
    | ok val =>
      obtain ⟨delta, fl⟩ := val
      simp [bind, Except.bind, Except.map, pure, Except.pure]
  | cons mi mis ih =>
    cases h1 : trsVModuleItem decls funcs mtrss ctxs cpos ifw flops true mi acc with
    | error e =>
      show stf_iterate (buildExecProcessesFromItems decls funcs mtrss ctxs cpos ifw flops
            (.cons mi mis)) acc = _
      unfold buildExecProcessesFromItems
      unfold stf_iterate
      simp only [moduleItemToExecProcess, h1, trsVModuleItems_acc, List.foldlM, Except.map]
      rfl
    | ok val1 =>
      obtain ⟨d1, f1⟩ := val1
      show stf_iterate (buildExecProcessesFromItems decls funcs mtrss ctxs cpos ifw flops
            (.cons mi mis)) acc = _
      unfold buildExecProcessesFromItems
      unfold stf_iterate
      simp only [moduleItemToExecProcess, h1, trsVModuleItems_acc, List.foldlM, Except.map,
                  Except.bind, pure, Except.pure, bind]
      change stf_iterate (buildExecProcessesFromItems decls funcs mtrss ctxs cpos ifw flops mis) (hupds acc d1) = _
      rw [ih (hupds acc d1)]
      cases h2 : trsVModuleItems_acc decls funcs mtrss ctxs cpos ifw flops true mis (hupds acc d1) with
      | error e => rfl
      | ok val2 =>
        obtain ⟨acc', f2⟩ := val2
        simp [Except.map]

-- ## Part 4: Connection to trsVModuleDecl

/- One STF iteration via abstract processes equals one concrete module evaluation
    (via the accumulating trsVModuleItems_acc).

    trsVModuleDecl first evaluates parameter ports to get nw0, then calls
    trsVModuleItems. The abstract stf_iterate operates on buildExecProcesses
    starting from nw0. -/
theorem stf_iterate_eq_trsVModuleDecl_acc
    (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    (m : module_decl) (nw0 : NW)
    (hpps : match m with
      | .ansi _ pps _ _ => trsVParamPorts decls funcs ctxs cpos ifw HMap.empty pps = .ok nw0) :
    stf_iterate
      (buildExecProcesses decls funcs mtrss ctxs cpos ifw flops m) nw0 =
    (match m with
     | .ansi _ _ _ mitems =>
       trsVModuleItems_acc decls funcs mtrss ctxs cpos ifw flops true mitems nw0).map
      Prod.fst := by
  match m with
  | .ansi _name pps _ports mitems =>
    exact stf_iterate_eq_trsVModuleItems_acc decls funcs mtrss ctxs cpos ifw flops mitems nw0

-- ## Part 5: Convergence bridge

/- Helper: trsVModuleDecl_IFF fixed-point implies trsVModuleItems produces a
    delta that, when merged with sf_ifw, gives sf_ifw back. -/
private theorem fixed_point_delta
    (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (decls : Decls) (funcs : Funcs) (m : module_decl)
    (sf_ifw : IFW) (sf_fl : Flops)
    (hfix : trsVModuleDecl_IFF mtrss ctxs cpos decls funcs m (sf_ifw, sf_fl) = .ok (sf_ifw, sf_fl)) :
    ∃ nw fl, trsVModuleDecl mtrss ctxs cpos decls funcs m sf_ifw sf_fl = .ok (nw, fl) ∧
      hupds sf_ifw nw = sf_ifw ∧ hupds sf_fl fl = sf_fl := by
  simp only [trsVModuleDecl_IFF] at hfix
  cases hd : trsVModuleDecl mtrss ctxs cpos decls funcs m sf_ifw sf_fl with
  | error e =>
    simp [hd, bind, Except.bind] at hfix
  | ok val =>
    obtain ⟨nw, fl⟩ := val
    simp [hd, bind, Except.bind, pure, Except.pure] at hfix
    exact ⟨nw, fl, rfl, hfix.1, hfix.2⟩

end VerilLean.Lang.Equiv.Bridge
