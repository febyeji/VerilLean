-- Static analysis predicates for module equivalence checking.

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Analysis
import VerilLean.Lang.Semantics

namespace VerilLean.Lang.Equiv.StaticCheck

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lib

-- ## Part 1: Read/Write Set Computation

mutual

-- Variables read by an expression (syntactic approximation).
def exprReads : expression → List VId
  | .primary_literal _ => []
  | .ident n => [n]
  | .hierarchical_ident pe ce => exprReads pe ++ exprReads ce
  | .select te se => exprReads te ++ exprReads se
  | .select_const_range se lr rr => exprReads se ++ exprReads lr ++ exprReads rr
  | .select_indexed_range_add se lr rr => exprReads se ++ exprReads lr ++ exprReads rr
  | .select_indexed_range_sub se lr rr => exprReads se ++ exprReads lr ++ exprReads rr
  | .concat es => exprListReads es
  | .mult_concat ne ces => exprReads ne ++ exprListReads ces
  | .tf_call _tfid aes => exprListReads aes
  | .system_tf_call _ aes => exprListReads aes
  | .cast sze e => exprReads sze ++ exprReads e
  | .unary_op _ e => exprReads e
  | .inc_or_dec (.inc vid) => [vid]
  | .inc_or_dec (.dec vid) => [vid]
  | .binary_op _ le re => exprReads le ++ exprReads re
  | .cond ce te fe => exprReads ce ++ exprReads te ++ exprReads fe
  | .inside ie res => exprReads ie ++ exprListReads res

-- Reads for a list of expressions.
def exprListReads : List expression → List VId
  | [] => []
  | e :: es => exprReads e ++ exprListReads es

/- Extract reads from the index expressions in an lvalue.
    The target variable itself is a write, not a read. -/
def lvalueReads : expression → List VId
  | .ident _ => []
  | .hierarchical_ident pe _ce => lvalueReads pe
  | .select te se => lvalueReads te ++ exprReads se
  | .select_const_range se lr rr => lvalueReads se ++ exprReads lr ++ exprReads rr
  | .select_indexed_range_add se lr rr => lvalueReads se ++ exprReads lr ++ exprReads rr
  | .select_indexed_range_sub se lr rr => lvalueReads se ++ exprReads lr ++ exprReads rr
  | e => exprReads e

-- Extract the target variable name(s) from an lvalue expression.
def lvalueTarget : expression → List VId
  | .ident n => [n]
  | .hierarchical_ident pe _ => lvalueTarget pe
  | .select te _ => lvalueTarget te
  | .select_const_range se _ _ => lvalueTarget se
  | .select_indexed_range_add se _ _ => lvalueTarget se
  | .select_indexed_range_sub se _ _ => lvalueTarget se
  | .concat es => lvalueTargetList es
  | _ => []

-- Targets for a list of expressions.
def lvalueTargetList : List expression → List VId
  | [] => []
  | e :: es => lvalueTarget e ++ lvalueTargetList es

end

-- Variables read by a single assign.
def assignReads : assign → List VId
  | .net lv e => lvalueReads lv ++ exprReads e

-- Variables read by an assigns chain.
def assignsReads : assigns → List VId
  | .one a => assignReads a
  | .cons a as_ => assignReads a ++ assignsReads as_

-- Variables written by a single assign.
def assignWrites : assign → List VId
  | .net lv _ => lvalueTarget lv

-- Variables written by an assigns chain.
def assignsWrites : assigns → List VId
  | .one a => assignWrites a
  | .cons a as_ => assignWrites a ++ assignsWrites as_

-- Variables read by an op_assign.
def opAssignReads : op_assign → List VId
  | .op lv _ e => lvalueReads lv ++ exprReads lv ++ exprReads e

-- Variables written by an op_assign.
def opAssignWrites : op_assign → List VId
  | .op lv _ _ => lvalueTarget lv

-- Variables read by a for_init.
def forInitReads : for_init → List VId
  | .var_assigns vas => assignsReads vas

-- Variables written by a for_init.
def forInitWrites : for_init → List VId
  | .var_assigns vas => assignsWrites vas

-- Variables read by a for_step.
def forStepReads : for_step → List VId
  | .op_assign oa => opAssignReads oa
  | .inc_or_dec (.inc vid) => [vid]
  | .inc_or_dec (.dec vid) => [vid]

-- Variables written by a for_step.
def forStepWrites : for_step → List VId
  | .op_assign oa => opAssignWrites oa
  | .inc_or_dec (.inc vid) => [vid]
  | .inc_or_dec (.dec vid) => [vid]

mutual

-- Variables read by a statement (syntactic).
def stmtReads : statement_item → List VId
  | .blocking_assign_normal vlv e => lvalueReads vlv ++ exprReads e
  | .nonblocking_assign vlv e => lvalueReads vlv ++ exprReads e
  | .case _ ce css => exprReads ce ++ caseItemListReads css
  | .cond cp ts fs =>
      exprReads cp ++
      (match ts with | some s => stmtReads s | none => []) ++
      (match fs with | some (some s) => stmtReads s | _ => [])
  | .forever s => stmtReads s
  | .repeat re s => exprReads re ++ stmtReads s
  | .while we s => exprReads we ++ stmtReads s
  | .for init ce step s => forInitReads init ++ exprReads ce ++ forStepReads step ++ stmtReads s
  | .do_while s we => stmtReads s ++ exprReads we
  | .return re => exprReads re
  | .proc_timing_control _ s => stmtReads s
  | .seq_block ss => stmtListReads ss

-- Reads for a list of case items.
def caseItemListReads : List (case_item statement_item) → List VId
  | [] => []
  | (.case ce' st) :: rest => exprReads ce' ++ stmtReads st ++ caseItemListReads rest
  | (.default st) :: rest => stmtReads st ++ caseItemListReads rest

-- Reads for a list of statements.
def stmtListReads : List statement_item → List VId
  | [] => []
  | s :: ss => stmtReads s ++ stmtListReads ss

-- Variables written by a statement (syntactic).
def stmtWrites : statement_item → List VId
  | .blocking_assign_normal vlv _ => lvalueTarget vlv
  | .nonblocking_assign vlv _ => lvalueTarget vlv
  | .case _ _ css => caseItemListWrites css
  | .cond _ ts fs =>
      (match ts with | some s => stmtWrites s | none => []) ++
      (match fs with | some (some s) => stmtWrites s | _ => [])
  | .forever s => stmtWrites s
  | .repeat _ s => stmtWrites s
  | .while _ s => stmtWrites s
  | .for init _ step s => forInitWrites init ++ forStepWrites step ++ stmtWrites s
  | .do_while s _ => stmtWrites s
  | .return _ => []
  | .proc_timing_control _ s => stmtWrites s
  | .seq_block ss => stmtListWrites ss

-- Writes for a list of case items.
def caseItemListWrites : List (case_item statement_item) → List VId
  | [] => []
  | (.case _ st) :: rest => stmtWrites st ++ caseItemListWrites rest
  | (.default st) :: rest => stmtWrites st ++ caseItemListWrites rest

-- Writes for a list of statements.
def stmtListWrites : List statement_item → List VId
  | [] => []
  | s :: ss => stmtWrites s ++ stmtListWrites ss

end

-- ## Part 2: Process Abstraction

-- A process is an abstraction of a module item that can be independently evaluated.
structure CombProcess where
  /-- Variables this process reads (sensitivity). -/
  reads : List VId
  /-- Variables this process writes. -/
  writes : List VId
  /-- Is this a combinational process? -/
  isComb : Bool
  deriving Repr, BEq

-- Extract reads from a named_port_conn.
def namedPortConnReads : named_port_conn → List VId
  | .ident pid => [pid]
  | .expr _ e => exprReads e
  | .wildcard => []

-- Extract reads from a named_port_conns structure.
def namedPortConnsReads : named_port_conns → List VId
  | .one npc => namedPortConnReads npc
  | .cons npc npcs => namedPortConnReads npc ++ namedPortConnsReads npcs

-- Extract writes from a named_port_conn.
def namedPortConnWrites : named_port_conn → List VId
  | .ident pid => [pid]
  | .expr pid _ => [pid]
  | .wildcard => []

-- Extract writes from a named_port_conns structure.
def namedPortConnsWrites : named_port_conns → List VId
  | .one npc => namedPortConnWrites npc
  | .cons npc npcs => namedPortConnWrites npc ++ namedPortConnsWrites npcs

-- Extract processes from assigns.
def getProcessesFromAssigns : assigns → List CombProcess
  | .one (.net lv e) =>
      [{ reads := exprReads e, writes := lvalueTarget lv, isComb := true }]
  | .cons (.net lv e) rest =>
      { reads := exprReads e, writes := lvalueTarget lv, isComb := true }
        :: getProcessesFromAssigns rest

-- Extract processes from net_decl_assigns.
def getProcessesFromNetDeclAssigns : net_decl_assigns → List CombProcess
  | .one (.net vid (some e)) =>
      [{ reads := exprReads e, writes := [vid], isComb := true }]
  | .one (.net _ none) => []
  | .cons (.net vid (some e)) rest =>
      { reads := exprReads e, writes := [vid], isComb := true }
        :: getProcessesFromNetDeclAssigns rest
  | .cons (.net _ none) rest => getProcessesFromNetDeclAssigns rest

-- Extract processes from var_decl_assigns.
def getProcessesFromVarDeclAssigns : var_decl_assigns → List CombProcess
  | .one (.var vid _ (some e)) =>
      [{ reads := exprReads e, writes := [vid], isComb := true }]
  | .one (.var _ _ none) => []
  | .cons (.var vid _ (some e)) rest =>
      { reads := exprReads e, writes := [vid], isComb := true }
        :: getProcessesFromVarDeclAssigns rest
  | .cons (.var _ _ none) rest => getProcessesFromVarDeclAssigns rest

-- Extract combinational processes from a single module_common_item.
def getProcessesFromModuleCommonItem : module_common_item → List CombProcess
  | .always .always_comb (.stmt si) =>
      [{ reads := stmtReads si, writes := stmtWrites si, isComb := true }]
  | .always .always_latch (.stmt si) =>
      [{ reads := stmtReads si, writes := stmtWrites si, isComb := true }]
  | .always .always_ff (.stmt si) =>
      [{ reads := stmtReads si, writes := stmtWrites si, isComb := false }]
  | .always .always (.stmt si) =>
      -- Generic always: treat as combinational (conservative)
      [{ reads := stmtReads si, writes := stmtWrites si, isComb := true }]
  | .cont_assign (.net nas) => getProcessesFromAssigns nas
  | .initial _ => []
  | .decl (.pkg (.net (.net _ _ ndas))) => getProcessesFromNetDeclAssigns ndas
  | .decl (.pkg (.data (.var_decl (.var _ vdas)))) => getProcessesFromVarDeclAssigns vdas
  | .decl _ => []
  | .assert _ => []

-- Extract processes from a module_or_generate_item.
def getProcessesFromModuleOrGenerateItem : module_or_generate_item → List CombProcess
  | .common ci => getProcessesFromModuleCommonItem ci
  | .ins (.module _ _ (.hier _ (.named npcs))) =>
      [{ reads := namedPortConnsReads npcs
       , writes := namedPortConnsWrites npcs
       , isComb := true }]

mutual
-- Extract processes from a generate_module_item (recursive).
def getProcessesFromGenerateModuleItem : generate_module_item → List CombProcess
  | .module mogi => getProcessesFromModuleOrGenerateItem mogi
  | .cond _ tgmi fgmi =>
      getProcessesFromGenerateModuleItem tgmi ++
      (match fgmi with | some f => getProcessesFromGenerateModuleItem f | none => [])
  | .block gmis => getProcessesFromGenerateModuleItemList gmis

def getProcessesFromGenerateModuleItemList : List generate_module_item → List CombProcess
  | [] => []
  | gmi :: rest => getProcessesFromGenerateModuleItem gmi ++ getProcessesFromGenerateModuleItemList rest
end

-- Extract processes from a non_port_module_item.
def getProcessesFromNonPortModuleItem : non_port_module_item → List CombProcess
  | .generated_module_ins (.generated gmi) => getProcessesFromGenerateModuleItem gmi
  | .module_or_generate_item mogi => getProcessesFromModuleOrGenerateItem mogi

-- Extract processes from a module_item.
def getProcessesFromModuleItem : module_item → List CombProcess
  | .port_decl _ => []
  | .non_port np => getProcessesFromNonPortModuleItem np

-- Extract processes from module_items.
def getProcessesFromModuleItems : module_items → List CombProcess
  | .one mi => getProcessesFromModuleItem mi
  | .cons mi mis => getProcessesFromModuleItem mi ++ getProcessesFromModuleItems mis

-- Extract all processes from a module declaration.
def getProcesses (m : module_decl) : List CombProcess :=
  match m with
  | .ansi _ _ _ items => getProcessesFromModuleItems items

-- ## Part 3: The 4 Static Predicates

-- P1: Every variable is written by at most one combinational process.
def UniqueWrites (procs : List CombProcess) : Prop :=
  ∀ (i j : Nat), i ≠ j →
    ∀ (p1 p2 : CombProcess), procs[i]? = some p1 → procs[j]? = some p2 →
      p1.isComb = true → p2.isComb = true →
        ∀ v, v ∈ p1.writes → v ∈ p2.writes → False

/- Compute dependency edges: for each comb process i that reads variable v,
    find comb process j that writes v. Add edge (j, i). -/
def DepEdges (procs : List CombProcess) : List (Nat × Nat) :=
  let indexed := procs.zipIdx
  indexed.flatMap fun (pi, i) =>
    if pi.isComb then
      pi.reads.flatMap fun v =>
        indexed.filterMap fun (pj, j) =>
          if pj.isComb && i != j && pj.writes.elem v then some (j, i)
          else none
    else []

/- P2: The dependency graph among combinational processes is acyclic.
    Stated as: there is no cycle in the dependency graph. -/
def AcyclicDeps (procs : List CombProcess) : Prop :=
  ¬ ∃ cycle : List Nat,
    cycle.length > 0 ∧
    (∀ k, k < cycle.length →
      let i := cycle[k]!
      let j := cycle[(k + 1) % cycle.length]!
      (i, j) ∈ DepEdges procs)

/- P3: Every variable read by a combinational process is written by some
    process or is an input/flop. -/
def CompleteReads (procs : List CombProcess) (inputs flops : List VId) : Prop :=
  ∀ p, p ∈ procs → p.isComb = true →
    ∀ v, v ∈ p.reads →
      v ∈ inputs ∨ v ∈ flops ∨ (∃ q, q ∈ procs ∧ v ∈ q.writes)

mutual
-- Check whether a statement contains no nonblocking assignments.
def hasNoNonblocking : statement_item → Bool
  | .blocking_assign_normal _ _ => true
  | .nonblocking_assign _ _ => false
  | .case _ _ css => hasNoNonblockingCases css
  | .cond _ ts fs =>
      (match ts with | some s => hasNoNonblocking s | none => true) &&
      (match fs with | some (some s) => hasNoNonblocking s | _ => true)
  | .forever s => hasNoNonblocking s
  | .repeat _ s => hasNoNonblocking s
  | .while _ s => hasNoNonblocking s
  | .for _ _ _ s => hasNoNonblocking s
  | .do_while s _ => hasNoNonblocking s
  | .return _ => true
  | .proc_timing_control _ s => hasNoNonblocking s
  | .seq_block ss => hasNoNonblockingList ss

def hasNoNonblockingCases : List (case_item statement_item) → Bool
  | [] => true
  | ci :: rest =>
      (match ci with
       | .case _ st => hasNoNonblocking st
       | .default st => hasNoNonblocking st) &&
      hasNoNonblockingCases rest

def hasNoNonblockingList : List statement_item → Bool
  | [] => true
  | s :: rest => hasNoNonblocking s && hasNoNonblockingList rest
end

mutual
-- Check whether a statement contains no blocking assignments.
def hasNoBlocking : statement_item → Bool
  | .blocking_assign_normal _ _ => false
  | .nonblocking_assign _ _ => true
  | .case _ _ css => hasNoBlockingCases css
  | .cond _ ts fs =>
      (match ts with | some s => hasNoBlocking s | none => true) &&
      (match fs with | some (some s) => hasNoBlocking s | _ => true)
  | .forever s => hasNoBlocking s
  | .repeat _ s => hasNoBlocking s
  | .while _ s => hasNoBlocking s
  | .for _ _ _ s => hasNoBlocking s
  | .do_while s _ => hasNoBlocking s
  | .return _ => true
  | .proc_timing_control _ s => hasNoBlocking s
  | .seq_block ss => hasNoBlockingList ss

def hasNoBlockingCases : List (case_item statement_item) → Bool
  | [] => true
  | ci :: rest =>
      (match ci with
       | .case _ st => hasNoBlocking st
       | .default st => hasNoBlocking st) &&
      hasNoBlockingCases rest

def hasNoBlockingList : List statement_item → Bool
  | [] => true
  | s :: rest => hasNoBlocking s && hasNoBlockingList rest
end

-- Check proper assign kind for a single module_common_item.
def checkProperAssignKindItem : module_common_item → Bool
  | .always .always_comb (.stmt si) => hasNoNonblocking si
  | .always .always_latch (.stmt si) => hasNoNonblocking si
  | .always .always_ff (.stmt si) => hasNoBlocking si
  | _ => true

-- Check proper assign kind for a module_or_generate_item.
def checkProperAssignKindMOGI : module_or_generate_item → Bool
  | .common ci => checkProperAssignKindItem ci
  | .ins _ => true

mutual
-- Check proper assign kind for a generate_module_item (recursive).
def checkProperAssignKindGMI : generate_module_item → Bool
  | .module mogi => checkProperAssignKindMOGI mogi
  | .cond _ tgmi fgmi =>
      checkProperAssignKindGMI tgmi &&
      (match fgmi with | some f => checkProperAssignKindGMI f | none => true)
  | .block gmis => checkProperAssignKindGMIList gmis

def checkProperAssignKindGMIList : List generate_module_item → Bool
  | [] => true
  | gmi :: rest => checkProperAssignKindGMI gmi && checkProperAssignKindGMIList rest
end

-- Check proper assign kind for a non_port_module_item.
def checkProperAssignKindNPMI : non_port_module_item → Bool
  | .generated_module_ins (.generated gmi) => checkProperAssignKindGMI gmi
  | .module_or_generate_item mogi => checkProperAssignKindMOGI mogi

-- Check proper assign kind for a module_item.
def checkProperAssignKindMI : module_item → Bool
  | .port_decl _ => true
  | .non_port np => checkProperAssignKindNPMI np

-- Check proper assign kind for module_items.
def checkProperAssignKindMIs : module_items → Bool
  | .one mi => checkProperAssignKindMI mi
  | .cons mi mis => checkProperAssignKindMI mi && checkProperAssignKindMIs mis

-- P4: Combinational blocks use only blocking, sequential use only nonblocking.
def ProperAssignKind (m : module_decl) : Prop :=
  match m with
  | .ansi _ _ _ items => checkProperAssignKindMIs items = true

-- ## Part 4: Decidable (Bool-returning) versions

-- Check P1: every variable is written by at most one combinational process.
def checkUniqueWrites (procs : List CombProcess) : Bool :=
  let combProcs := procs.zipIdx |>.filter (fun (p, _) => p.isComb)
  combProcs.all fun (pi, i) =>
    combProcs.all fun (pj, j) =>
      i == j || pi.writes.all fun v => !pj.writes.elem v

/- Topological sort via Kahn's algorithm.
    Returns true if the dependency graph is acyclic. -/
def checkAcyclicDeps (procs : List CombProcess) : Bool :=
  let n := procs.length
  let edges := DepEdges procs
  -- in-degree for each node
  let inDeg := edges.foldl (fun (acc : Array Nat) (_, dst) =>
    if h : dst < acc.size then acc.set dst (acc[dst] + 1)
    else acc) (Array.replicate n 0)
  -- initial queue: nodes with in-degree 0
  let initQueue := (List.range n).filter fun i =>
    match inDeg[i]? with | some d => d == 0 | none => true
  go edges inDeg initQueue 0 n
where
  go (edges : List (Nat × Nat)) (inDeg : Array Nat) (queue : List Nat)
      (processed : Nat) (n : Nat) : Bool :=
    match h : queue with
    | [] => processed == n
    | u :: rest =>
      if processed < n then
        let neighbors := edges.filterMap fun (src, dst) =>
          if src == u then some dst else none
        let (inDeg', newQueue) := neighbors.foldl (fun (acc : Array Nat × List Nat) dst =>
          let (deg, q) := acc
          if h : dst < deg.size then
            let newDeg := deg[dst] - 1
            let deg' := deg.set dst newDeg
            if newDeg == 0 then (deg', q ++ [dst])
            else (deg', q)
          else acc) (inDeg, rest)
        go edges inDeg' newQueue (processed + 1) n
      else false
  termination_by n - processed

-- Check P3: every variable read by a comb process is accounted for.
def checkCompleteReads (procs : List CombProcess) (inputs flops : List VId) : Bool :=
  let allWrites := procs.flatMap (fun p => p.writes)
  procs.all fun p =>
    !p.isComb || p.reads.all fun v =>
      inputs.elem v || flops.elem v || allWrites.elem v

-- Check P4: proper assignment kinds throughout the module.
def checkProperAssignKind (m : module_decl) : Bool :=
  match m with
  | .ansi _ _ _ items => checkProperAssignKindMIs items

end VerilLean.Lang.Equiv.StaticCheck
