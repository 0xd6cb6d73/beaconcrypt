-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompile
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve

/-! LQ-F: budget transport for the compiled LQ-F program. The compiled program is a program of the logged source; its requests are classified by `LaterServerReserve.laterKind`, which gives every source14 request its source14 kind and the Server read none. Embedding a source14 program keeps its per-kind caps and adds no Server read (`embed_bound`, `embed_server`), and its results are results of the source14 program (`embed_support`). If `A₁` respects the run-phase budget and `A₂` respects the post-run budget on every input, the compiled LQ-F program makes at most the caps of the compiled Beacon-side program `compileLater` in every source14 kind (`compile_server_bound`), in closed form the transported caps of the classical compiled program plus `qFinish + qCreate` prekey and one-time reads each, `qCreate` identity reads and the post-run coin, HMAC and BLAKE2b budgets (`laterTransported`, `laterTransported_eq`, `compile_server_certified`), and at most one Server read (`compile_server_reads`; by construction exactly one, but only the upper bound is stated). It issues no KEM read for any pair of adversaries (`compile_server_no_kem`). Its creation cap is the create budget, which meets T4's `room` premise for `count + 1 = qCreate + 1` (`server_room`). These are the `certified` and read-cap premises of the LQ-F KEM bills. No assumption is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (ModeSpec Mode FreshBounds Budget asModeO)
open PqxdhDeploymentSecrecy (Ledger wrap)
open PqxdhDeploymentCompile (Local compileImpl)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhDeploymentLater (Snap PostSpec PostBudget postEmbed)
open PqxdhDeploymentLaterCompile (compileSnapImpl terminal laterCost readCost postCore runCap)
open PqxdhDeploymentLaterServerSource (embed)
open PqxdhDeploymentLaterServerReserve (laterKind)
open PqxdhDeploymentLaterServerCompile (compileServer)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X Out Result : Type}

/-- Embedding a source14 program into the logged source keeps its cap in every source14 kind. -/
theorem embed_bound (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (kind : SourceKind) (bound : Nat)
    (bounded : program.IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind) bound) :
    (simulateQ embed program).IsQueryBoundP (fun request => laterKind (KemSK := KemSK) request = some kind) bound := by
  induction program using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    obtain ⟨allowed, rest⟩ := bounded
    simp only [simulateQ_bind, simulateQ_spec_query, embed]
    rw [isQueryBoundP_query_bind_iff]
    have same : laterKind (KemSK := KemSK) (Sum.inl query) = some kind ↔ sourceKind (KemSK := KemSK) query = kind := by
      simp [laterKind]
    by_cases hit : sourceKind (KemSK := KemSK) query = kind
    · rw [ite_eq_left hit] at rest
      refine ⟨Or.inr (by rcases allowed with free | positive; exact absurd hit free; exact positive), fun reply => ?_⟩
      rw [ite_eq_left (same.mpr hit)]
      exact ih reply _ (rest reply)
    · rw [ite_eq_right hit] at rest
      refine ⟨Or.inl fun found => hit (same.mp found), fun reply => ?_⟩
      rw [ite_eq_right fun found => hit (same.mp found)]
      exact ih reply _ (rest reply)

/-- An embedded source14 program issues no Server read. -/
theorem embed_server (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    (simulateQ embed program).IsQueryBoundP (fun request => laterKind (KemSK := KemSK) request = none) 0 := by
  induction program using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, embed]
    rw [isQueryBoundP_query_bind_iff]
    have other : ¬ laterKind (KemSK := KemSK) (Sum.inl query) = none := by simp [laterKind]
    refine ⟨Or.inl other, fun reply => ?_⟩
    rw [ite_eq_right other]
    exact ih reply

/-- Every result of an embedded source14 program is a result of the program. -/
theorem embed_support (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (result : Result) (reached : result ∈ support (simulateQ embed program)) : result ∈ support program := by
  induction program using OracleComp.inductionOn with
  | pure value => simpa using reached
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, embed, mem_support_bind_iff] at reached ⊢
    obtain ⟨reply, _, member⟩ := reached
    exact ⟨reply, mem_support_query _ _, ih reply member⟩

/-- Budget transport for the compiled LQ-F program: if `A₁` respects the run-phase budget and `A₂` respects the post-run budget on every input, the compiled LQ-F program makes at most the caps of the compiled Beacon-side program in every source14 kind: the run-part cost (the CE-3 cost plus the finish pre-reads), one identity, prekey and one-time read per transported create, and the post-part cost. The Server read is no source14 request. -/
theorem compile_server_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (kind : SourceKind) :
    (compileServer setup codec route bounds mode first second).IsQueryBoundP
      (fun request => laterKind (KemSK := KemSK) request = some kind)
      (∑ core, laterCost kind core * runCap bounds budget core + readCost kind * runCap bounds budget 1 +
        ∑ postKind, cost kind (postCore postKind) * post.cap postKind) := by
  have runBound := FinitePartitionQueryBounds.weighted_bound commandKind (laterCost kind) (runCap bounds budget)
    (compileSnapImpl setup codec route) (fun request => sourceKind (KemSK := KemSK) request = kind)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode first
      budget respects core)
    (fun query state => PqxdhDeploymentLaterCompile.snap_step_bound setup codec route kind query state)
    (Snap.empty, Local.empty)
  refine IsQueryBoundP.mono (isQueryBoundP_bind (n := ∑ core, laterCost kind core * runCap bounds budget core)
    (m := readCost kind * runCap bounds budget 1 + (0 + (∑ postKind, cost kind (postCore postKind) * post.cap postKind +
      0))) (embed_bound _ kind _ runBound) fun run member => ?_) (by omega)
  have count := PqxdhDeploymentLaterCompile.owners_bound setup codec route bounds mode first budget respects run
    (embed_support _ run member)
  have reads := IsQueryBoundP.mono (PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) kind run.2.1
    (List.range run.2.2.log.owners.length))
    (Nat.mul_le_mul_left (readCost kind) (by simpa only [List.length_range] using count))
  refine isQueryBoundP_bind (n := readCost kind * runCap bounds budget 1)
    (m := 0 + (∑ postKind, cost kind (postCore postKind) * post.cap postKind + 0)) (embed_bound _ kind _ reads)
    fun beacons _ => ?_
  refine isQueryBoundP_bind (n := 0) ?_ fun server _ => ?_
  · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [laterKind])
  · refine isQueryBoundP_bind (embed_bound _ kind _ (PqxdhDeploymentLaterCompile.post_bound setup codec route kind
      (second run.1.1 (beacons, server)) post (postRespects _ _) run.2.2)) fun _ _ => trivial

/-- The compiled LQ-F program issues at most one Server read, for every pair of adversaries. (By construction it issues exactly one, after the terminal Beacon reads; the lower bound is not stated.) -/
theorem compile_server_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) :
    (compileServer setup codec route bounds mode first second).IsQueryBoundP
      (fun request => laterKind (KemSK := KemSK) request = none) 1 := by
  refine isQueryBoundP_bind (n := 0) (m := 1) (embed_server _) fun run _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 1) (embed_server _) fun beacons _ => ?_
  refine isQueryBoundP_bind (n := 1) (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr (by simp [laterKind]))
    fun server _ => ?_
  exact isQueryBoundP_bind (n := 0) (m := 0) (embed_server _) fun _ _ => trivial

/-- The compiled LQ-F program issues no KEM read, for every pair of adversaries and without a budget: the finish pre-reads, the terminal Beacon reads and the post part read only identity, prekey and one-time fields, and the Server read reads the identity pool. The KEM read cap of the GoodKem argument therefore stays 0. -/
theorem compile_server_no_kem (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) :
    (compileServer setup codec route bounds mode first second).IsQueryBoundP
      (fun request => laterKind (KemSK := KemSK) request = some (.inr 1)) 0 := by
  have zero : ∀ core : Fin 12, cost (.inr 1) core = 0 := by
    intro core
    fin_cases core <;> simp [cost, unit]
  have laterZero : ∀ core, laterCost (.inr 1) core = 0 := by
    intro core
    simp [laterCost, zero, unit]
  have runZero := PqxdhDeploymentCompileSecrecy.simulate_zero (compileSnapImpl setup codec route) _
    (fun query state => by simpa only [laterZero] using
      PqxdhDeploymentLaterCompile.snap_step_bound setup codec route (.inr 1) query state)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) (Snap.empty, Local.empty)
  refine isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ runZero) fun run _ => ?_
  have readZero : (terminal (KemSK := KemSK) run.2.1 (List.range run.2.2.log.owners.length)).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr 1) 0 := by
    simpa [readCost, unit] using PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) (.inr 1) run.2.1
      (List.range run.2.2.log.owners.length)
  refine isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ readZero) fun beacons _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr (by simp [laterKind]))
    fun server _ => ?_
  exact isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ (PqxdhDeploymentCompileSecrecy.simulate_zero
    (compileImpl setup codec route) _ (fun query copies => by
      simpa only [zero] using PqxdhDeploymentCompileBudget.step_bound setup codec route (.inr 1) query copies) _
    run.2.2)) fun _ _ => trivial

/-- The transported caps of the compiled LQ-F program in the fourteen source14 query kinds: the transported caps of the classical compiled program, plus the post-run coin, HMAC and BLAKE2b budgets, `qCreate` identity reads and `qFinish + qCreate` prekey and one-time reads each. -/
def laterTransported (bounds : FreshBounds) (budget : Budget) (post : PostBudget) :
    PqxdhRegistrationJointKemCommands.Budget :=
  Sum.elim
    ![budget.coin + budget.test + budget.freshBytes bounds + post.coin, budget.create, budget.bundle, budget.accept,
      budget.build, budget.finish, budget.hmac + post.hmac,
      budget.hash + budget.sends + budget.receives + budget.test + budget.fresh + post.hash,
      budget.serverSend + budget.serverRaw + budget.test + budget.fresh]
    ![budget.create, 0, budget.finish + budget.create, budget.finish + budget.create,
      budget.beaconSend + budget.beaconRaw + budget.test + budget.fresh]

/-- The closed form of the transported caps of the compiled LQ-F program. -/
theorem laterTransported_eq (bounds : FreshBounds) (budget : Budget) (post : PostBudget) (kind : SourceKind) :
    (∑ core, laterCost kind core * runCap bounds budget core + readCost kind * runCap bounds budget 1 +
      ∑ postKind, cost kind (postCore postKind) * post.cap postKind) = laterTransported bounds budget post kind := by
  rcases kind with kind | kind <;> fin_cases kind <;>
    simp [Fin.sum_univ_succ, laterCost, readCost, postCore, cost, unit, runCap,
      PqxdhDeploymentCompileSecrecy.wrapCost, Budget.cap, PostBudget.cap, laterTransported, Budget.freshBytes,
      Budget.sends, Budget.receives] <;> ring

/-- The compiled LQ-F program meets the transported caps in every source14 query kind: the `certified` premise of the LQ-F KEM bills. -/
theorem compile_server_certified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (kind : SourceKind) :
    (compileServer setup codec route bounds mode first second).IsQueryBoundP
      (fun request => laterKind (KemSK := KemSK) request = some kind) (laterTransported bounds budget post kind) := by
  rw [← laterTransported_eq]
  exact compile_server_bound setup codec route bounds mode first second budget respects post postRespects kind

/-- The creation cap of the compiled LQ-F program is the create budget, within T4's `room` for `count + 1 = qCreate + 1`. -/
theorem server_room (bounds : FreshBounds) (budget : Budget) (post : PostBudget) :
    laterTransported bounds budget post (.inl 1) ≤ budget.create + 1 := by
  simp [laterTransported]

/-- The creation cap of the compiled LQ-F program is the create budget, for every post-run adversary: only the run part creates Beacons. This is T4's `room` premise for `count + 1 = qCreate + 1`. -/
theorem compile_server_creates (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) :
    (compileServer setup codec route bounds mode first second).IsQueryBoundP
      (fun request => laterKind (KemSK := KemSK) request = some (.inl 1)) budget.create := by
  have runBound := FinitePartitionQueryBounds.weighted_bound commandKind (laterCost (.inl 1)) (runCap bounds budget)
    (compileSnapImpl setup codec route) (fun request => sourceKind (KemSK := KemSK) request = .inl 1)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode first
      budget respects core)
    (fun query state => PqxdhDeploymentLaterCompile.snap_step_bound setup codec route (.inl 1) query state)
    (Snap.empty, Local.empty)
  have total : (∑ core, laterCost (.inl 1) core * runCap bounds budget core) = budget.create := by
    rw [← PqxdhDeploymentLaterCompile.runCap_create bounds budget]
    simp [Fin.sum_univ_succ, laterCost, cost, unit]
  rw [total] at runBound
  refine IsQueryBoundP.mono (isQueryBoundP_bind (n := budget.create) (m := 0) (embed_bound _ _ _ runBound)
    fun run _ => ?_) (by omega)
  have readZero : (terminal (KemSK := KemSK) run.2.1 (List.range run.2.2.log.owners.length)).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 1) 0 := by
    simpa [readCost, unit] using PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) (.inl 1) run.2.1
      (List.range run.2.2.log.owners.length)
  refine isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ readZero) fun beacons _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr (by simp [laterKind]))
    fun server _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ ?_) fun _ _ => trivial
  rw [← QueryImpl.simulateQ_compose]
  refine PqxdhDeploymentCompileSecrecy.simulate_zero ((compileImpl setup codec route) ∘ₛ postEmbed) _
    (fun query state => ?_) _ run.2.2
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [commandKind, cost, unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 1) (.inl coin) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [commandKind, cost, unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 1) (.inr (.hmac key message)) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [commandKind, cost, unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 1) (.inr (.hash bytes)) state

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.embed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.embed_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.embed_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.embed_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.embed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.embed_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_no_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_no_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.laterTransported_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.laterTransported_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_certified

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.server_room' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.server_room

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCompileBudget.compile_server_creates
