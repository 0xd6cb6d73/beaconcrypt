-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds
/-! The public allocator has its own explicit uniform allowance per reached terminal reserve call. These draws are added once per possible send, including test/fresh sends and failed writes; shared-hash and administrative budgets are unchanged. The premise bounds only the concrete public service, not any protocol or security conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds
open PqxdhRecordLiftInterface (Environment WorldSpec EffectKind Frame Caps effectKind)
open PqxdhRecordLiftBudget (WorldEffect NativeRecord)
open PqxdhDeploymentInterface (Spec Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhDeploymentCompileSecrecy (wrapCost)
open RegistrationNativePlatformGatedRecordInterface (closed post native program)
variable {n : Nat} {E Failure A X Reader Response : Type}

def reserveCost (coins : Nat) : EffectKind → Nat
  | .coin => coins
  | _ => 0

def nativeCost (allowance : Fin 14 → EffectKind → Nat) (coins : Nat) (kind : EffectKind) (core : Fin 12) : Nat :=
  PqxdhRecordLiftBudget.nativeCost allowance kind core +
    if core.val = 8 ∨ core.val = 10 then reserveCost coins kind else 0

private theorem gate_total (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (output : Option RawCtxSourceSend.Encrypted) (before : E) :
    ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) output).run before).IsTotalQueryBound coins := by
  rw [← isQueryBoundP_true_iff]
  cases output with
  | none => exact isQueryBoundP_pure _ _ _
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run_bind]
      have query := (bounded value.ciphertext.length before).isQueryBoundP (p := fun _ => True)
      exact (isQueryBoundP_bind query (fun result _ => by
        cases result.1 <;> exact isQueryBoundP_pure _ _ 0)).mono (Nat.add_zero _).le

private theorem closed_bound (work : StateT E ProbComp A) (coins : Nat) (before : E)
    (bounded : (work.run before).IsTotalQueryBound coins) (kind : EffectKind) :
    ((closed (n := n) work).run before).IsQueryBoundP (WorldEffect kind) (reserveCost coins kind) := by
  cases kind
  case' coin => apply (bounded.isQueryBoundP (p := fun _ => True)).simulateQ_of_step
  case' hash | administrative => apply (isQueryBoundP_false (work.run before) 0).simulateQ_of_step
  all_goals simp [PqxdhRecordLiftInterface.coinLift, WorldEffect, effectKind, isQueryBoundP_query_iff]

/-- The reached public service contributes only its declared uniform cap; unsuccessful or absent sends do not add another primitive category. -/
theorem post_bound (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (kind : EffectKind) (query : Spec.Domain) (reply : Spec.Range query) (before : E) :
    ((post (n := n) reserve query reply).run before).IsQueryBoundP (WorldEffect kind)
      (if NativeRecord .send query then reserveCost coins kind else 0) := by
  rcases query with coin | command
  · exact isQueryBoundP_pure _ _ _
  · cases command
    case serverSend keyId plaintext =>
      exact closed_bound _ coins before (gate_total reserve coins bounded reply before) kind
    case beaconSend owner plaintext =>
      exact closed_bound _ coins before (gate_total reserve coins bounded reply before) kind
    all_goals exact isQueryBoundP_pure _ _ _

/-- The real native dispatch charges the source environment bill and the separate public allocator allowance in the literal source order. -/
theorem native_bound (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (kind : EffectKind) (query : Spec.Domain) (before : E) :
    ((native env reserve query).run before).IsQueryBoundP (WorldEffect kind)
      (nativeCost allowance coins kind (commandKind query)) := by
  simp only [native, StateT.run_bind]
  exact isQueryBoundP_bind (PqxdhRecordLiftBudget.native_bound env startup allowance framed kind query before)
    (fun result _ => by
      convert post_bound reserve coins bounded kind query result.1 result.2 using 1
      simp only [NativeRecord, Fin.ext_iff]
      rfl)

private theorem partition_weighted {Kind ι : Type} {spec : OracleSpec ι} [Fintype Kind] [DecidableEq Kind]
    (classify : spec.Domain → Kind) (cost cap : Kind → Nat) (work : OracleComp spec A)
    (bounded : ∀ kind, work.IsQueryBoundP (fun query => classify query = kind) (cap kind)) :
    PqxdhRecordLiftCtxProgramBounds.Weighted (fun query => cost (classify query)) work
      (FinitePartitionQueryBounds.bill cost cap) := by
  apply OracleComp.IsQueryBound.proj (FinitePartitionQueryBounds.bill cost)
    (h := FinitePartitionQueryBounds.structural classify work cap bounded)
  · intro query current positive
    have exactBill := FinitePartitionQueryBounds.bill_step cost current (classify query) positive
    dsimp only
    omega
  · intro query current positive
    have exactBill := FinitePartitionQueryBounds.bill_step cost current (classify query) positive
    dsimp only
    omega

/-- The complete adaptive wrapper carries the separate allocator allowance through all source command and secrecy branches. -/
theorem wrapped_bound (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds)
    (mode : Mode) (caps : Caps) (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (kind : EffectKind) (before : E) :
    ((simulateQ (native env reserve)
      (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run before).IsQueryBoundP
      (WorldEffect kind) (PqxdhRecordLiftBudget.directCost caps.outer bounds kind + caps.envTotal allowance kind +
        reserveCost coins kind * caps.outer.sends) := by
  let work := PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (PqxdhDeploymentInterface.asModeO mode adversary)
  have base := partition_weighted commandKind (PqxdhRecordLiftBudget.nativeCost allowance kind)
    (fun core => ∑ full, wrapCost bounds core full * caps.outer.cap full) work
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound crypto codec serverKid bounds mode adversary caps.outer respects core)
  have reserveBound := PqxdhRecordLiftCtxProgramBounds.weighted_indicator (NativeRecord .send) (reserveCost coins kind)
    work _ (PqxdhRecordLiftBudget.wrap_record_bound crypto codec serverKid bounds mode caps.outer adversary respects .send)
  have combined := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ work _ _ base reserveBound
  have steps : ∀ query state, ((native env reserve query).run state).IsQueryBoundP (WorldEffect kind)
      (PqxdhRecordLiftBudget.nativeCost allowance kind (commandKind query) +
        if NativeRecord .send query then reserveCost coins kind else 0) := by
    intro query state
    convert native_bound env startup allowance framed reserve coins bounded kind query state using 1
    simp only [nativeCost, NativeRecord, Fin.ext_iff]
    rfl
  have executed := PqxdhRecordLiftCtxBills.run_bound (native env reserve) (WorldEffect kind) _ steps work _ combined before
  exact executed.mono (Nat.add_le_add_right (PqxdhRecordLiftBudget.cost_sum caps bounds allowance kind) _)

/-- Public allocator uniforms are added explicitly; every other actual source-effect bill is retained. -/
theorem program_bound (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds)
    (mode : Mode) (caps : Caps) (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (kind : EffectKind) :
    (program env reserve crypto codec serverKid bounds mode adversary).IsQueryBoundP (WorldEffect kind)
      (PqxdhRecordLiftBudget.startupCost startup kind +
        (PqxdhRecordLiftBudget.directCost caps.outer bounds kind + caps.envTotal allowance kind + reserveCost coins kind * caps.outer.sends)) := by
  apply isQueryBoundP_bind (PqxdhRecordLiftBudget.startup_bound env startup allowance framed kind)
  rintro (_ | ⟨created, initial⟩) _
  all_goals simp [WorldEffect, isQueryBoundP_query_bind_iff, bind_pure_comp, isQueryBoundP_map_iff]
  exact wrapped_bound env startup allowance framed reserve coins bounded crypto codec serverKid bounds mode caps adversary respects kind initial

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.post_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.wrapped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.wrapped_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds.program_bound
