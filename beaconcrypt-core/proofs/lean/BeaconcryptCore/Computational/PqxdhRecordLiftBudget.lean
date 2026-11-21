-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! Finite resource transport for the actual open record-lift program. These counts include its startup and secrecy-wrapper coins, public hash requests and restricted environment effects. Record-handler work and lazy hidden-seed sampling remain costs of the world interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftBudget
open PqxdhRecordLiftInterface PqxdhDeploymentInterface
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhDeploymentCompileSecrecy (wrapCost)

/-- Requests issued in the world's restricted-effect summand, including its direct public coin/hash routes. -/
def WorldEffect {n : Nat} (kind : EffectKind) : (WorldSpec n).Domain → Prop
  | .inr (.inl effect) => effectKind effect = kind
  | _ => False

instance {n : Nat} (kind : EffectKind) : DecidablePred (WorldEffect (n := n) kind) :=
  fun query => match query with
  | .inr (.inl effect) => inferInstanceAs (Decidable (effectKind effect = kind))
  | .inl _ | .inr (.inr _) => isFalse id

/-- Only registration/HMAC classes invoke the environment. Native coins and hashes are charged directly. -/
def nativeCost (allowance : Fin 14 → EffectKind → Nat) (kind : EffectKind) : Fin 12 → Nat :=
  ![if kind = .coin then 1 else 0,
    allowance 1 kind, allowance 2 kind, allowance 3 kind, allowance 4 kind,
    allowance 5 kind, allowance 6 kind, if kind = .hash then 1 else 0, 0, 0, 0, 0]

/-- Adversary coins, the possible test-bit draws, fresh-message bytes and public BLAKE2b calls bypass the environment. -/
def directCost (budget : Budget) (bounds : FreshBounds) : EffectKind → Nat
  | .coin => budget.coin + budget.test + bounds.max * budget.fresh
  | .hash => budget.hash
  | .administrative => 0

/-- Startup may draw coins, but cannot invoke a capability. -/
def startupCost (startupCoins : Nat) : EffectKind → Nat
  | .coin => startupCoins
  | _ => 0

/-- The actual native and secrecy-layer cost matrices fit the finite environment allowance plus explicit direct work. -/
theorem cost_sum (caps : Caps) (bounds : FreshBounds) (allowance : Fin 14 → EffectKind → Nat)
    (kind : EffectKind) :
    (∑ core, nativeCost allowance kind core * ∑ full, wrapCost bounds core full * caps.outer.cap full) ≤
      directCost caps.outer bounds kind + caps.envTotal allowance kind := by
  cases kind <;>
    simp [nativeCost, directCost, wrapCost, Caps.envTotal, Budget.cap, Fin.sum_univ_succ, Nat.mul_comm] <;> omega

/-- The restricted handler keeps its actual per-class bound when its effects enter the world. -/
theorem environment_bound {n : Nat} {E : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startupCoins allowance) (kind : EffectKind) (query : EnvQuery) (state : E) :
    ((environmentStep env query).run state).IsQueryBoundP (WorldEffect kind)
      (allowance (queryClass (.inl (.inr query.val))) kind) := by
  apply (framed.2 query state kind).simulateQ_of_step
  all_goals simp [effectLift, WorldEffect, isQueryBoundP_query_iff]

set_option backward.isDefEq.respectTransparency false in
/-- Every actual native branch is bounded by its own cost, including refusal paths. -/
theorem native_bound {n : Nat} {E : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startupCoins allowance) (kind : EffectKind) (query : Spec.Domain) (state : E) :
    ((native env query).run state).IsQueryBoundP (WorldEffect kind)
      (nativeCost allowance kind (commandKind query)) := by
  rcases query with coin | command
  · simp +contextual [native, coinLift, commandKind, nativeCost, WorldEffect, effectKind,
      StateT.run_lift, isQueryBoundP_query_iff, eq_comm]
  · cases command <;> first
      | exact environment_bound env startupCoins allowance framed kind _ state
      | simp +contextual [native, effectLift, commandKind, nativeCost, WorldEffect, effectKind,
          StateT.run_lift, isQueryBoundP_query_iff, eq_comm]

/-- The exact secrecy wrapper and native environment composition obey the finite cap in either observation mode. -/
theorem wrapped_bound {n : Nat} {E X Reader Response : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startupCoins allowance) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (caps : Caps)
    (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (kind : EffectKind) (state : E) :
    ((simulateQ (native env)
      (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (asModeO mode adversary))).run state).IsQueryBoundP
        (WorldEffect kind) (directCost caps.outer bounds kind + caps.envTotal allowance kind) :=
  (FinitePartitionQueryBounds.weighted_bound commandKind (nativeCost allowance kind)
    (fun core => ∑ full, wrapCost bounds core full * caps.outer.cap full)
    (native env) (WorldEffect kind)
    (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (asModeO mode adversary))
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound crypto codec serverKid bounds mode
      adversary caps.outer respects core)
    (fun query state => native_bound env startupCoins allowance framed kind query state) state).mono
      (cost_sum caps bounds allowance kind)

/-- Startup contributes only its declared uniform draws, including a startup that later returns no constructor. -/
theorem startup_bound {n : Nat} {E : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startupCoins allowance) (kind : EffectKind) :
    (simulateQ (coinLift (n := n)) env.start).IsQueryBoundP (WorldEffect kind) (startupCost startupCoins kind) := by
  cases kind
  case' coin =>
    apply (framed.1.isQueryBoundP (p := fun _ => True)).simulateQ_of_step
  case' hash | administrative =>
    apply (isQueryBoundP_false env.start 0).simulateQ_of_step
  all_goals simp [coinLift, WorldEffect, effectKind, isQueryBoundP_query_iff]

/-- Resource transport for the actual open program, with startup, wrapper work and environment work all charged. -/
theorem program_bound {n : Nat} {E X Reader Response : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startupCoins allowance) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (caps : Caps)
    (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary) (kind : EffectKind) :
    (program env crypto codec serverKid bounds mode adversary).IsQueryBoundP (WorldEffect kind)
      (startupCost startupCoins kind + (directCost caps.outer bounds kind + caps.envTotal allowance kind)) := by
  apply isQueryBoundP_bind (startup_bound env startupCoins allowance framed kind)
  rintro (_ | ⟨created, initial⟩) _
  all_goals simp [WorldEffect, isQueryBoundP_query_bind_iff, bind_pure_comp, isQueryBoundP_map_iff]
  exact wrapped_bound env startupCoins allowance framed crypto codec serverKid bounds mode caps adversary respects kind initial

/-- Joint record classes keep a handle-selected send in one class across both directions. -/
inductive RecordKind where
  | send
  | raw
  deriving DecidableEq

def NativeRecord (kind : RecordKind) (query : Spec.Domain) : Prop :=
  match kind with
  | .send => commandKind query = 8 ∨ commandKind query = 10
  | .raw => commandKind query = 9 ∨ commandKind query = 11

instance (kind : RecordKind) : DecidablePred (NativeRecord kind) :=
  fun _ => by cases kind <;> unfold NativeRecord <;> infer_instance

/-- A test or fresh command makes at most one send, regardless of its selected role. -/
def recordCost : RecordKind → Fin 14 → Nat
  | .send, query => if query.val = 8 ∨ query.val = 10 ∨ query.val = 12 ∨ query.val = 13 then 1 else 0
  | .raw, query => if query.val = 9 ∨ query.val = 11 then 1 else 0

/-- Joint record accounting for one actual secrecy-wrapper step, including every rejected attempt. -/
theorem wrap_record_step {Reader Response : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (kind : RecordKind) (query : Query)
    (ledger : PqxdhDeploymentSecrecy.Ledger) :
    ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger).IsQueryBoundP
      (NativeRecord kind) (recordCost kind (queryClass query)) := by
  rcases query with request | secrecy
  case' inr =>
    have coins (bound : Nat) : (PqxdhDeploymentSecrecy.coin bound).IsQueryBoundP (NativeRecord kind) 0 := by
      cases kind <;> simp [PqxdhDeploymentSecrecy.coin, NativeRecord, commandKind, isQueryBoundP_query_iff]
    have bytes (length : Nat) : (PqxdhDeploymentSecrecy.uniformBytes length).IsQueryBoundP
        (NativeRecord kind) 0 := by
      induction length with
      | zero => trivial
      | succ length ih =>
          exact isQueryBoundP_bind (coins 255) fun _ _ =>
            isQueryBoundP_bind ih fun _ _ => isQueryBoundP_pure _ _ 0
    have sends (handle : Handle) (plaintext : Pqxdh.Bytes) :
        (PqxdhDeploymentSecrecy.send handle plaintext).IsQueryBoundP
          (NativeRecord kind) (if kind = .send then 1 else 0) := by
      cases kind <;> cases handle <;>
        simp [PqxdhDeploymentSecrecy.send, NativeRecord, commandKind, isQueryBoundP_query_iff]
    have cost : recordCost kind (queryClass (.inr secrecy)) = (if kind = .send then 1 else 0) := by
      cases kind <;> cases secrecy <;> rfl
    rcases secrecy with ⟨handle, left, right⟩ | ⟨handle, length⟩
    · simp only [cost, PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
      split
      · split
        · exact (isQueryBoundP_bind (n := 0)
            (by simpa only [PqxdhDeploymentSecrecy.drawBit, isQueryBoundP_map_iff] using coins 1)
            (fun _ _ => isQueryBoundP_bind (m := 0) (sends handle _) fun _ _ =>
              isQueryBoundP_pure _ _ 0)).mono (by omega)
        · split
          · exact isQueryBoundP_bind (m := 0) (sends handle _) fun _ _ => isQueryBoundP_pure _ _ 0
          · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_pure _ _ _
    · simp only [cost, PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
      split
      · exact (isQueryBoundP_bind (bytes length)
          (fun _ _ => isQueryBoundP_bind (m := 0) (sends handle _) fun _ _ =>
            isQueryBoundP_pure _ _ 0)).mono (by omega)
      · exact isQueryBoundP_pure _ _ _
  case inl =>
    rcases request with coin | command
    · cases kind <;> simp [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, NativeRecord, recordCost,
        queryClass, commandKind, isQueryBoundP_query_iff]
    · cases command <;> cases kind <;>
        simp [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, NativeRecord, recordCost,
          queryClass, commandKind, isQueryBoundP_query_iff]

/-- The existing CE totals combine both directions and count each test/fresh once. -/
def recordBudget (budget : Budget) : RecordKind → Nat
  | .send => budget.sends
  | .raw => budget.receives

/-- The actual wrapper has a joint send/raw cap, without double charging the alternative handle directions. -/
theorem wrap_record_bound {X Reader Response : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) (kind : RecordKind) :
    (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (asModeO mode adversary)).IsQueryBoundP
      (NativeRecord kind) (recordBudget budget kind) := by
  have bounded := FinitePartitionQueryBounds.weighted_bound queryClass (recordCost kind) budget.cap
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds) (NativeRecord kind)
    (asModeO mode adversary) (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects)
    (fun query ledger => wrap_record_step crypto codec serverKid bounds kind query ledger)
    PqxdhDeploymentSecrecy.Ledger.empty
  cases kind <;> simpa [PqxdhDeploymentSecrecy.wrap, recordCost, recordBudget, Budget.cap, Budget.sends, Budget.receives,
    Fin.sum_univ_succ, Nat.add_assoc] using bounded

def recordKind : RecordQuery → RecordKind
  | .inl (.inl _) | .inr (_, .inl _) => .send
  | .inl (.inr _) | .inr (_, .inr _) => .raw

/-- Count both role directions jointly among actual open-program record requests. -/
def WorldRecord {n : Nat} (kind : RecordKind) : (WorldSpec n).Domain → Prop
  | .inr (.inr query) => recordKind query = kind
  | _ => False

instance {n : Nat} (kind : RecordKind) : DecidablePred (WorldRecord (n := n) kind) :=
  fun query => match query with
  | .inr (.inr _) => inferInstanceAs (Decidable (_ = kind))
  | .inl _ | .inr (.inl _) => isFalse id

/-- The restricted effect type prevents every environment command from issuing a record request. -/
theorem environment_record_bound {n : Nat} {E : Type} (env : Environment n E)
    (kind : RecordKind) (query : EnvQuery) (state : E) :
    ((environmentStep env query).run state).IsQueryBoundP (WorldRecord kind) 0 := by
  apply (isQueryBoundP_false ((env.step query).run state) 0).simulateQ_of_step
  all_goals simp [effectLift, WorldRecord, isQueryBoundP_query_iff]

set_option backward.isDefEq.respectTransparency false in
/-- Actual native dispatch forwards one matching record request and no record work on any other branch. -/
theorem native_record_step {n : Nat} {E : Type} (env : Environment n E)
    (kind : RecordKind) (query : Spec.Domain) (state : E) :
    ((native env query).run state).IsQueryBoundP (WorldRecord kind)
      (if NativeRecord kind query then 1 else 0) := by
  rcases query with coin | command
  · cases kind <;> simp [native, coinLift, NativeRecord, commandKind, WorldRecord,
      StateT.run_lift, isQueryBoundP_query_iff]
  · cases command <;> cases kind <;> first
      | exact environment_record_bound env _ _ state
      | simp [native, effectLift, NativeRecord, commandKind, WorldRecord, recordKind,
          StateT.run_lift, isQueryBoundP_query_iff]

/-- Interleaved environment work preserves every joint record-request bound through actual native dispatch. -/
theorem native_record_bound {n : Nat} {E X : Type} (env : Environment n E)
    (kind : RecordKind) (client : OracleComp Spec X) (bound : Nat)
    (bounded : client.IsQueryBoundP (NativeRecord kind) bound) (state : E) :
    ((simulateQ (native env) client).run state).IsQueryBoundP (WorldRecord kind) bound :=
  bounded.simulateQ_run_of_step
    (fun query matching state => by simpa only [ite_eq_left matching] using native_record_step env kind query state)
    (fun query other state => by simpa only [ite_eq_right other] using native_record_step env kind query state) state

/-- Startup's uniform-only interface cannot issue either kind of record request. -/
theorem startup_record_bound {n : Nat} {E : Type} (env : Environment n E) (kind : RecordKind) :
    (simulateQ (coinLift (n := n)) env.start).IsQueryBoundP (WorldRecord kind) 0 := by
  apply (isQueryBoundP_false env.start 0).simulateQ_of_step
  all_goals simp [coinLift, WorldRecord, isQueryBoundP_query_iff]

/-- The actual open program has at most `Budget.sends` joint sends and `Budget.receives` joint raw attempts. -/
theorem program_record_bound {n : Nat} {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) (kind : RecordKind) :
    (program env crypto codec serverKid bounds mode adversary).IsQueryBoundP
      (WorldRecord kind) (recordBudget budget kind) := by
  apply (isQueryBoundP_bind (m := recordBudget budget kind) (startup_record_bound env kind) ?_).mono (by omega)
  rintro (_ | ⟨created, initial⟩) _ <;>
    simp [WorldRecord, isQueryBoundP_query_bind_iff, bind_pure_comp, isQueryBoundP_map_iff]
  exact native_record_bound env kind _ _
    (wrap_record_bound crypto codec serverKid bounds mode budget adversary respects kind) initial

end BeaconcryptCore.Computational.PqxdhRecordLiftBudget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.cost_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.cost_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.environment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.environment_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.native_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.wrapped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.wrapped_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.startup_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.startup_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.program_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.wrap_record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.wrap_record_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.wrap_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.wrap_record_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.environment_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.environment_record_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.native_record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.native_record_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.native_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.native_record_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.startup_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.startup_record_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftBudget.program_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftBudget.program_record_bound
