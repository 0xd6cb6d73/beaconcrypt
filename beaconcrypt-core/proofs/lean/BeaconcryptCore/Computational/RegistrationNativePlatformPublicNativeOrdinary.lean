-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicWorldBills (nativeBill)
open PqxdhRecordLiftInterface (EffectKind effectKind EnvEffects RecordQuery)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind)
variable {n : Nat} {E Platform A B KemSK : Type}
private theorem map_iff {J X Y : Type} {spec : OracleSpec J}
    (cost : J → Nat) (work : OracleComp spec X) (change : X → Y) (cap : Nat) :
    Weighted cost (change <$> work) cap ↔ Weighted cost work cap :=
  isQueryBound_map_iff work change cap _ _
private theorem zero_bind {J : Type} {spec : OracleSpec J} (cost : J → Nat)
    (work : OracleComp spec A) (next : A → OracleComp spec B)
    (first : Weighted cost work 0) (later : ∀ value, Weighted cost (next value) 0) :
    Weighted cost (work >>= next) 0 := by
  simpa only [Nat.zero_add] using weighted_bind cost work next 0 0 first later
private theorem platform_zero (qSign qKem : Nat) (kind : EffectKind) (work : StateT Platform ProbComp A) (before : Platform) :
    Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind) ((platformFull work).run before) 0 := by
  unfold platformFull StateT.run
  induction work.run before using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, publicCoin]
    rw [Weighted, isQueryBound_query_bind_iff]
    exact ⟨by simp [nativeBill], fun value => ih value⟩
private theorem old_zero (qSign qKem : Nat) (kind : EffectKind) (query : RecordQuery) :
    Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind) (old (.inr query)) 0 := by
  simp [old, Weighted, nativeBill, RegistrationNativeRestrictedCosts.bill]
private theorem gate_zero (qSign qKem : Nat) (kind : EffectKind)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (size : A → Nat)
    (output : Option A) (before : Platform) :
    Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (reserve amount)) size output).run before) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run_bind]
    exact zero_bind _ _ _ (platform_zero qSign qKem kind _ before) (fun result => by cases result.1 <;> trivial)
/-- Every actual ongoing source record route has zero old/global Env cost. Its native record request and public reservation are kept in their own ledgers, including failed sends and raw receives. -/
theorem record_bound {source : RegistrationNativeMldsa.Source} (qSign qKem : Nat) (kind : EffectKind)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery) (before : State source Platform) :
    Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind) ((record reserve query).run before) 0 := by
  rcases query with (send | raw) | ⟨index, (plaintext | raw)⟩
  · simp only [record, StateT.run]
    apply zero_bind _ _ _ (old_zero qSign qKem kind (.inl (.inl send)))
    intro output
    simp only [bind_pure_comp, map_iff]
    exact gate_zero qSign qKem kind reserve _ output before.2
  · simpa only [record, StateT.run, map_iff] using old_zero (n := n) (KemSK := KemSK) qSign qKem kind (.inl (.inr raw))
  · simp only [record, StateT.run]
    cases before.1.beacons[index]? with
    | none => trivial
    | some owner =>
      dsimp only
      apply zero_bind _ _ _ (old_zero qSign qKem kind (.inr (owner.view.worldOwner, .inl plaintext)))
      intro output
      simp only [bind_pure_comp, map_iff]
      exact gate_zero qSign qKem kind reserve _ output before.2
  · simp only [record, StateT.run]
    cases before.1.beacons[index]? with
    | none => trivial
    | some owner =>
      simpa only [map_iff] using old_zero (n := n) (KemSK := KemSK) qSign qKem kind (.inr (owner.view.worldOwner, .inr raw))
/-- The actual public coin/hash leaf pays its single native/global effect, preserving the same local frontend/P value. -/
theorem effect_bound {source : RegistrationNativeMldsa.Source} (qSign qKem : Nat) (kind : EffectKind)
    (query : (EnvEffects n).Domain) (before : State source Platform) :
    Weighted (RegistrationNativePlatformPublicNativeLocal.bill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((StateT.lift (effect query) : LocalM n KemSK Platform source _).run before)
      (if effectKind query = kind then 1 else 0) := by
  simp only [StateT.run_lift, bind_pure_comp, map_iff, effect]
  simpa only [RegistrationNativeReferenceCosts.bill] using
    RegistrationNativePlatformPublicNativeLocal.local_query (n := n) (KemSK := KemSK) qSign qKem kind false
      (.inr (.inl (.inr (.inr query))))
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary.record_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary.effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeOrdinary.effect_bound
