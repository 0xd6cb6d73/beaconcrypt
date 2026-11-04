-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning

/-! Raw ML receipt payloads are private analysis data in the causal joint-Ed reduction: they may contain the censored signature. The actual hash, record and signing source leaves do not inspect earlier receipt bytes. This explicit view erases only that coordinate and retains the full World, counters, auxiliary state and request markers. It is an event-compatible view, not equality of private raw logs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxBackend (Spec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response Auxiliary Value : Type} {base : OracleSpec I}

def view (before : State n Auxiliary) : State n Auxiliary := {before with world := (before.world.1, [])}

def Stable (work : StateT (State n Auxiliary) (OracleComp Spec) Value) : Prop :=
  ∀ before, Prod.map id view <$> work.run before = Prod.map id view <$> work.run (view before)

/-- Prior raw signing payloads are never read by actual source environment effects. -/
theorem effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (RegistrationNativePlatformCtxLocal.effects (n := n) (Auxiliary := Auxiliary) query) := by
  intro before
  simp only [RegistrationNativePlatformCtxLocal.effects, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    view, RegistrationNativePlatformCtxLocal.attach]

/-- Actual record primitive leaves retain the same complete World and optional reply after private receipt erasure. -/
theorem record (setup : Setup base KemSK) (codec : Codec Reader Response) (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Stable (RegistrationNativePlatformCtxLocal.record (n := n) (Auxiliary := Auxiliary) setup codec query) := by
  intro before
  simp only [RegistrationNativePlatformCtxLocal.record, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    view, RegistrationNativePlatformCtxLocal.attach]

/-- The complete source shared dictionary has no receipt-payload input dependency. -/
theorem shared (setup : Setup base KemSK) (codec : Codec Reader Response) (query : MldsaSharedNative.Spec.Domain) :
    Stable (RegistrationNativePlatformCtxLocal.shared (n := n) (Auxiliary := Auxiliary) setup codec query) := by
  cases query with
  | inl query => exact effects (.inr (.hash query.2))
  | inr query => exact record setup codec query

/-- Signing uses the exact request and sampler, then appends private receipt metadata. Its reply and all remaining state are independent of the prior raw log. -/
theorem outgoing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) :
    Stable (RegistrationNativePlatformCtxSigning.outgoing (n := n) (Auxiliary := Auxiliary) sign query) := by
  cases query with
  | hash request => exact effects (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
  | sign request payload digest =>
    intro before
    simp only [RegistrationNativePlatformCtxSigning.outgoing, StateT.run,
      Functor.map_map, Prod.map_def, id_eq, view]

/-- Resetting the private receipt view at every source query gives the same complete projected adaptive execution. -/
theorem complete {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (StateT (State n Auxiliary) (OracleComp Spec)))
    (law : ∀ query, Stable (handler query)) (work : OracleComp queries Value) (before : State n Auxiliary) :
    Prod.map id view <$> (simulateQ handler work).run before =
      (simulateQ (r := StateT (State n Auxiliary) (OracleComp Spec))
        (fun query current => Prod.map id view <$> (handler query).run current) work).run (view before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq handler _ view
  intro query current
  exact law query current

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.effects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.record
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.shared
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView.complete
