-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateProfile

/-! The complete uniform native source retains its original full ledger and actual reached private state before any event is evaluated. This is an exact observation of the concrete whole-startup hybrid, permitting source-supported structural target receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev Observation (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Value : Type) (count : Nat) :=
  RegistrationNativeKemStartupGame.Bootstrap n source ×
    RegistrationNativeKemCandidateObservation.Outcome (RegistrationNativeKemParsedRouting.Ambient n source) KemSK
      (RegistrationNativeKemServerState.State n source) (Value × RegistrationNativeLedger.State) count

def observe {source : RegistrationNativeMldsa.Source} {count : Nat}
    (decision : Value × RegistrationNativeLedger.State → Bool) (result : Option (Observation n KemSK source Value count)) : Bool :=
  (result.map fun outcome => outcome.2.record.observe decision).getD false

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat) (real : Bool) :
    ProbComp (Option (Observation n KemSK source Value budget.create)) := do
  let initial ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initial with
  | none => pure none
  | some initial => do
      let outcome ← RegistrationNativeKemCandidateObservation.total setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (RegistrationNativeKemFullSource.program setup checks wire initial.created.server.server.metadata.sender
          bounds mode (work initial.public) parsed) budget.create selected index real
      pure (some (RegistrationNativeKemStartupGame.ofInitial source initial, outcome))

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)

/-- Every original-ledger decision is the exact projection of the complete native source observation. -/
theorem source_observe (decision : Value × RegistrationNativeLedger.State → Bool) (real : Bool) :
    observe decision <$> profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index real =
      RegistrationNativeKemCandidateProfile.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode work budget parsed selected index decision real := by
  simp only [profile, RegistrationNativeKemCandidateProfile.profile, map_bind]
  apply bind_congr
  intro initial
  cases initial with
  | none => rfl
  | some initial =>
      simpa only [map_bind, map_pure, observe, Option.map_some, Option.getD_some,
        RegistrationNativeKemFullTotal.client, bind_pure_comp, Functor.map_map, Function.comp_def] using
        RegistrationNativeKemCandidateObservation.total_observe setup.baseImpl setup.kem
          (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
          (pure (RegistrationNativeKemServerState.project initial.state))
          (RegistrationNativeKemFullSource.program setup checks wire initial.created.server.server.metadata.sender
            bounds mode (work initial.public) parsed) budget.create selected index real decision

/-- The actual whole-startup ordinary KEM hybrid retains the complete original full observation, with no event-correspondence premise. -/
theorem hybrid_observe (decision : Value × RegistrationNativeLedger.State → Bool) (real : Bool) :
    EvalDistEq (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision real)
      (observe decision <$> profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode work budget parsed selected index real) := by
  rw [source_observe]
  exact RegistrationNativeKemCandidateProfile.hybrid_source (n := n) setup checks wire route representation source ensureInit
    identityIndex serverKeyId bounds mode work budget parsed selected index decision real

/-- A successful actual hybrid event has a genuine supported full native source observation and the literal original ledger value witnessing that event. -/
theorem winning_support (decision : Value × RegistrationNativeLedger.State → Bool) (real : Bool)
    (supported : true ∈ support (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision real)) :
    ∃ outcome value, some outcome ∈ support (profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index real) ∧ outcome.2.record.value = some value ∧ decision value = true := by
  rw [OracleComp.support_eq_of_evalDistEq (hybrid_observe (n := n) setup checks wire route representation source ensureInit
    identityIndex serverKeyId bounds mode work budget parsed selected index decision real), support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  cases result with
  | none => simp only [observe, Option.map_none, Option.getD_none, Bool.false_eq_true] at equal
  | some outcome =>
      cases found : outcome.2.record.value with
      | none =>
          simp only [observe, Option.map_some, Option.getD_some, RegistrationNativeKemCandidateObservation.Record.observe,
            RegistrationNativeKemCutMap.observe, found, Option.map_none, Option.getD_none, Bool.false_eq_true] at equal
      | some value =>
          exact ⟨outcome, value, reached, found, by simpa only [observe, Option.map_some, Option.getD_some,
            RegistrationNativeKemCandidateObservation.Record.observe, RegistrationNativeKemCutMap.observe, found] using equal⟩

end BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile.source_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile.source_observe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile.hybrid_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile.hybrid_observe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile.winning_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile.winning_support
