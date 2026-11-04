-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence

/-! Corrected assigned-ID finish cannot introduce an incoherent pending capability. Actual authentication, agreement, record opening, copy/install and every failed branch preserve the existing all-owner control/pin invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconCoherence (Holds PhaseCoherent)
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Auxiliary Value Platform : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}
private def Keeps (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, Holds owners → result ∈ support ((work.run owners).run env) → Holds result.1.2

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps {Next : Type} (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : Keeps work)
    (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior reached) continued

private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  exact prior

private theorem readonly_keeps (work : M n KemSK source Auxiliary Value)
    (readonly : RegistrationNativeBeaconFootprint.ReadOnly work) : Keeps work := by
  intro owners env result prior supported
  rw [readonly owners env result supported]
  exact prior

private theorem simulate_keeps {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (law : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) :
    Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (law query) ih

private theorem current_keeps (index : Nat) (change : Owner source → Owner source)
    (valid : ∀ owner, PhaseCoherent owner.phase → PhaseCoherent (change owner).phase) :
    Keeps ((modify fun owners => match owners[index]? with
      | none => owners
      | some current => owners.set index (change current)) : M n KemSK source Auxiliary Unit) := by
  intro owners env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => exact prior
  | some owner =>
      intro selected member
      rcases List.mem_or_eq_of_mem_set member with original | rfl
      · exact prior selected original
      · exact valid owner (prior owner (List.mem_of_getElem? found))

private theorem phase_keeps (index : Nat) (phase : Phase) (valid : PhaseCoherent phase) :
    Keeps (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) :=
  current_keeps index (fun owner => { owner with phase }) (fun _ _ => valid)

private theorem abort_pure_keeps (owner : Owner source) (value : Value) :
    Keeps ((abort owner *> pure value) : M n KemSK source Auxiliary Value) := by
  rw [seqRight_eq_bind]
  exact bind_keeps _ _
    (readonly_keeps _ (RegistrationNativeBeaconFootprint.abort_readonly owner))
    (fun _ => pure_keeps value)

private theorem install_keeps (index : Nat) (owner : Owner source)
    (completed : registration.CompletedBeacon) :
    Keeps (RegistrationNativePlatformBeaconFinish.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_keeps _ _ (lift_keeps _)
  intro installed
  cases installed with
  | false => exact abort_pure_keeps owner _
  | true => exact bind_keeps _ _ (phase_keeps index _ (by trivial)) (fun _ => pure_keeps _)

private theorem after_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) :
    Keeps (RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary)
      setup wire index owner oneTime accepted) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_keeps _ _
    (simulate_keeps _ (fun query => readonly_keeps _
      (RegistrationNativeBeaconFootprint.agreement_readonly setup owner oneTime query)) _)
  intro agreed
  cases agreed with
  | fail error | div => exact abort_pure_keeps owner _
  | ok effect =>
    cases effect
    all_goals first
      | exact abort_pure_keeps owner _
      | apply bind_keeps _ _
          (simulate_keeps _ (fun query => readonly_keeps _
            (RegistrationNativeBeaconFootprint.record_readonly setup wire query)) _)
        intro opened
        cases opened with
        | fail error | div => exact abort_pure_keeps owner _
        | ok answer => cases answer with
          | Err previous => exact abort_pure_keeps owner _
          | Ok completed => exact install_keeps index owner completed

/-- Full corrected finish preserves every retained pending control/pin equation on all failed and successful prefixes. -/
theorem finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (prior : Holds owners)
    (supported : result ∈ support
      (((RegistrationNativePlatformBeaconFinish.finish (n := n) setup source wire index packet).run owners).run env)) :
    Holds result.1.2 := by
  simp only [RegistrationNativePlatformBeaconFinish.finish, RegistrationNativePlatformBeaconFinish.finishWith,
    StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact prior
  | some owner =>
    rw [found] at supported
    cases phase : owner.phase <;> simp only [phase] at supported
    all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact prior }
    case initSent pending oneTime =>
      cases stopped : pending.aborted_state with
      | fail error | div =>
        simp only [stopped, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact prior
      | ok aborted =>
        simp only [stopped] at supported
        apply (bind_keeps _ _ (phase_keeps index (.aborted aborted) (by trivial)) (fun _ => ?_)) owners env result prior supported
        apply bind_keeps _ _
          (simulate_keeps _ (fun query => readonly_keeps _
            (RegistrationNativeBeaconFootprint.authentication_readonly setup query)) _)
        intro authenticated
        cases authenticated with
        | fail error | div => exact abort_pure_keeps owner _
        | ok answer => cases answer with
          | Err previous => exact abort_pure_keeps owner _
          | Ok accepted => exact after_keeps setup wire index owner oneTime accepted

/-- The corrected complete nested source callback preserves coherence for every retained pending owner. -/
theorem native_finish (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes)) (prior : Holds before.beacons)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet))).run before).run previous)) :
    Holds after.beacons := by
  have actual : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  cases same
  apply finish setup source wire index packet before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1 prior
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

end BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence.native_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence.native_finish
