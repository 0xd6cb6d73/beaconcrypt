-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners
import BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint

/-! Corrected source finish retains exact owner credentials, identity scalars, private KEM handles, public keys and pins on all authentication, agreement, opening and installation outcomes. The actual assigned sender identifier affects the installed shell, while immutable owner metadata is retained by the reached operations themselves. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeOwnerFields (metadata)
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Auxiliary Value Platform : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}
private abbrev Keys (source : RegistrationNativeMldsa.Source) := List (Owner source)

private def Keeps (expected : Keys mlSource) (work : M n KemSK mlSource Auxiliary Value) : Prop :=
  ∀ owners env result, owners.map metadata = expected →
    result ∈ support ((work.run owners).run env) → result.1.2.map metadata = expected

private theorem pure_keeps (expected : Keys mlSource) (value : Value) :
    Keeps expected (pure value : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps {Next : Type} (expected : Keys mlSource) (work : M n KemSK mlSource Auxiliary Value)
    (next : Value → M n KemSK mlSource Auxiliary Next) (first : Keeps expected work)
    (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior reached) continued

private theorem lift_keeps (expected : Keys mlSource)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps expected (StateT.lift work : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _, returned⟩ := supported
  cases returned
  exact prior

private theorem simulate_keeps {Query : Type} {spec : OracleSpec Query} (expected : Keys mlSource)
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary))
    (law : ∀ query, Keeps expected (implementation query)) (work : OracleComp spec Value) :
    Keeps expected (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps expected value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps expected _ _ (law query) ih

private theorem set_same (expected : Keys mlSource) (index : Nat) (key : Owner mlSource)
    (found : expected[index]? = some key) : expected.set index key = expected := by
  obtain ⟨below, selected⟩ := List.getElem?_eq_some_iff.mp found
  rw [← selected]
  exact List.set_getElem_self below

private theorem current_keeps (expected : Keys mlSource) (index : Nat) (change : Owner mlSource → Owner mlSource)
    (same : ∀ owner, metadata (change owner) = metadata owner) :
    Keeps expected ((modify fun owners => match owners[index]? with
      | none => owners
      | some current => owners.set index (change current)) : M n KemSK mlSource Auxiliary Unit) := by
  intro owners env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => simpa only [found] using prior
  | some owner =>
      simp only [List.map_set, same, prior]
      apply set_same expected index (metadata owner)
      rw [← prior]
      simp [found]

private theorem phase_keeps (expected : Keys mlSource) (index : Nat) (phase : Phase) :
    Keeps expected (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) index phase) :=
  current_keeps expected index (fun owner => { owner with phase }) (fun _ => rfl)


private theorem readonly_keeps (expected : Keys mlSource) (work : M n KemSK mlSource Auxiliary Value)
    (law : RegistrationNativeBeaconFootprint.ReadOnly work) : Keeps expected work := by
  intro owners env result prior supported
  rw [law owners env result supported]
  exact prior

private theorem abort_pure_keeps (owner : Owner mlSource) (expected : Keys mlSource) (value : Value) :
    Keeps expected ((abort owner *> pure value) : M n KemSK mlSource Auxiliary Value) := by
  rw [seqRight_eq_bind]
  exact bind_keeps expected _ _
    (readonly_keeps expected _ (RegistrationNativeBeaconFootprint.abort_readonly owner))
    (fun _ => pure_keeps expected value)

private theorem install_keeps (index : Nat) (owner : Owner mlSource)
    (completed : registration.CompletedBeacon) (expected : Keys mlSource) :
    Keeps expected (RegistrationNativePlatformBeaconFinish.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro installed
  cases installed with
  | false => exact abort_pure_keeps owner expected _
  | true => exact bind_keeps expected _ _ (phase_keeps expected index _) (fun _ => pure_keeps expected _)

private theorem after_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) (expected : Keys mlSource) :
    Keeps expected (RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary)
      setup wire index owner oneTime accepted) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_keeps expected _ _
    (simulate_keeps expected _ (fun query => readonly_keeps expected _
      (RegistrationNativeBeaconFootprint.agreement_readonly setup owner oneTime query)) _)
  intro agreed
  cases agreed with
  | fail error | div => exact abort_pure_keeps owner expected _
  | ok effect =>
    cases effect
    all_goals first
      | exact abort_pure_keeps owner expected _
      | apply bind_keeps expected _ _
          (simulate_keeps expected _ (fun query => readonly_keeps expected _
            (RegistrationNativeBeaconFootprint.record_readonly setup wire query)) _)
        intro opened
        cases opened with
        | fail error | div => exact abort_pure_keeps owner expected _
        | ok answer => cases answer with
          | Err previous => exact abort_pure_keeps owner expected _
          | Ok completed => exact install_keeps index owner completed expected

/-- Full corrected finish, including failed prefixes, preserves complete immutable owner metadata. -/
theorem finish_metadata (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativePlatformBeaconFinish.finish (n := n) setup source wire index packet).run owners).run env)) :
    result.1.2.map metadata = owners.map metadata := by
  simp only [RegistrationNativePlatformBeaconFinish.finish, RegistrationNativePlatformBeaconFinish.finishWith,
    StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl
  | some owner =>
    rw [found] at supported
    cases phase : owner.phase <;> simp only [phase] at supported
    all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl }
    case initSent pending oneTime =>
      cases stopped : pending.aborted_state with
      | fail error | div =>
        simp only [stopped, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        rfl
      | ok aborted =>
        simp only [stopped] at supported
        apply (bind_keeps _ _ _ (phase_keeps _ index (.aborted aborted)) (fun _ => ?_)) owners env result rfl supported
        apply bind_keeps _ _ _
          (simulate_keeps _ _ (fun query => readonly_keeps _ _
            (RegistrationNativeBeaconFootprint.authentication_readonly setup query)) _)
        intro authenticated
        cases authenticated with
        | fail error | div => exact abort_pure_keeps owner _ _
        | ok answer => cases answer with
          | Err previous => exact abort_pure_keeps owner _ _
          | Ok accepted => exact after_keeps setup wire index owner oneTime accepted _

/-- The corrected complete nested source callback retains the exact immutable owner snapshot. -/
theorem native_metadata (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformBeaconFinish.finish setup mlSource wire index packet))).run before).run previous)) :
    after.beacons.map metadata = before.beacons.map metadata := by
  have actual : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup mlSource wire index packet)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  cases same
  apply finish_metadata setup mlSource wire index packet before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

/-- Actual nested Platform finish preserves every generated row/owner relation while installing the corrected assigned sender. -/
theorem finish (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes))
    (prior : RegistrationNativeKemBirthInvariant.Holds setup before.beacons before.pool)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformBeaconFinish.finish setup mlSource wire index packet))).run before).run previous)) :
    RegistrationNativeKemBirthInvariant.Holds setup after.beacons after.pool := by
  have actual : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup mlSource wire index packet)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at actual
  obtain ⟨result, reached, returned⟩ := actual
  have preserved := RegistrationNativeKemBirthInvariant.trusted_program setup checks representation created mlSource
    before.beacons _ before result.2 result.1 prior reached
  have native : result.1 ∈ support
      (((RegistrationNativePlatformBeaconFinish.finish (n := n) setup mlSource wire index packet).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have retained := finish_metadata setup mlSource wire index packet _ _ result.1 native
  cases returned
  exact RegistrationNativePlatformKnownOwners.metadata setup before.beacons result.1.1.2 result.2.pool preserved retained

end BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata.finish_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata.finish_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata.native_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata.native_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata.finish
