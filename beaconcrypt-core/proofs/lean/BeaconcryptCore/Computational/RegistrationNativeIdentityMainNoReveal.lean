-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealBeacon

/-! The concrete whole native client has no generated-identity reveal operation, for every public adversary, oracle reply, native failure and actual startup outcome. This derives the ordinary joint report monitor's freshness condition structurally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State M)
open RegistrationNativeIdentityMainNoRevealCore (Allowed Safe mapped pure_safe bind_safe get_safe modify_safe ordinary_safe)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

/-- Actual SDK Server work forwards only ordinary native randomness to the joint interface. -/
theorem server_safe (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) :
    Safe (RegistrationNativeIdentityMain.server work : M n KemSK mlSource Value) := ordinary_safe _

/-- Actual shared-World work executes no generated-identity operation. -/
theorem world_safe (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    Safe (RegistrationNativeIdentityMain.world work : M n KemSK mlSource Value) := server_safe _

/-- Record lookup, outer admission and every native record path contain no identity reveal. -/
theorem record_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    Safe (RegistrationNativeIdentityMain.record setup wire route query : M n KemSK mlSource _) := by
  cases query with
  | inl query => exact world_safe _
  | inr query =>
      rcases query with ⟨index, query⟩
      cases query with
      | inl plaintext =>
          unfold RegistrationNativeIdentityMain.record
          apply bind_safe _ _ get_safe
          intro before
          cases before.beacons[index]? with
          | none => exact pure_safe _
          | some selected => exact world_safe _
      | inr raw =>
          unfold RegistrationNativeIdentityMain.record
          apply bind_safe _ _ get_safe
          intro before
          cases before.beacons[index]? with
          | none => exact pure_safe _
          | some selected => exact world_safe _

/-- Every concrete typed native operation uses only creation, ordinary joint signing/static DH, uniform randomness and candidate reports. -/
theorem handler_safe (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Safe (RegistrationNativeIdentityMain.handler (n := n) setup checks wire route representation created credential query) := by
  cases query with
  | inl coin => exact world_safe _
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativeIdentityMainNoRevealBeacon.beacon_safe setup checks representation created _
          (RegistrationNativeIdentityNoReveal.create_safe setup edPin mlPin keyId)
    | bundle owner =>
        exact RegistrationNativeIdentityMainNoRevealBeacon.beacon_safe setup checks representation created _
          (RegistrationNativeIdentityNoReveal.bundle_safe setup wire owner)
    | accept packet =>
        unfold RegistrationNativeIdentityMain.handler
        apply bind_safe _ _ (RegistrationNativeIdentityMainNoRevealCore.report_safe packet)
        intro reported
        apply bind_safe _ _ (modify_safe _)
        intro result
        exact server_safe _
    | build session application => exact server_safe _
    | finish owner packet =>
        exact RegistrationNativeIdentityMainNoRevealBeacon.beacon_safe setup checks representation created _
          (RegistrationNativeIdentityNoReveal.finish_safe setup wire owner packet)
    | hmac key message => exact pure_safe _
    | hash bytes => exact world_safe _
    | serverSend keyId plaintext => exact record_safe setup wire route (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record_safe setup wire route (.inl (.inr raw))
    | beaconSend owner plaintext => exact record_safe setup wire route (.inr (owner, .inl plaintext))
    | beaconRaw owner raw => exact record_safe setup wire route (.inr (owner, .inr raw))

/-- Arbitrary adaptive typed native execution preserves structural non-reveal safety. -/
theorem program_safe (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Safe (simulateQ (RegistrationNativeIdentityMain.handler (n := n) setup checks wire route representation created credential) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_safe value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (handler_safe setup checks wire route representation created credential query) ih

/-- The complete original raw-CBOR and secrecy-ledger program cannot introduce a generated-identity reveal through compilation. -/
theorem run_safe (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK mlSource) :
    AllQueriesSatisfy (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work before) Allowed :=
  mapped _ _ Allowed (program_safe setup checks wire route representation created credential _ before)

/-- The actual generated-startup ordinary joint client, with any native public adversary and ledger observer, contains no reveal request on any branch. -/
theorem client_safe (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) :
    AllQueriesSatisfy (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event) Allowed := by
  unfold RegistrationNativeIdentityMainProfile.client
  apply allQueriesSatisfy_bind (RegistrationNativeIdentityMainNoRevealCore.coins_safe _)
  intro initialized
  cases initialized with
  | none => trivial
  | some initial =>
      apply allQueriesSatisfy_bind (run_safe setup checks wire route representation initial.created initial.credential bounds mode _ _)
      intro result
      apply allQueriesSatisfy_bind (RegistrationNativeIdentityMainNoRevealCore.emit_safe _)
      intro _
      trivial

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.server_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.server_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.world_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.world_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.record_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.record_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.handler_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.program_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.run_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.run_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.client_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal.client_safe
