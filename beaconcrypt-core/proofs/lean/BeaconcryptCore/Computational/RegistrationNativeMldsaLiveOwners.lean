-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation

/-! Reached opaque ML credentials stay live through actual owner lifecycle callbacks. Immutable owner metadata retains the full credential; the only creation suffix appends the actual generated credential after all source preflights. No key injectivity or closed dummy-source equality is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaPoolMap (CredentialLive OwnersLive StateLive)
open RegistrationNativeBeaconFrontend
open RegistrationNativeOwnerFields (metadata)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

/-- Equality of the actual immutable owner snapshots retains the complete opaque ML credential and its reached private row. -/
theorem metadata_live (pool : Pool source) (before after : State (handleSource source))
    (same : after.map metadata = before.map metadata) (live : OwnersLive source pool before) :
    OwnersLive source pool after := by
  intro selected member
  have earlier : metadata selected ∈ before.map metadata := by
    rw [← same]
    exact List.mem_map.mpr ⟨selected, member, rfl⟩
  obtain ⟨old, oldMember, oldSame⟩ := List.mem_map.mp earlier
  have credential := congrArg (fun owner : Owner (handleSource source) => owner.mldsa) oldSame
  change old.mldsa = selected.mldsa at credential
  exact credential ▸ live old oldMember

/-- Every complete actual outgoing Init callback program retains all already-live native ML handles, including failed signing/publication paths. -/
theorem outgoing (setup : Setup base KemSK) (pool : Pool source) (index : Nat)
    (owner : Owner (handleSource source)) (work : OracleComp RegistrationBeaconInitExecutor.Spec Value)
    (owners : State (handleSource source)) (env : EnvState Auxiliary)
    (result : (Value × State (handleSource source)) × EnvState Auxiliary)
    (live : OwnersLive source pool owners)
    (supported : result ∈ support
      (((simulateQ (RegistrationNativeBeaconFrontend.outgoing (n := n) setup (handleSource source) index owner) work).run owners).run env)) :
    OwnersLive source pool result.1.2 :=
  metadata_live source pool owners result.1.2
    (RegistrationNativeOwnerFields.outgoing_metadata setup (handleSource source) index owner work owners env result supported) live

/-- Both actual successful and failed bundles preserve every reached live ML credential. -/
theorem bundle (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (pool : Pool source) (index : Nat)
    (owners : State (handleSource source)) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State (handleSource source)) × EnvState Auxiliary)
    (live : OwnersLive source pool owners)
    (supported : result ∈ support (((RegistrationNativeBeaconFrontend.bundle (n := n) setup (handleSource source) wire index).run owners).run env)) :
    OwnersLive source pool result.1.2 :=
  metadata_live source pool owners result.1.2
    (RegistrationNativeOwnerFields.bundle_metadata setup (handleSource source) wire index owners env result supported) live

/-- Actual terminal finish, including malformed input and consumed-owner failure, preserves every reached live ML credential. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (pool : Pool source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : State (handleSource source)) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State (handleSource source)) × EnvState Auxiliary)
    (live : OwnersLive source pool owners)
    (supported : result ∈ support (((RegistrationNativeBeaconFrontend.finish (n := n) setup (handleSource source) wire index packet).run owners).run env)) :
    OwnersLive source pool result.1.2 :=
  metadata_live source pool owners result.1.2
    (RegistrationNativeOwnerFields.finish_metadata setup (handleSource source) wire index packet owners env result supported) live

private theorem beacon_live (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (pool : Pool source)
    (work : M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value)
    (law : ∀ owners env result, OwnersLive source pool owners →
      result ∈ support ((work.run owners).run env) → OwnersLive source pool result.1.2)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : Value × RegistrationNativeExperiment.State n KemSK (handleSource source))
    (live : StateLive source pool before)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    StateLive source pool result.2 := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  apply law before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1 live
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created (handleSource source)) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

def NonCreate : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.create _ _ _) => False
  | _ => True

/-- All actual typed callbacks except ML generation retain the reached live-owner invariant; bundle and finish use exact full-credential metadata, while Server/record calls retain the literal owner list. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (handleSource source)) (pool : Pool source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source))
    (live : StateLive source pool before)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created (handleSource source) credential query).run before)) :
    StateLive source pool result.2 := by
  have ordinary (good : RegistrationNativeStatePreservation.Ordinary query) : StateLive source pool result.2 := by
    have same := RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation created credential
      query good before result supported
    change OwnersLive source pool result.2.beacons
    rw [same.2]
    exact live
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create _ _ _ => exact False.elim allowed
    | bundle index =>
        exact beacon_live source setup checks representation created pool _
          (bundle source setup wire pool index) before result live supported
    | finish index packet =>
        exact beacon_live source setup checks representation created pool _
          (finish source setup wire pool index packet) before result live supported
    | _ => exact ordinary trivial

private def Ensures (pool : Pool source)
    (work : M n KemSK (handleSource source) Auxiliary Value) (post : Value → Prop) : Prop :=
  ∀ owners env result, OwnersLive source pool owners →
    result ∈ support ((work.run owners).run env) → OwnersLive source pool result.1.2 ∧ post result.1.1

private theorem pure_ensures (pool : Pool source) (value : Value) (post : Value → Prop) (good : post value) :
    Ensures source pool (pure value : M n KemSK (handleSource source) Auxiliary Value) post := by
  intro owners env result live supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact ⟨live, good⟩

private theorem bind_ensures (pool : Pool source)
    (work : M n KemSK (handleSource source) Auxiliary Value)
    (next : Value → M n KemSK (handleSource source) Auxiliary Next) (post : Value → Prop) (final : Next → Prop)
    (first : Ensures source pool work post)
    (rest : ∀ value, post value → Ensures source pool (next value) final) :
    Ensures source pool (work >>= next) final := by
  intro owners env result live supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  obtain ⟨current, good⟩ := first owners env middle live queried
  exact rest middle.1.1 good middle.1.2 middle.2 result current continued

private theorem lift_ensures (pool : Pool source)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Ensures source pool (StateT.lift work : M n KemSK (handleSource source) Auxiliary Value) (fun _ => True) := by
  intro owners env result live supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  exact ⟨live, trivial⟩

private theorem simulate_ensures {Query : Type} {queries : OracleSpec Query} (pool : Pool source)
    (implementation : QueryImpl queries (M n KemSK (handleSource source) Auxiliary))
    (law : ∀ query, Ensures source pool (implementation query) (fun _ => True)) (work : OracleComp queries Value) :
    Ensures source pool (simulateQ implementation work) (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_ensures source pool value _ trivial
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_ensures source pool _ _ _ _ (law query) (fun value _ => ih value)

private theorem sample_ensures (pool : Pool source) (draw : ProbComp Value) :
    Ensures source pool (sample (n := n) (KemSK := KemSK) (mldsaSource := handleSource source) (Auxiliary := Auxiliary) draw)
      (fun _ => True) := by
  unfold sample
  exact simulate_ensures source pool (fun (query : unifSpec.Domain) => effect (.inl query))
    (fun _ => lift_ensures source pool _) draw

private theorem get_ensures (pool : Pool source) :
    Ensures source pool (get : M n KemSK (handleSource source) Auxiliary (State (handleSource source)))
      (OwnersLive source pool) := by
  intro owners env result live supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact ⟨live, live⟩

private theorem set_ensures (pool : Pool source) (owners : State (handleSource source))
    (live : OwnersLive source pool owners) :
    Ensures source pool (set owners : M n KemSK (handleSource source) Auxiliary Unit) (fun _ => True) := by
  intro current env result _old supported
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact ⟨live, trivial⟩

private def PreparedLive (pool : Pool source) : RustM (Option (Prepared (handleSource source))) → Prop
  | .ok (some prepared) => CredentialLive source pool prepared.credentials
  | _ => True

private theorem afterGenerated_ensures (pool : Pool source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64)
    (generated : Option (RegistrationNativeMldsa.Credential (handleSource source)))
    (fresh : ∀ credential ∈ generated, CredentialLive source pool credential) :
    Ensures source pool (RegistrationNativeMldsaCreation.afterGenerated (n := n) (KemSK := KemSK) edPin mlPin keyId generated)
      (PreparedLive source pool) := by
  unfold RegistrationNativeMldsaCreation.afterGenerated
  cases generated with
  | none => exact pure_ensures source pool _ _ trivial
  | some credential =>
      have generatedLive : CredentialLive source pool credential := fresh credential (by simp)
      dsimp only
      cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error | div => exact pure_ensures source pool _ _ trivial
      | ok pending =>
          dsimp only
          cases pending.request with
          | fail error | div => exact pure_ensures source pool _ _ trivial
          | ok request =>
              apply bind_ensures source pool _ _ (fun _ => True) _ (lift_ensures source pool _)
              intro digest _good
              cases pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error | div => exact pure_ensures source pool _ _ trivial
              | ok reply => cases reply with
                | none => exact pure_ensures source pool _ _ trivial
                | some pin =>
                    apply bind_ensures source pool _ _ (fun _ => True) _ (sample_ensures source pool _)
                    intro identity _good
                    apply bind_ensures source pool _ _ (fun _ => True) _ (sample_ensures source pool _)
                    intro prekey _good
                    exact pure_ensures source pool _ _ generatedLive

private theorem appendBorn_ensures (setup : Setup base KemSK) (pool : Pool source)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey : PqxdhJointGapDh.ScalarBytes)
    (fresh : CredentialLive source pool credential) :
    Ensures source pool (appendBorn (n := n) (Auxiliary := Auxiliary) setup (handleSource source)
      edPin keyId pin credential identity prekey) (fun _ => True) := by
  unfold appendBorn
  apply bind_ensures source pool _ _ (fun _ => True) _ (lift_ensures source pool _)
  intro born _good
  apply bind_ensures source pool _ _ (fun _ => True) _ (lift_ensures source pool _)
  intro worldOwner _good
  apply bind_ensures source pool _ _ (OwnersLive source pool) _ (get_ensures source pool)
  intro owners live
  apply bind_ensures source pool _ _ (fun _ => True) _
    (set_ensures source pool _ (RegistrationNativeMldsaPoolMap.owners_append source pool owners _ live fresh))
  intro ignored _good
  exact pure_ensures source pool _ _ trivial

/-- The actual generated-key suffix preserves every old live owner and appends only the supplied reached live credential, through all source preflight and KEM-birth failures. -/
theorem createSuffix (setup : Setup base KemSK) (pool : Pool source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (generated : Option (RegistrationNativeMldsa.Credential (handleSource source)))
    (fresh : ∀ credential ∈ generated, CredentialLive source pool credential)
    (owners : State (handleSource source)) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Nat) × State (handleSource source)) × EnvState RegistrationServerRoleBackend.State)
    (live : OwnersLive source pool owners)
    (supported : result ∈ support
      (((RegistrationNativeMldsaCreation.createSuffix (n := n) setup edPin mlPin keyId generated).run owners).run env)) :
    OwnersLive source pool result.1.2 := by
  have law : Ensures source pool
      (RegistrationNativeMldsaCreation.createSuffix (n := n) setup edPin mlPin keyId generated) (fun _ => True) := by
    unfold RegistrationNativeMldsaCreation.createSuffix
    apply bind_ensures source pool _ _ (PreparedLive source pool) _
      (afterGenerated_ensures source pool edPin mlPin keyId generated fresh)
    intro prepared good
    cases prepared with
    | fail error | div => exact pure_ensures source pool _ _ trivial
    | ok result => cases result with
      | none => exact pure_ensures source pool _ _ trivial
      | some prepared =>
          exact appendBorn_ensures source setup pool edPin keyId prepared.pin
            prepared.credentials prepared.identity prepared.prekey good
  exact (law owners env result live supported).1

/-- Closing the original generated-key suffix preserves the reached complete native owner invariant at that same current table. -/
theorem source_createSuffix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (pool : Pool source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (generated : Option (RegistrationNativeMldsa.Credential (handleSource source)))
    (fresh : ∀ credential ∈ generated, CredentialLive source pool credential)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source))
    (live : StateLive source pool before)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId generated)).run before)) :
    StateLive source pool result.2 :=
  beacon_live source setup checks representation created pool _
    (fun owners env result old reached => createSuffix source setup pool edPin mlPin keyId generated fresh owners env result old reached)
    before result live supported

end BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.metadata_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.metadata_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.createSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.createSuffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.source_createSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners.source_createSuffix
