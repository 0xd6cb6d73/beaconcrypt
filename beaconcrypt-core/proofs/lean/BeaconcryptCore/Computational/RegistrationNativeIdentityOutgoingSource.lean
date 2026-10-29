-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster
import BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityRoles

/-! The outgoing indexed signing callback is the actual native source callback after private credential realization. The proof keeps current-owner histories, the reached Env and complete native Context; the private service transcript records each signing attempt before attached-buffer packing. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner Ambient)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def signature (credential : RegistrationNativeIdentityInterface.Credential) (message : Pqxdh.Bytes) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (Option PqxdhEd25519EufCma.Ed25519Signature) :=
  StateT.lift (StateT.lift (RegistrationNativeIdentityInterface.sign (Ambient n KemSK) credential message))

theorem signature_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (credential : RegistrationNativeIdentityInterface.Credential) (seed : IdentitySeed) (message : Pqxdh.Bytes)
    (found : seeds[credential.handle]? = some seed) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (signature credential message) (pure (some (setup.joint.sign seed message))) := by
  intro before prior
  have present : before.2.identities.seeds[credential.handle]? = some seed := by rw [prior]; exact found
  simp only [runNew, signature, StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map]
  rw [RegistrationNativeIdentityWorldServices.sign_source setup checks representation created credential seed message before.2 present]
  simp only [runOld, StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq, view]

theorem signature_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeIdentityInterface.Credential) (message : Pqxdh.Bytes) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created (signature credential message) := by
  intro before result supported
  simp only [runNew, signature, StateT.run_lift, StateT.run_map, bind_pure_comp,
    simulateQ_map, RegistrationNativeIdentityInterface.sign, simulateQ_spec_query] at supported
  rw [RegistrationNativeIdentityWorld.service_source] at supported
  simp only [map_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

theorem history_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (message : Pqxdh.Bytes) (value : PqxdhEd25519EufCma.Ed25519Signature) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.logEd index message value)
      (RegistrationNativeBeaconFrontend.logEd index message value) := by
  apply related_modify setup checks representation created seeds
  intro current
  exact RegistrationNativeIdentitySourceRoster.history_source ⟨seeds, []⟩ current index message value

theorem history_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (message : Pqxdh.Bytes) (value : PqxdhEd25519EufCma.Ed25519Signature) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.logEd index message value) :=
  keeps_modify setup checks representation created _

/-- Every actual outgoing Ed callback is the source callback under this exact generated credential, including mismatch rejection and failed attached-buffer packing. -/
theorem ed_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (request : registration.Ed25519SigningRequest)
    (found : seeds[owner.identity.handle]? = some seed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.outgoing setup source index owner (.inr request))
      (RegistrationNativeBeaconFrontend.outgoing setup source index (RegistrationNativeIdentityFrontend.restore seed owner) (.inr request)) := by
  change Related (Value := RegistrationSigningShared.SignReply) setup checks representation created seeds _ _
  classical
  let message := TranscriptAuthParts.absSlice request.message
  let next : Option PqxdhEd25519EufCma.Ed25519Signature → RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source RegistrationSigningShared.SignReply
    | none => pure .None
    | some value => do
        RegistrationNativeIdentityFrontend.logEd index message value
        pure (RegistrationAuthenticationShared.openedBytes (some (value.toList ++ message)))
  let original : Option PqxdhEd25519EufCma.Ed25519Signature → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary RegistrationSigningShared.SignReply
    | none => pure .None
    | some value => do
        RegistrationNativeBeaconFrontend.logEd index message value
        pure (RegistrationAuthenticationShared.openedBytes (some (value.toList ++ message)))
  by_cases matched : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · have later (value : Option PqxdhEd25519EufCma.Ed25519Signature) :
        Related setup checks representation created seeds (next value) (original value) := by
      cases value with
      | none => exact related_pure setup checks representation created seeds (core.option.Option.None : RegistrationSigningShared.SignReply)
      | some value =>
          exact related_bind setup checks representation created seeds _ _ _ _
            (history_source setup checks representation created seeds index message value)
            (history_keeps setup checks representation created index message value)
            (fun _ => related_pure setup checks representation created seeds _)
    have assembled := related_bind setup checks representation created seeds
      (signature owner.identity message) (pure (some (setup.joint.sign seed message))) next original
      (signature_source setup checks representation created seeds owner.identity seed message found)
      (signature_keeps setup checks representation created owner.identity message) later
    simp only [RegistrationNativeIdentityFrontend.outgoing, RegistrationNativeBeaconFrontend.outgoing,
      RegistrationNativeIdentityFrontend.restore, ← publicKey, ite_eq_left matched,
      signature, next, original, pure_bind, message] at assembled ⊢
    convert assembled using 1 <;> rfl
  · simpa only [RegistrationNativeIdentityFrontend.outgoing, RegistrationNativeBeaconFrontend.outgoing,
      RegistrationNativeIdentityFrontend.restore, ← publicKey, ite_eq_right matched] using
      (related_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
        (core.option.Option.None : RegistrationSigningShared.SignReply))

theorem ed_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (request : registration.Ed25519SigningRequest) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (RegistrationNativeIdentityFrontend.outgoing setup source index owner (.inr request)) := by
  classical
  by_cases matched : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · simp only [RegistrationNativeIdentityFrontend.outgoing, ite_eq_left matched]
    apply keeps_bind setup checks representation created _ _ (signature_keeps setup checks representation created owner.identity _)
    intro value
    cases value with
    | none => exact keeps_pure setup checks representation created _
    | some value =>
        exact keeps_bind setup checks representation created _ _
          (history_keeps setup checks representation created index _ value)
          (fun _ => keeps_pure setup checks representation created _)
  · simpa only [RegistrationNativeIdentityFrontend.outgoing, ite_eq_right matched] using
      (keeps_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
        (core.option.Option.None : RegistrationSigningShared.SignReply))

/-- Hash, ML signing and generated-handle Ed signing callbacks jointly recover the actual original native outgoing service. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (found : seeds[owner.identity.handle]? = some seed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.outgoing setup source index owner query)
      (RegistrationNativeBeaconFrontend.outgoing setup source index (RegistrationNativeIdentityFrontend.restore seed owner) query) := by
  cases query with
  | inl query => cases query with
    | hash request =>
        exact RegistrationNativeIdentityCommonSource.effect_source setup checks representation created seeds _
    | sign request payload digest =>
        simp only [RegistrationNativeIdentityFrontend.outgoing, RegistrationNativeBeaconFrontend.outgoing,
          RegistrationNativeIdentityFrontend.restore]
        apply related_bind setup checks representation created seeds _ _ _ _
          (RegistrationNativeIdentityCommonSource.sample_source setup checks representation created seeds _)
          (RegistrationNativeIdentityCommonSource.sample_keeps setup checks representation created _)
        intro reply
        exact related_bind setup checks representation created seeds _ _ _ _
          (RegistrationNativeIdentityCommonSource.update_source setup checks representation created seeds _)
          (RegistrationNativeIdentityCommonSource.update_keeps setup checks representation created _)
          (fun _ => related_pure setup checks representation created seeds reply)
  | inr request => exact ed_source setup checks representation created seeds index owner seed request found publicKey

theorem query_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (RegistrationNativeIdentityFrontend.outgoing setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _
    | sign request payload digest =>
        simp only [RegistrationNativeIdentityFrontend.outgoing]
        exact keeps_bind setup checks representation created _ _
          (RegistrationNativeIdentityCommonSource.sample_keeps setup checks representation created _)
          (fun _ => keeps_bind setup checks representation created _ _
            (RegistrationNativeIdentityCommonSource.update_keeps setup checks representation created _)
            (fun _ => keeps_pure setup checks representation created _))
  | inr request => exact ed_keeps setup checks representation created index owner request

/-- Complete native Init execution retains all three signing attempts, shared hashes, ML receipts, dynamic encoder results and every failure path under the same source interpretation. -/
theorem program_source {Value : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (found : seeds[owner.identity.handle]? = some seed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (simulateQ (RegistrationNativeIdentityFrontend.outgoing setup source index owner) work)
      (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index (RegistrationNativeIdentityFrontend.restore seed owner)) work) :=
  related_program setup checks representation created seeds _ _
    (query_source setup checks representation created seeds index owner seed found publicKey)
    (query_keeps setup checks representation created index owner) work

theorem program_keeps {Value : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (simulateQ (RegistrationNativeIdentityFrontend.outgoing setup source index owner) work) :=
  keeps_program setup checks representation created _ (query_keeps setup checks representation created index owner) work

/-- The source correspondence includes the actual complete outgoing Init controller with its generated public fields and dynamic wire encoder. -/
theorem init_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : seeds[owner.identity.handle]? = some seed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (simulateQ (RegistrationNativeIdentityFrontend.outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
          (RegistrationNativeIdentityFrontend.inputs owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey))
      (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index (RegistrationNativeIdentityFrontend.restore seed owner))
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
          (RegistrationNativeBeaconFrontend.inputs setup (RegistrationNativeIdentityFrontend.restore seed owner))
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)) := by
  rw [← RegistrationNativeIdentityRoles.inputs_source setup owner seed publicKey]
  exact program_source setup checks representation created seeds index owner seed found publicKey _

theorem init_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (simulateQ (RegistrationNativeIdentityFrontend.outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
          (RegistrationNativeIdentityFrontend.inputs owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)) :=
  program_keeps setup checks representation created index owner _

end BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.signature_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.signature_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.signature_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.signature_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.history_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.history_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.history_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.history_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.ed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.ed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.ed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.ed_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.query_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.init_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.init_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.init_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource.init_keeps
