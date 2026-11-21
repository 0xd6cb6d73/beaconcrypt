-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeWire
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! Successful native outgoing Init publication retains the original generated classical identity through all three Ed signatures and request hashing. The original explicit four-field wire readback contract recovers the exact identity from public bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityPublication
open PqxdhEd25519EufCma (Ed25519PublicKey)
open PqxdhEd25519EufCma (encodedIdentity parseIdentity)
open BeaconcryptCore.Refinement
open RegistrationBeaconInitExecutor
variable {Encoded : Type}

def Started (key : Ed25519PublicKey) (state : registration.BeaconInitState) : Prop :=
  absBytes state.started.message.identity_key = encodedIdentity key

def Signed (key : Ed25519PublicKey) (state : registration.BeaconInitState) : Prop :=
  absBytes state.started.message.identity_key = encodedIdentity key

/-- An actual successful writer invocation and the exact tagged identity it received. -/
def PublishedKey (encode : registration.InitView → core.option.Option Encoded)
    (key : Ed25519PublicKey) (published : registration.PublishedBeaconInit Encoded) : Prop :=
  ∃ view, encode view = .Some published.encoded ∧
    absBytes view.fields.identity_key = encodedIdentity key

attribute [local irreducible] RegistrationBeaconInitExecutor.begin
  registration.BeaconInitHash.resume

private theorem continue_support {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (continueWith action next)) :
    ∃ value, action = .ok value ∧ .ok (.Ok published) ∈ support (next value) := by
  cases action <;> simp_all [continueWith]

private theorem started_validation (input : pqxdh.InitKex) (verified : pqxdh.VerifiedInitKex)
    (validated : pqxdh.validate_init_kex input = .ok (.Ok verified)) :
    absBytes input.identity_key = encodedIdentity (RegistrationRootInput.identity verified) := by
  have parsed := ((PqxdhHeadlineBridges.validate_init_kex_bridge input).2.1 verified).mp validated
  simp only [PqxdhHeadlineBridges.parsedFields, PqxdhHeadlineBridges.parsedBytes,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at parsed
  obtain ⟨identity, identityParsed, prekey, _, oneTime, _, pq, _, result⟩ := parsed
  have same := congrArg (fun value => value.1) result
  have identityResult : parseIdentity (absBytes input.identity_key) =
      some (RegistrationRootInput.identity verified) := by
    simpa only [PqxdhHeadlineBridges.typedVerified, RegistrationRootInput.identity, PqxdhPhase2InputBytes.word] using
      identityParsed.trans (congrArg some same)
  exact (PqxdhEd25519EufCma.parseIdentity_eq_some_iff _ _).mp identityResult

private theorem ed_started (key : Ed25519PublicKey)
    (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconEd25519Signing) (prior : Started key pending.state)
    (actual : pending.resume reply = .ok (.Ed25519SigningRequested next)) : Started key next.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases stage : pending.stage
  all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
  · exact (congrArg (Started key) progress.2.2.2).mpr prior
  · exact (congrArg (Started key) progress.2.2.2).mpr prior
  · exact progress.2.elim

private theorem ed_signed (key : Ed25519PublicKey)
    (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconInitHash) (prior : Started key pending.state)
    (actual : pending.resume reply = .ok (.HashRequested next)) : Signed key next.state := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  simp only [RegistrationSigning.EdReplyTransition] at progress
  exact (congrArg (Started key) progress.2.2.2).mpr prior

private theorem ready_key (encode : registration.InitView → core.option.Option Encoded)
    (key : Ed25519PublicKey) (pending : registration.BeaconInitReady)
    (published : registration.PublishedBeaconInit Encoded) (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (ready encode pending)) : PublishedKey encode key published := by
  obtain ⟨view, requested, returned⟩ := continue_support pending.message _ published supported
  have fields : view.fields.identity_key = pending.state.started.message.identity_key := by
    simp only [registration.BeaconInitReady.message, RegistrationSigningContinuations.retained_fields_exact,
      bind_tc_ok, RustM.ok.injEq] at requested
    cases requested
    rfl
  simp only [support_pure, Set.mem_singleton_iff] at returned
  cases encoded : encode view with
  | none =>
      rw [encoded,RegistrationSigningContinuations.failed_publication_preserves_fresh] at returned
      cases returned
  | some bytes =>
      obtain ⟨actual,ran,_control,_pin,_hash,_identity,_pre,_one,_pq,output⟩ :=
        RegistrationSigningContinuations.publication_retains_exact_request pending bytes
      have same : actual = published := by
        have current := returned
        rw [encoded] at current
        simpa using ran.symm.trans current.symm
      subst actual
      exact ⟨view,output ▸ encoded,by simpa only [fields,Signed] using prior⟩

private theorem hash_key (encode : registration.InitView → core.option.Option Encoded)
    (key : Ed25519PublicKey) (pending : registration.BeaconInitHash)
    (published : registration.PublishedBeaconInit Encoded) (prior : Signed key pending.state)
    (supported : .ok (.Ok published) ∈ support (fromHash encode pending)) : PublishedKey encode key published := by
  obtain ⟨request, _, called⟩ := continue_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨digest, _, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published continued
  obtain ⟨next, actual, retained, _⟩ := RegistrationSigningContinuations.beacon_init_hash_some_exact
    pending (RegistrationAuthenticationShared.digestArray digest)
  rw [actual] at resumed
  cases resumed
  exact ready_key encode key next published (retained ▸ prior) continued

private theorem ed_key (encode : registration.InitView → core.option.Option Encoded)
    (key : Ed25519PublicKey) (pending : registration.BeaconEd25519Signing)
    (published : registration.PublishedBeaconInit Encoded) (prior : Started key pending.state)
    (supported : .ok (.Ok published) ∈ support (fromEd encode pending)) : PublishedKey encode key published := by
  rw [fromEd.eq_def] at supported
  obtain ⟨request, _, called⟩ := continue_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨reply, _, continued⟩ := called
  cases actual : pending.resume reply with
  | fail error => rw [actual] at continued; simp at continued
  | div => rw [actual] at continued; simp at continued
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
        rw [actual] at continued
        exact ed_key encode key next published (ed_started key pending reply next prior actual) continued
    | HashRequested next =>
        rw [actual] at continued
        exact hash_key encode key next published (ed_signed key pending reply next prior actual) continued
    | _ => rw [actual] at continued; simp at continued
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- The actual complete outgoing controller publishes its original classical identity after every signing and hashing stage. -/
theorem begin_key (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (begin encode control inputs coins pin)) :
    PublishedKey encode (PqxdhPhase2InputBytes.word inputs.identity_public_key) published := by
  unfold RegistrationBeaconInitExecutor.begin at supported
  obtain ⟨effect, actual, continued⟩ := continue_support
    (registration.begin_beacon_init control inputs coins pin) _ published supported
  obtain ⟨started, startedRun, validated, _, _⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact
    control inputs coins pin
  have same := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  rw [beginRun] at actual
  split_ifs at actual
  · cases actual; simp at continued
  · cases actual
    refine ed_key encode _ _ published ?_ continued
    exact started_validation _ _ validated

/-- Stateful interpretation retains the same successful writer receipt without any primitive-correctness or signing-origin assumption. -/
theorem simulated_key {State : Type} (implementation : QueryImpl Spec (StateT State ProbComp))
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin)).run before)) :
    PublishedKey encode (PqxdhPhase2InputBytes.word inputs.identity_public_key) published := by
  apply begin_key encode control inputs coins pin published
  apply OracleComp.support_simulateQ_run'_subset implementation (begin encode control inputs coins pin) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

/-- Native wire readback recovers the same original classical identity from successful public bytes. -/
theorem decoded_key (wire : RegistrationNativeWire.Wire) (readback : RegistrationNativeWire.InitReadBack wire)
    (key : Ed25519PublicKey) (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (receipt : PublishedKey wire.encodeInit key published) :
    ∃ packet, RegistrationNativeWire.readInit wire published.encoded = some packet ∧
      parseIdentity (absBytes packet.identity_key) = some key := by
  obtain ⟨view, written, payload⟩ := receipt
  refine ⟨RegistrationNativeWire.initPacket view, readback view published.encoded written, ?_⟩
  simpa only [RegistrationNativeWire.initPacket, payload] using
    PqxdhEd25519EufCma.parseIdentity_encodedIdentity key

open RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeWire (Wire)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

private theorem outgoing_identity (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (selected : Owner mlSource) (oneTime : ScalarBytes)
    (owners ownersAfter : State mlSource) (env envAfter : EnvState Auxiliary)
    (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (reached : ((.ok (.Ok published), ownersAfter), envAfter) ∈ support
      (((simulateQ (outgoing (n := n) setup mlSource index selected)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨selected.pin.binding⟩ (inputs setup selected)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ selected.pin)).run owners).run env)) :
    RegistrationNativeIdentityPublication.PublishedKey wire.encodeInit (setup.joint.publicKeys selected.identitySeed).ed25519 published := by
  have original := RegistrationNativeBeaconPublication.nested_support mlSource (outgoing setup mlSource index selected)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨selected.pin.binding⟩ (inputs setup selected)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ selected.pin)
    owners ownersAfter env envAfter (.ok (.Ok published)) reached
  simpa only [inputs, PqxdhPhase2InputBytes.word_rootArray] using RegistrationNativeIdentityPublication.begin_key wire.encodeInit
    ⟨selected.pin.binding⟩ (inputs setup selected)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ selected.pin published original

private theorem bundle_identity (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (owners ownersAfter : State mlSource) (env envAfter : EnvState Auxiliary)
    (bytes : Pqxdh.Bytes)
    (reached : ((.ok (some bytes), ownersAfter), envAfter) ∈ support
      (((bundle (n := n) setup mlSource wire index).run owners).run env)) :
    ∃ selected published, owners[index]? = some selected ∧ published.encoded = bytes ∧
      RegistrationNativeIdentityPublication.PublishedKey wire.encodeInit (setup.joint.publicKeys selected.identitySeed).ed25519 published := by
  obtain ⟨selected, oneTime, published, beforeOwners, beforeEnv, duringOwners, duringEnv,
    found, encoded, called⟩ := RegistrationNativeKemBirthOwners.bundle_receipt
      setup mlSource wire index owners env bytes ownersAfter envAfter reached
  exact ⟨selected, published, found, encoded,
    outgoing_identity setup mlSource wire index selected oneTime beforeOwners duringOwners beforeEnv duringEnv published called⟩

/-- The full source wrapper's public encoded Init recovers its actual original owner's generated classical identity under the native wire readback contract. -/
theorem source_bundle_identity (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (readback : RegistrationNativeWire.InitReadBack wire) (index : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (bytes : Pqxdh.Bytes)
    (reached : (.ok (some bytes), after) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation created
        (bundle setup mlSource wire index)).run before)) :
    ∃ selected packet, before.beacons[index]? = some selected ∧
      RegistrationNativeWire.readInit wire bytes = some packet ∧
      parseIdentity (absBytes packet.identity_key) = some (setup.joint.publicKeys selected.identitySeed).ed25519 := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨⟨⟨⟨value, ownersAfter⟩, envAfter⟩, sourceAfter⟩, interpreted, returned⟩ := reached
  have valueEq : value = .ok (some bytes) := congrArg Prod.fst returned.symm
  subst value
  have original : ((.ok (some bytes), ownersAfter), envAfter) ∈ support
      (((bundle (n := n) setup mlSource wire index).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst interpreted
  obtain ⟨selected, published, found, encoded, receipt⟩ := bundle_identity setup mlSource wire index _ _ _ _ bytes original
  obtain ⟨packet, decoded, sameKey⟩ := RegistrationNativeIdentityPublication.decoded_key wire readback (setup.joint.publicKeys selected.identitySeed).ed25519 published receipt
  exact ⟨selected, packet, found, encoded ▸ decoded, sameKey⟩


end BeaconcryptCore.Computational.RegistrationNativeIdentityPublication


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.begin_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.begin_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.simulated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.simulated_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.decoded_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.decoded_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.source_bundle_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublication.source_bundle_identity
