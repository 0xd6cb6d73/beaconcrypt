-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFinishRootReceipt
import BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts
import BeaconcryptCore.Computational.RegistrationNativeServerPublicContents
import BeaconcryptCore.Computational.RegistrationNativeStagedResponseOrigin

/-! Outside the original protected-ML issuance and shared-cache collision events, actual initialized native finish has an earlier same-run consumed Server token with exactly the same derived root, and retains the actual Beacon initializer, consumed receive kernel, metadata and application. Local key/control/identity invariants and public stage correspondence are derived from the reached source path. Completed Server peer installation and cross-role initializer/application equality are separate claims. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem path_cut {S κ : Type} {spec : OracleSpec κ} (implementation : QueryImpl spec (StateT S ProbComp))
    {first last : S} (leading trailing : List (Call spec S)) (call : Call spec S)
    (actual : Path implementation first (leading ++ call :: trailing) last) :
    Path implementation first leading call.before ∧ RegistrationNativeStageTrace.Executed implementation call ∧
      Path implementation call.after trailing last := by
  induction leading generalizing first with
  | nil => cases actual with
    | cons head called rest final following => exact ⟨.nil _, called, following⟩
  | cons head rest ih => cases actual with
    | cons current called remaining final following =>
      obtain ⟨beforeCut, executed, afterCut⟩ := ih following
      exact ⟨.cons head called _ _ beforeCut, executed, afterCut⟩

private theorem take_pin (handle : Nat) (before current : RegistrationServerFrontendCompiler.State n)
    (token : peer.ConsumedRegistration)
    (taken : RegistrationServerSdkSource.take handle before = (some token, current)) : current.pin = before.pin := by
  unfold RegistrationServerSdkSource.take at taken
  cases found : before.sessions[handle]? with
  | none => simp only [found, Prod.mk.injEq] at taken; cases taken.1
  | some value => cases value with
    | none => simp only [found, Prod.mk.injEq] at taken; cases taken.1
    | some moved =>
      simp only [found, Prod.mk.injEq] at taken
      exact (congrArg (fun state => state.pin) taken.2).symm

private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State V) (before : Native) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- The exact root-bearing Beacon initializer and consumed receive state at successful source finish. -/
def Outcome (token : peer.ConsumedRegistration) (pending : registration.BeaconPending) (application : Pqxdh.Bytes) : Prop :=
    ∃ (capability : agreement.BeaconAgreement) (established : registration.CompletedBeacon)
      (initial : registration.BeaconInitialKdf) (aead : registration.BeaconRecordAead) (plaintext : Slice U8)
      (adDigest : CtxRomAuth.CtxDigest),
      token.agreement.root.bytes = capability.root.bytes ∧
      capability.binding = RegistrationResponseExecutor.completedBinding pending adDigest ∧
      established.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding (RegistrationResponseExecutor.completedBinding pending adDigest) capability.candidate.assigned_key_id ∧
      registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested aead) ∧
      aead.agreement = capability ∧
      aead.pending.finish (.Some plaintext) = .ok (established.kernel,
        .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ : record.OpenedRecord (Slice U8))) ∧
      established.application = plaintext.drop 8#usize ∧ application = TranscriptAuthParts.absSlice established.application

attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree

/-- Original protected native finish has an earlier same-run Server root equal to its actual successful Beacon root, with no local invariant or root-equality premise. -/
theorem path_root (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) (final : Native)
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Native) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) ∈ calls)
    (found : beforeFinish.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (good : ¬ RegistrationNativeMldsaOriginJournal.BadCalls initial.credential calls)
    (keyProtected : pending.binding.server_pin.public_key = initial.credential.publicKey)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache beforeFinish))
    (correct : RegistrationNativePairedCoordinates.RecipientCorrect setup) :
    ∃ serverCall ∈ calls, ∃ handle token current plaintext availability serverInitial hashed,
      serverCall.query = .inr (.build handle (some plaintext)) ∧
      RegistrationServerSdkSource.take handle serverCall.before.server = (some token, current) ∧
      BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext serverInitial ∧
      RegistrationServerRecordExecutor.Path serverInitial hashed ∧ Outcome token pending application := by
  have issued := RegistrationNativeMldsaOriginJournal.finish_issued initial.credential calls good index packet application
    beforeFinish afterFinish member owner pending oneTime found phase keyProtected
  obtain ⟨_completed, _verified, leading, trailing, serverCall, receipt, handle, serverInput, token, current,
      plaintext, availability, serverInitial, hashed, split, earlier, queryEq, taken, inputEq, _stage, admitted,
      recordPath, identity, ephemeral, kem, _ciphertext, _assigned, initHash, _rooted⟩ :=
    RegistrationNativeCausalResponseContents.path_contents setup checks wire route representation ensureInit identityIndex serverKid
      initial startup calls final actual index pending packet owner oneTime beforeFinish afterFinish application member found phase issued
  have actualSplit := actual
  rw [split] at actualSplit
  obtain ⟨beforePath, finished, _afterPath⟩ := path_cut _ leading trailing
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) actualSplit
  obtain ⟨matched⟩ := RegistrationNativeMatchedServerInput.from_taken setup checks wire route representation ensureInit identityIndex serverKid
    initial startup beforeFinish leading beforePath index owner pending oneTime found phase serverCall earlier handle token current taken
    plaintext availability serverInitial hashed admitted recordPath initHash collisionFree
  have localFacts := RegistrationNativePathAgreementFacts.initialized setup checks wire route representation ensureInit identityIndex serverKid
    initial startup beforeFinish leading beforePath
  have prekey := localFacts.2.1 owner (List.mem_of_getElem? found)
  have coherent := RegistrationNativeBeaconCoherence.pending beforeFinish.beacons localFacts.2.2 index owner found pending oneTime phase
  obtain ⟨_serverLeading, _serverTrailing, _serverSplit, serverPrefix, _serverCalled, _serverSuffix⟩ := beforePath.member serverCall earlier
  have serverIdentity := RegistrationNativePathAgreementFacts.server_identity setup checks wire route representation ensureInit identityIndex serverKid
    initial startup serverCall.before _ serverPrefix
  have currentPin := take_pin handle serverCall.before.server current token taken
  obtain ⟨_binding, candidateEq, _rest⟩ := RegistrationNativeServerContents.path_contents serverInitial hashed recordPath
  obtain ⟨candidateIdentity, _beaconIdentity, candidateEphemeral, candidateKem⟩ :=
    RegistrationNativeServerPublicContents.initial current.control current.pin availability token.agreement plaintext serverInitial admitted
  have packetIdentity : packet.public.identity_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys initial.created.seed).ed25519 := by
    calc
      packet.public.identity_key = hashed.candidate.server_identity_public_key := identity.symm
      _ = serverInitial.candidate.server_identity_public_key := congrArg (fun value => value.server_identity_public_key) candidateEq
      _ = current.pin.binding.identity_public_key := candidateIdentity
      _ = serverCall.before.server.pin.binding.identity_public_key := congrArg (fun value => value.binding.identity_public_key) currentPin
      _ = _ := serverIdentity
  have packetEphemeral : packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key :=
    ephemeral.symm.trans ((congrArg (fun value => value.ephemeral_public_key) candidateEq).trans candidateEphemeral)
  have packetKem : packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext :=
    kem.symm.trans ((congrArg (fun value => value.kem_ciphertext) candidateEq).trans candidateKem)
  simp only [RegistrationNativeStageTrace.Executed, RegistrationNativeExperiment.handler] at finished
  change (.ok (some application), afterFinish) ∈ support
    ((RegistrationNativeExperiment.beacon setup checks representation initial.created
      (RegistrationNativeBeaconFrontend.finish setup source wire index (some packet))).run beforeFinish) at finished
  rw [source_lower, support_map] at finished
  obtain ⟨inner, supported, same⟩ := finished
  have outcomeEq : inner.1 = .ok (some application) := congrArg Prod.fst same
  have supportedFinish : (.ok (some application), inner.2) ∈ support
      ((lower setup checks representation initial.created
        (RegistrationNativeBeaconFrontend.finish setup source wire index (some packet))).run
          (beforeFinish.beacons, (RegistrationWorldAgreementCompiler.erase beforeFinish.server.world, beforeFinish))) := by
    rw [← outcomeEq]
    exact supported
  have result : Outcome token pending application := RegistrationNativeFinishRootReceipt.finish setup checks wire route representation initial.created
    owner pending oneTime index packet application _ inner.2 found phase supportedFinish localFacts.1 coherent token beforeFinish.server.pin
    (RegistrationNativeWorldCache.cache beforeFinish) matched prekey packetIdentity packetEphemeral packetKem correct
  refine ⟨serverCall, ?_, handle, token, current, plaintext, availability,
    serverInitial, hashed, ?_, taken, admitted, recordPath, result⟩
  · simpa only [← split] using (List.mem_append.mpr (Or.inl earlier) : serverCall ∈ leading ++ (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) :: trailing)
  · simpa only [inputEq] using queryEq

end BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement.path_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement.path_root
