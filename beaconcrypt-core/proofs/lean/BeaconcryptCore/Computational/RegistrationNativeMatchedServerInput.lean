-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePendingTuple
import BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace
import BeaconcryptCore.Computational.RegistrationNativeServerContents

/-! Same-run pending-bundle and consumed-token receipts identify the Server's actual checked root tuple with the current Beacon owner's actual public inputs. Only the common-cache collision exception and actual source-stage Init-hash equality are used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree

structure Receipt (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (token : peer.ConsumedRegistration)
    (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache) where
  before : RegistrationServerFrontendCompiler.State n
  packet : registration.InitPacket
  events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event
  authenticated : registration.AuthenticatedInit
  afterAuthentication : RegistrationServerFrontendCompiler.State n
  afterAgreement : RegistrationServerFrontendCompiler.State n
  checked : (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
    ((RegistrationServerNativeSource.authenticate setup (RegistrationNativeWire.ledgerCodec wire) route source.verify created packet).run before)
  agreed : (.ok (.ServerComplete token.agreement), afterAgreement) ∈ support
    ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run afterAuthentication)
  root : RegistrationNativeTokenRootReceipt.Input setup checks representation created packet authenticated afterAuthentication afterAgreement token.agreement
  registration : authenticated.registration = {
    beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    beacon_prekey_public_key := owner.prekeyPublic,
    beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
    beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }
  pinEq : before.pin = pin
  cacheExtension : afterAuthentication.world.world.1.primitive.2 ≤ cache


/-- The actual earlier build's consumed token has checked Server root inputs matching this reached Beacon's pending public tuple, without an input- or root-agreement premise. -/
theorem from_taken (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (final : RegistrationNativeExperiment.State n KemSK source)
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source)))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (found : final.beacons[index]? = some owner)
    (phase : owner.phase = .initSent pending oneTime)
    (buildCall : Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source))
    (member : buildCall ∈ calls) (handle : Nat) (token : peer.ConsumedRegistration)
    (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take handle buildCall.before.server = (some token, current))
    (plaintext : Slice U8) (availability : pqxdh.KeyIdAvailability) (serverInitial : registration.ServerInitialKdf)
    (hashed : registration.ServerResponseHash)
    (admitted : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext serverInitial)
    (recordPath : RegistrationServerRecordExecutor.Path serverInitial hashed)
    (initHash : hashed.binding.init_hash = pending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final)) :
    Nonempty (Receipt (n := n) setup checks wire route representation initial.created owner oneTime token final.server.pin (RegistrationNativeWorldCache.cache final)) := by
  obtain ⟨pendingInput⟩ := RegistrationNativePendingTuple.initialized_path setup checks wire route representation ensureInit identityIndex
    serverKid initial startup final calls actual index owner pending oneTime found phase
  obtain ⟨buildLeading, buildTrailing, _buildSplit, beforeBuild, built, afterBuild⟩ := actual.member buildCall member
  have empty := RegistrationNativeTokenTrace.start_empty setup ensureInit identityIndex serverKid initial startup
  obtain ⟨acceptCall, acceptLeading, between, _acceptSplit, beforeAccept, accepted, betweenPath, origin⟩ :=
    RegistrationNativeTokenCacheTrace.taken_origin setup checks wire route representation initial.created initial.credential beforeBuild empty handle token current taken
  obtain ⟨packet, events, authenticated, afterAuthentication, _queryEq, checked, birth, summaryEq⟩ := origin
  obtain ⟨afterAgreement, _history, agreed, _consumed, root⟩ := RegistrationNativeTokenRootReceipt.born
    setup checks representation initial.created packet authenticated afterAuthentication token birth
  obtain ⟨root⟩ := root
  have afterAccept : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      acceptCall.after (between ++ buildCall :: buildTrailing) final := betweenPath.append (.cons buildCall built _ _ afterBuild)
  have extension := RegistrationNativeInitTupleAgreement.path_cache setup checks wire route representation initial.created initial.credential afterAccept
  have cacheEq : afterAuthentication.world.world.1.primitive.2 = RegistrationNativeWorldCache.cache acceptCall.after := by
    simpa only [RegistrationNativeInitFinal.summary, RegistrationNativeWorldCache.cache] using
      congrArg (fun value : RegistrationSigningShared.State => value.2) summaryEq
  have authExtension : afterAuthentication.world.world.1.primitive.2 ≤ RegistrationNativeWorldCache.cache final := by
    rw [cacheEq]
    exact extension
  have tokenBinding : token.agreement.binding = authenticated.binding := congrArg (fun value : agreement.ServerAgreement => value.binding) root.completedEq
  have initialHash := BeaconcryptCore.Refinement.RegistrationAd.server_admission_init_hash
    current.control current.pin availability token.agreement plaintext serverInitial admitted
  have retained := (RegistrationNativeServerContents.path_contents serverInitial hashed recordPath).1
  have retainedHash : hashed.binding.init_hash = token.agreement.binding.init_hash :=
    (congrArg (fun value : session.CompletedRegistrationBinding => value.init_hash) retained).trans initialHash
  have authHash : authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray pendingInput.digest :=
    (congrArg (fun value : session.RegistrationBinding => value.init_hash) tokenBinding.symm).trans
      (retainedHash.symm.trans (initHash.trans pendingInput.initHash))
  have startedSame : pendingInput.hashing.state.started = pendingInput.started := by
    simpa only [RegistrationNativeInitTupleSource.Fixed, RegistrationNativeInitTupleSource.metadata] using congrArg Prod.fst pendingInput.fixed
  have matched := RegistrationNativeInitTupleAgreement.registration setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
    initial.created packet acceptCall.before.server afterAuthentication events authenticated checked (RegistrationNativeWorldCache.cache final)
      authExtension pendingInput.hashing.state pendingInput.started _ startedSame pendingInput.attached pendingInput.validated
        pendingInput.digest pendingInput.cached authHash collisionFree
  have fromAccept : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      acceptCall.before (acceptCall :: between ++ buildCall :: buildTrailing) final := .cons acceptCall accepted _ _ afterAccept
  have pinEq := (RegistrationNativeInitTupleAgreement.path_pin setup checks wire route representation initial.created initial.credential fromAccept).symm
  exact ⟨⟨acceptCall.before.server, packet, events, authenticated, afterAuthentication, afterAgreement, checked, agreed, root, matched, pinEq, authExtension⟩⟩

end BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput.from_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput.from_taken
