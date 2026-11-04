-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers

/-! One final shared-cache collision exception and the one original global protected-ML issuance exception give source initializer receipts for every owner and every reached successful protected finish in the same execution. The proof transports final collision-freedom to each actual acceptance prefix; it does not resample histories or take a union of incompatible games. Computed initializers remain distinguished from later consumed record kernels. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeAllOwnerInitializers
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeInitializedInitializers (Outcome)
variable {n : Nat} {ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- All owner/cut indices range over one actual initialized path and share the same final collision and global issuance exceptions. -/
theorem simultaneous (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
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
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final))
    (correct : RegistrationNativePairedCoordinates.RecipientCorrect setup) :
    ∃ serverCall ∈ calls, ∃ handle token current plaintext availability serverInitial hashed,
      serverCall.query = .inr (.build handle (some plaintext)) ∧
      RegistrationServerSdkSource.take handle serverCall.before.server = (some token, current) ∧
      registration.begin_server_completion current.control current.pin availability token.agreement plaintext = .ok (.Ok serverInitial) ∧
      RegistrationServerRecordExecutor.Path serverInitial hashed ∧ Outcome crypto setup.source token serverInitial pending application := by
  obtain ⟨_leading, trailing, _split, _beforePath, executed, afterPath⟩ := actual.member
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) member
  have through : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      beforeFinish ((⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) :: trailing) final :=
    .cons _ executed _ _ afterPath
  have extension := RegistrationNativeInitTupleAgreement.path_cache setup checks wire route representation initial.created initial.credential through
  have beforeFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache beforeFinish) := by
    rintro ⟨left, right, first, second, different, leftPresent, rightPresent, equal⟩
    exact collisionFree ⟨left, right, first, second, different, extension leftPresent, extension rightPresent, equal⟩
  exact RegistrationNativeInitializedInitializers.path_initializers crypto setup checks wire route representation ensureInit identityIndex serverKid
    initial startup calls final actual index pending packet owner oneTime beforeFinish afterFinish application member found phase good keyProtected beforeFree correct

end BeaconcryptCore.Computational.RegistrationNativeAllOwnerInitializers

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllOwnerInitializers.simultaneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllOwnerInitializers.simultaneous
