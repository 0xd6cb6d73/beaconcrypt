-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual

/-! Canonical original-ledger designation determines the selected actual SDK getter's genuine generated key. The owner may be created later; its retained private handle is justified by the actual constructor invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetGetter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (Initial State)
open RegistrationNativeEvents (Observed)
open RegistrationNativeParsedTargetActual (Call)
open RegistrationNativeKemCut (Cut scan)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeKemParsedRouting.source
  RegistrationNativeKemParsedRouting.handler RegistrationNativeExperiment.handler

/-- Any suspension of the actual chosen parsed attempt has the key from its original publicly verified packet. -/
theorem selected_key (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (parsed : Nat) (before : State n KemSK mlSource)
    (counter : before.parsedAccepts = parsed)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (verified : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys)
    (key : PqxdhKemIndCca.MlKem768PublicKey)
    (next : (PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret) →
      OracleComp (RegistrationNativeKemParsedRouting.Spec n mlSource KemSK) (RustM (Option Nat)))
    (reached : RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (supported : (Cut.pending key next, reached) ∈ support
      ((scan (RegistrationNativeKemParsedRouting.source setup checks wire route representation created credential)
        (RegistrationNativeKemParsedRouting.handler setup checks wire parsed (.inr (.accept packet))) 0).run
          (RegistrationNativeKemAcceptCompiler.nativeProject before))) : key = keys.2.pqKey := by
  rw [RegistrationNativeParsedTargetCut.selected_scan setup checks wire route representation created credential
    packet parsed before counter] at supported
  have program : simulateQ (RegistrationNativeKemSdkGetterKey.lower (n := n) (mlSource := mlSource) (KemSK := KemSK))
      (RegistrationNativeKemServerInterface.typedAccept setup checks packet) =
      simulateQ (RegistrationNativeKemRouting.route true) (simulateQ RegistrationNativeKemFrontendInterface.lift
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) := by
    simp only [RegistrationNativeKemSdkGetterKey.lower, QueryImpl.simulateQ_compose]
  rw [← program] at supported
  exact RegistrationNativeKemSdkGetterKey.typed_pending_key setup checks wire route representation created credential
    packet keys verified key next _ reached supported

/-- Original broad native success supplies a selected getter at the genuine KEM pair's public key, with exactly the original accept-by-owner target coordinates. -/
theorem initialized_getter (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state))
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire initial.created.server.server.metadata.sender budget target claim observed) :
    ∃ session,
      ∃ call : Call (n := n) setup checks wire route representation initial.created initial.credential observed.2.1.transcript target.1.val session,
      ∃ owner pair next reached, observed.2.2.beacons[target.2.val]? = some owner ∧
      owner.kemHandle = target.2.val ∧ observed.2.2.pool.keys[target.2.val]? = some pair ∧
      pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) ∧
      (Cut.pending pair.1 next, reached) ∈ support
        ((scan (RegistrationNativeKemParsedRouting.source setup checks wire route representation initial.created initial.credential)
          (RegistrationNativeKemParsedRouting.handler setup checks wire target.1.val (.inr (.accept call.packet))) 0).run
            (RegistrationNativeKemAcceptCompiler.nativeProject call.first)) := by
  obtain ⟨index, guess, entry, session, call, owner, keys, pair, _claimed, _fresh, _designated,
    _guessed, found, handle, privateAt, generated, verified, matched⟩ :=
      RegistrationNativeParsedTargetCanonicalActual.initialized_born_call setup checks wire route representation source
        ensureInit identityIndex serverKeyId initial started readback bounds mode work budget target claim observed supported winning
  obtain ⟨key, next, reached, pending⟩ := call.pending
  have equal := (selected_key setup checks wire route representation initial.created initial.credential
    call.packet target.1.val call.first call.counter keys verified key next reached pending).trans matched
  subst key
  exact ⟨session.val, call, owner, pair, next, reached, found, handle, privateAt, generated, pending⟩

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetGetter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetGetter.selected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetGetter.selected_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetGetter.initialized_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetGetter.initialized_getter
