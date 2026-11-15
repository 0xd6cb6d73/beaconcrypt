-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializerFields
import BeaconcryptCore.Computational.RawCtxSourceHkdf

/-! The actual source initializer pending values compute complementary native role kernels from a common derived root and the concrete fixed-source initial KDF. This is a local functional composition; the initialized path wrapper supplies root equality separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitializerAgreement
open PqxdhInitialRatchetComplementarity (serverPending beaconPending)
open BeaconcryptCore.Refinement.PqxdhConcreteSession

/-- The exact actual initializer capabilities, resumed with their concrete source replies, have complementary role chains and matching material streams. -/
theorem kernels {AD PT CT : Type}
    (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (serverCapability : agreement.ServerAgreement) (beaconCapability : agreement.BeaconAgreement) (application : Slice U8)
    (serverInitial : registration.ServerInitialKdf) (beaconInitial : registration.BeaconInitialKdf)
    (serverStarted : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability serverCapability application serverInitial)
    (beaconStarted : registration.begin_beacon_completion beaconCapability = .ok beaconInitial)
    (sameRoot : serverCapability.root.bytes = beaconCapability.root.bytes) :
    ∃ beaconOrigin serverOrigin beaconKernel serverKernel,
      pqxdh.concrete.resume_initial_ratchet_kdf beaconInitial.pending
        (RawCtxSourceHkdf.initialResponse source.crypto ⟨beaconCapability.root.bytes, ratchet.INITIAL_RATCHET_INFO⟩) = .ok beaconKernel ∧
      pqxdh.concrete.resume_initial_ratchet_kdf serverInitial.pending
        (RawCtxSourceHkdf.initialResponse source.crypto ⟨serverCapability.root.bytes, ratchet.INITIAL_RATCHET_INFO⟩) = .ok serverKernel ∧
      ConcreteSession crypto beaconOrigin serverOrigin beaconKernel serverKernel ∧
      beaconKernel.refined.send_chain = serverKernel.refined.receive_chain ∧
      beaconKernel.refined.receive_chain = serverKernel.refined.send_chain ∧
      ∀ position, Ratchet.msgKeyAt crypto beaconKernel.refined.send_chain position = Ratchet.msgKeyAt crypto serverKernel.refined.receive_chain position ∧
        Ratchet.msgKeyAt crypto serverKernel.refined.send_chain position = Ratchet.msgKeyAt crypto beaconKernel.refined.receive_chain position := by
  have serverFields := RegistrationNativeInitializerFields.server control pin availability serverCapability application serverInitial serverStarted
  have beaconFields := RegistrationNativeInitializerFields.beacon beaconCapability beaconInitial beaconStarted
  obtain ⟨beaconOrigin, serverOrigin, beaconKernel, serverKernel, beaconRun, serverRun, session, send, receive, messages⟩ :=
    initialize_establishes_concrete_session crypto serverCapability.root.bytes (RawCtxSourceHkdf.initialResponse source.crypto)
  refine ⟨beaconOrigin, serverOrigin, beaconKernel, serverKernel, ?_, ?_, session, send, receive, messages⟩
  · rw [beaconFields.2.1, ← sameRoot]
    simpa only [initializeBeacon_eq] using beaconRun
  · rw [serverFields.1]
    simpa only [initializeServer_eq] using serverRun

end BeaconcryptCore.Computational.RegistrationNativeInitializerAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializerAgreement.kernels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializerAgreement.kernels
