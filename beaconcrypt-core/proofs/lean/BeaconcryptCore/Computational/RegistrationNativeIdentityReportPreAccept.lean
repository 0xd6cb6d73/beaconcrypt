-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh

/-! An actual native candidate with a changed prekey sets the chronological report event before SDK acceptance continues. The prefix corollary derives generated ownership, signing-history synchronization and the fixed-prekey policy from the initialized actual native run. Capacity and freshness remain explicit local facts, discharged separately before finite multi-user routing. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
open PqxdhEd25519EufCma (Phase1KeyTuple)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationWorldAuthentication.begin

theorem detects (joint : PqxdhJointIdentity.Primitives) (count : Nat) (packet : beaconcrypt_core.registration.InitPacket)
    (before : State n KemSK source) (monitor : MonitorState count)
    (consistent : RegistrationNativeIdentityReportMonitor.Consistent joint monitor)
    (holds : RegistrationNativeIdentityHistoryInvariant.Holds joint (privatePool monitor) before.beacons)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ before.beacons)
    (valid : owner.identity.handle < count)
    (fixed : RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory)
    (fresh : (⟨owner.identity.handle, valid⟩ : Fin count) ∉ monitor.1.snapshot.history.reveals)
    (decoded : Phase1KeyTuple)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify (RegistrationRootInput.candidate packet) =
      some (owner.identity.publicIdentity.ed25519, decoded))
    (different : decoded.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic)
    (result : (Unit × State n KemSK source) × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      ((RegistrationNativeIdentityMain.report packet).run before)).run monitor)) : result.2.1.occurred = true := by
  have snapshot : monitor.1.snapshot = RegistrationNativeIdentityHistoryReport.snapshot joint count (privatePool monitor) :=
    consistent.1.1.trans (RegistrationNativeIdentityReportSnapshot.reporting_snapshot joint monitor.2 consistent.2)
  have earlier : (⟨owner.identity.handle, valid⟩ : Fin count) ∉
      (RegistrationNativeIdentityHistoryReport.snapshot joint count (privatePool monitor)).history.reveals := by
    rw [← snapshot]
    exact fresh
  have recognized := (RegistrationNativeIdentityHistoryReport.prekey_or_event joint count (privatePool monitor)
    before.beacons holds.1 holds.2.2 owner member valid fixed earlier (RegistrationRootInput.candidate packet) decoded accepted).resolve_left different
  have actual : PqxdhJointPhase1Reports.candidateAccepted joint
      ⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩ monitor.1.snapshot = true := by
    rw [snapshot]
    exact recognized
  have matching : PqxdhEd25519EufCma.encodedIdentity owner.identity.publicIdentity.ed25519 =
      PqxdhRefinement.absBytes packet.identity_key :=
    (PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness joint.verify (RegistrationRootInput.candidate packet)
      owner.identity.publicIdentity.ed25519 decoded accepted).1.symm
  exact RegistrationNativeIdentityReportEmit.report_detects joint count packet before monitor result owner member matching actual supported

/-- Every changed-prekey accepted candidate at a reached actual native prefix is reported under its original generated identity index. -/
theorem prefix_detects (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (context : Context n KemSK) (count : Nat)
    (prefixResult : RegistrationNativeEvents.Observed Value (State n KemSK source) × MonitorState count)
    (prefixSupported : prefixResult ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩)))
    (packet : beaconcrypt_core.registration.InitPacket)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ prefixResult.1.2.2.beacons)
    (valid : owner.identity.handle < count)
    (decoded : Phase1KeyTuple)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) =
      some (owner.identity.publicIdentity.ed25519, decoded))
    (different : decoded.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic)
    (result : (Unit × State n KemSK source) × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
      ((RegistrationNativeIdentityMain.report packet).run prefixResult.1.2.2)).run prefixResult.2)) :
    result.2.1.occurred = true := by
  have invariant := RegistrationNativeIdentityReportHistoryRun.run_inv setup checks wire route representation created credential
    bounds mode work context count prefixResult prefixSupported
  have fixed := RegistrationNativeIdentityReportHistoryRun.run_fixed setup checks wire route representation created credential
    bounds mode work context count prefixResult prefixSupported owner member
  have consistent := RegistrationNativeIdentityReportMonitor.program_consistent setup.joint count _ _ prefixResult
    (RegistrationNativeIdentityReportMonitor.initial_consistent setup.joint count) prefixSupported
  have fresh := RegistrationNativeIdentityReportFresh.run_fresh setup.joint count _
    (RegistrationNativeIdentityMainNoReveal.run_safe setup checks wire route representation created credential bounds mode work ⟨context, []⟩)
    prefixResult prefixSupported ⟨owner.identity.handle, valid⟩
  exact detects setup.joint count packet prefixResult.1.2.2 prefixResult.2 consistent invariant.1 owner member valid fixed fresh decoded
    accepted different result supported

/-- The actual mandatory global-World verifier supplies the accepted tuple; a changed source-owner prekey is then detected by the actual pre-accept report operation. -/
theorem prefix_native_detects (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (context : Context n KemSK) (count : Nat)
    (prefixResult : RegistrationNativeEvents.Observed Value (State n KemSK source) × MonitorState count)
    (prefixSupported : prefixResult ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩)))
    (packet : beaconcrypt_core.registration.InitPacket)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ prefixResult.1.2.2.beacons)
    (valid : owner.identity.handle < count)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : beaconcrypt_core.registration.AuthenticatedInit) (after : PqxdhRecordLiftWorld.State n)
    (authentication : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationWorldAuthentication.begin setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
        prefixResult.1.2.2.context.server.pin packet).run prefixResult.1.2.2.context.server.world.world.1))
    (designated : RegistrationRootInput.identity authenticated.registration = owner.identity.publicIdentity.ed25519)
    (different : (RegistrationRootInput.keys authenticated.registration).prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic)
    (result : (Unit × State n KemSK source) × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
      ((RegistrationNativeIdentityMain.report packet).run prefixResult.1.2.2)).run prefixResult.2)) :
    result.2.1.occurred = true := by
  have accepted := RegistrationNativeEdOrigin.accepted_detached setup (RegistrationNativeWire.ledgerCodec wire) shortRejects route source.verify
    prefixResult.1.2.2.context.server.pin packet prefixResult.1.2.2.context.server.world.world.1 after events authenticated authentication
  rw [designated] at accepted
  exact prefix_detects setup checks wire route representation created credential bounds mode work context count prefixResult prefixSupported
    packet owner member valid (RegistrationRootInput.keys authenticated.registration) accepted different result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept.detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept.detects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept.prefix_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept.prefix_detects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept.prefix_native_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportPreAccept.prefix_native_detects
