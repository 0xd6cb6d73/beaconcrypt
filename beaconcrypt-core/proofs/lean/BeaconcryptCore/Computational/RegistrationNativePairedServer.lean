-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedCompile
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer

/-! The actual native Server material controller inherits its paired certificate from the arbitrary-Choice Word controller by literal address evaluation. Inlining publication then preserves the exact monitor through the actual current environment. No descriptor, trace-source, lifecycle or successful-publication certificate is supplied externally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedServer
open RegistrationNativePairedTrace (Safe)
open RegistrationNativePairedMaterialSource (nativeLift)
variable {n : Nat} {KemSK : Type}

private def ready (input : RegistrationServerReferenceRoot.Ready) : RegistrationNativeSecretWordMessage.ServerReady :=
  ⟨input.agreement, RegistrationNativeSecretWordMessage.literal input.reference⟩

private def state (before : RegistrationServerMaterialFrontend.State) : RegistrationNativeSecretWordMessage.ServerState :=
  ⟨before.control, before.pin, before.consumed, before.sessions.map (Option.map ready)⟩

private theorem state_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (before : RegistrationServerMaterialFrontend.State) :
    (state before).eval candidate = before := by
  have selected (input : RegistrationServerReferenceRoot.Ready) :
      (ready input).eval candidate = input := by cases input; rfl
  have entry (input : Option RegistrationServerReferenceRoot.Ready) :
      ((Option.map ready input).map (RegistrationNativeSecretWordMessage.ServerReady.eval candidate)) = input := by
    cases input <;> simp only [Option.map_none, Option.map_some, selected]
  rcases before with ⟨control, pin, consumed, sessions⟩
  simp [state, RegistrationNativeSecretWordMessage.ServerState.eval, List.map_map, Function.comp_def, entry]

/-- The exact raw native one-use build preserves the actual demanded descriptor and hidden Choice before each installation. -/
theorem raw_build (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) :
    Safe (simulateQ (nativeLift (n := n) (KemSK := KemSK))
      ((RegistrationServerMaterialFrontend.build wire reservePeer handle application).run before)) := by
  let candidate := RegistrationNativeSecretWordMessage.zero
  have valid := RegistrationNativePairedMaterialSource.safe (n := n) (KemSK := KemSK) candidate
    ((RegistrationNativeSecretWordServerMaterial.build wire reservePeer handle application).run (state before))
    (RegistrationNativeSecretWordPairedRawServer.build wire reservePeer handle application (state before))
  have exactProgram := congrArg (simulateQ (nativeLift (n := n) (KemSK := KemSK)))
    (RegistrationNativeSecretWordServerMaterial.build_source candidate wire reservePeer handle application (state before))
  simp only [simulateQ_map, state_eval] at exactProgram
  rw [← exactProgram, ← bind_pure_comp]
  exact RegistrationNativePairedTrace.bind_safe _ _ valid (fun _ => RegistrationNativePairedTrace.pure_safe _)

/-- The full native build retains its paired certificate through the actual shared current-environment publication compiler. -/
theorem build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reservePeer : Bool) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    Safe (RegistrationNativePairedCompile.compile (n := n) (KemSK := KemSK) source wire.frameWrite sign
      ((RegistrationServerMaterialFrontend.build wire reservePeer handle application).run before) env) :=
  RegistrationNativePairedCompile.safe source wire.frameWrite sign _ env (raw_build wire reservePeer handle application before)

/-- Every actual whole-frontend Server build retains the same internally derived paired certificate. -/
theorem frontend_build {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationNativePublicFrontend.State source) :
    Safe ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.build handle application))).run before) := by
  have exactProgram : (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run before =
      (fun reached => (reached.1.1, { before with server := reached.1.2, environment := reached.2 })) <$>
        RegistrationNativePairedCompile.compile setup.source wire.frameWrite sign
          ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.server) before.environment := by
    simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen,
      RegistrationServerOpenReferenceCompiler.build, StateT.run, RegistrationNativePairedCompile.compile]
    rfl
  rw [exactProgram, ← bind_pure_comp]
  exact RegistrationNativePairedTrace.bind_safe _ _
    (build setup.source wire sign checks.reservePeer handle application before.server before.environment)
    (fun _ => RegistrationNativePairedTrace.pure_safe _)

end BeaconcryptCore.Computational.RegistrationNativePairedServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServer.raw_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServer.raw_build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServer.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServer.frontend_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServer.frontend_build
