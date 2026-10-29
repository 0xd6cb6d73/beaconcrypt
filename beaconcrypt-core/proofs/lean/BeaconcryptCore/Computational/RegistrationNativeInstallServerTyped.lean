-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallServerComplete

/-! The original typed Server build's actual current-environment compiler refines the raw material controller on the same G2 trace. Its successful installation suffix is the reference stored at that literal pre-call session. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem build_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (frontend : RegistrationNativePublicFrontend.State source) :
    (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.build handle application))).run frontend =
      (fun result => (result.1.1, { frontend with server := result.1.2, environment := result.2 })) <$>
        RegistrationNativeInstallCompile.compile (KemSK := KemSK) setup.source wire.frameWrite sign
          ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run frontend.server) frontend.environment := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen,
    RegistrationServerOpenReferenceCompiler.build, RegistrationNativeInstallCompile.compile,
    StateT.run]
  rfl

/-- A literal live session in the original typed build contributes its own descriptor once exactly on public success. -/
theorem build_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (frontend : RegistrationNativePublicFrontend.State source) (ready : RegistrationServerReferenceRoot.Ready)
    (stored : frontend.server.sessions[handle]? = some (some ready))
    (before : RegistrationNativeG2Trace.State)
    (result : (RegistrationServerMaterialFrontend.Result × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeG2Trace.handler
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run frontend)).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ present result.1.1 = true then [ready.reference] else [] := by
  rw [build_source] at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨compiled, actual, returned⟩ := supported
  have original := RegistrationNativeInstallCompile.program_support setup.source wire.frameWrite sign
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run frontend.server)
      frontend.environment before compiled actual
  have bill := RegistrationNativeInstallServerComplete.build_live (KemSK := KemSK) role wire checks.reservePeer handle application
    frontend.server ready stored before (compiled.1.1, compiled.2) original
  cases returned
  exact bill


/-- A missing or already consumed original session contributes no successful installation descriptor. -/
theorem build_missing (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (frontend : RegistrationNativePublicFrontend.State source)
    (missing : ∀ ready, frontend.server.sessions[handle]? ≠ some (some ready))
    (before : RegistrationNativeG2Trace.State)
    (result : (RegistrationServerMaterialFrontend.Result × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeG2Trace.handler
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run frontend)).run before)) :
    messages role result.2.events = messages role before.events := by
  rw [build_source] at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨compiled, actual, returned⟩ := supported
  have original := RegistrationNativeInstallCompile.program_support setup.source wire.frameWrite sign
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run frontend.server)
      frontend.environment before compiled actual
  cases stored : frontend.server.sessions[handle]? with
  | none =>
      simp only [RegistrationServerMaterialFrontend.build, RegistrationServerMaterialFrontend.take, stored, StateT.run,
        simulateQ_pure, ] at original
      have trace : compiled.2 = before := congrArg Prod.snd original
      cases returned
      exact congrArg (fun value => messages role value.events) trace
  | some entry => cases entry with
    | none =>
        simp only [RegistrationServerMaterialFrontend.build, RegistrationServerMaterialFrontend.take, stored, StateT.run,
          simulateQ_pure, ] at original
        have trace : compiled.2 = before := congrArg Prod.snd original
        cases returned
        exact congrArg (fun value => messages role value.events) trace
    | some ready => exact False.elim (missing ready stored)



private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

/-- Missing or consumed sessions execute a literal pure public failure before any material callback. -/
theorem build_missing_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (frontend : RegistrationNativePublicFrontend.State source)
    (missing : ∀ ready, frontend.server.sessions[handle]? ≠ some (some ready)) :
    (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.build handle application))).run frontend = pure (.ok none, frontend) := by
  cases stored : frontend.server.sessions[handle]? with
  | none =>
      simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen,
        RegistrationServerOpenReferenceCompiler.build, RegistrationServerMaterialFrontend.build,
        RegistrationServerMaterialFrontend.take, stored, StateT.run, pure_apply, simulateQ_pure, map_pure]
  | some entry => cases entry with
    | none =>
        simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen,
          RegistrationServerOpenReferenceCompiler.build, RegistrationServerMaterialFrontend.build,
          RegistrationServerMaterialFrontend.take, stored, StateT.run, pure_apply, simulateQ_pure, map_pure]
    | some ready => exact False.elim (missing ready stored)

end BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped.build_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped.build_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped.build_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped.build_missing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped.build_missing_source
