-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete

/-! The original typed Server build's actual current-environment compiler refines the raw material controller on the same G2 trace. Its successful installation suffix is the reference stored at that literal pre-call session. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem build_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (frontend : RegistrationNativeSecretWordMessage.State source) :
    (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.build handle application))).run frontend =
      (fun result => (result.1.1, { frontend with server := result.1.2, environment := result.2 })) <$>
        RegistrationNativeSecretWordInstallCompile.compile (KemSK := KemSK) setup.source wire.frameWrite sign
          ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run frontend.server) frontend.environment := by
  simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.serverOpen,
    RegistrationNativeSecretWordServerCompiler.build, RegistrationNativeSecretWordInstallCompile.compile,
    StateT.run]
  rfl

/-- A literal live session in the original typed build contributes its own descriptor once exactly on public success. -/
theorem build_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (frontend : RegistrationNativeSecretWordMessage.State source) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : frontend.server.sessions[handle]? = some (some ready))
    (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run frontend)).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ present result.1.1 = true then [ready.reference] else [] := by
  rw [build_source] at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨compiled, actual, returned⟩ := supported
  have original := RegistrationNativeSecretWordInstallCompile.program_support setup.source wire.frameWrite sign
    ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run frontend.server)
      frontend.environment before compiled actual
  have bill := RegistrationNativeSecretWordInstallServerComplete.build_live (KemSK := KemSK) role wire checks.reservePeer handle application
    frontend.server ready stored before (compiled.1.1, compiled.2) original
  cases returned
  exact bill


/-- A missing or already consumed original session contributes no successful installation descriptor. -/
theorem build_missing (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (frontend : RegistrationNativeSecretWordMessage.State source)
    (missing : ∀ ready, frontend.server.sessions[handle]? ≠ some (some ready))
    (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run frontend)).run before)) :
    messages role result.2.events = messages role before.events := by
  rw [build_source] at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨compiled, actual, returned⟩ := supported
  have original := RegistrationNativeSecretWordInstallCompile.program_support setup.source wire.frameWrite sign
    ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run frontend.server)
      frontend.environment before compiled actual
  cases stored : frontend.server.sessions[handle]? with
  | none =>
      simp only [RegistrationNativeSecretWordServerMaterial.build, RegistrationNativeSecretWordServerMaterial.take, stored, StateT.run,
        simulateQ_pure, ] at original
      have trace : compiled.2 = before := congrArg Prod.snd original
      cases returned
      exact congrArg (fun value => messages role value.events) trace
  | some entry => cases entry with
    | none =>
        simp only [RegistrationNativeSecretWordServerMaterial.build, RegistrationNativeSecretWordServerMaterial.take, stored, StateT.run,
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
    (handle : Nat) (application : Option (Slice U8)) (frontend : RegistrationNativeSecretWordMessage.State source)
    (missing : ∀ ready, frontend.server.sessions[handle]? ≠ some (some ready)) :
    (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.build handle application))).run frontend = pure (.ok none, frontend) := by
  cases stored : frontend.server.sessions[handle]? with
  | none =>
      simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.serverOpen,
        RegistrationNativeSecretWordServerCompiler.build, RegistrationNativeSecretWordServerMaterial.build,
        RegistrationNativeSecretWordServerMaterial.take, stored, StateT.run, pure_apply, simulateQ_pure, map_pure]
  | some entry => cases entry with
    | none =>
        simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.serverOpen,
          RegistrationNativeSecretWordServerCompiler.build, RegistrationNativeSecretWordServerMaterial.build,
          RegistrationNativeSecretWordServerMaterial.take, stored, StateT.run, pure_apply, simulateQ_pure, map_pure]
    | some ready => exact False.elim (missing ready stored)

/-- Every original typed Word build has exactly the count of its own successful public reply. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (frontend : RegistrationNativeSecretWordMessage.State source) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run frontend)).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧
      added.length = (if role = .server ∧ present result.1.1 = true then 1 else 0) := by
  classical
  by_cases live : ∃ ready, frontend.server.sessions[handle]? = some (some ready)
  · obtain ⟨ready, stored⟩ := live
    have bill := build_live setup checks wire sign selectedOwner selectedAccept publicPrekey role handle application frontend ready stored before result supported
    refine ⟨if role = .server ∧ present result.1.1 = true then [ready.reference] else [], bill, ?_⟩
    split <;> rfl
  · have missing : ∀ ready, frontend.server.sessions[handle]? ≠ some (some ready) := by simpa only [not_exists] using live
    rw [build_missing_source setup checks wire sign selectedOwner selectedAccept publicPrekey handle application frontend missing] at supported
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], by simp only [List.append_nil], by simp [present]⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build_missing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build_missing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped.build
