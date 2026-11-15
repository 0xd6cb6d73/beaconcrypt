-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPinTrace
import BeaconcryptCore.PanicFreedom.RegistrationTrivial

/-! Actual native startup derives its configured Server pin from the created Server identity and actual generated ML credential. Pin selection performs no primitive callback and preserves the complete native state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPinStartup
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

/-- Actual pure pin selection preserves the configured binding and ML public key. -/
theorem initialize_pin (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before after : RegistrationWorldServerReplay.Global n Auxiliary) (pin : session.ServerAuthenticationPin)
    (supported : (.ok (.Some pin), after) ∈ support
      ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before)) :
    pin.binding = binding ∧ pin.public_key = publicKey := by
  simp only [RegistrationWorldServerFrontend.initializePin_native, mem_support_pure_iff] at supported
  cases supported
  exact ⟨rfl, rfl⟩

/-- Successful actual Server initialization uses the created source identity and actual supplied ML key. -/
theorem frontend_pin (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (publicKey : Std.Array U8 1952#usize)
    (auxiliary : Auxiliary) (before after : PqxdhRecordLiftWorld.State n)
    (native : RegistrationWorldServerFrontend.State n Auxiliary)
    (supported : (.ok (.Some native), after) ∈ support ((RegistrationWorldServerFrontend.start created publicKey auxiliary).run before)) :
    native.pin.binding = ⟨created.server.server.identity, created.server.server.metadata.sender⟩ ∧ native.pin.public_key = publicKey := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨installed, _installed, pinned, pinnedAt, returned⟩ := supported
  cases answered : pinned.1 with
  | fail error | div => simp only [answered] at returned; cases returned
  | ok value => cases value with
    | none => simp only [answered] at returned; cases returned
    | some pin =>
        simp only [answered] at returned
        cases returned
        apply initialize_pin _ publicKey _ _ pin
        have shape : pinned = (.ok (.Some pin), pinned.2) := by rw [← answered]
        rw [← shape]
        exact pinnedAt

/-- Every successful generated native startup derives the exact configured classical/ML pins internally. -/
theorem start_pin (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.server.pin.binding = ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ ∧
      initial.state.server.pin.public_key = initial.credential.publicKey := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
      simp only [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _generated, continued⟩ := continued
      cases chosen : generated.1 with
      | none => simp only [chosen, mem_support_pure_iff] at continued; cases continued
      | some credential =>
          simp only [chosen, mem_support_bind_iff] at continued
          obtain ⟨initialized, reached, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp only [native, mem_support_pure_iff] at returned; cases returned
          | ok reply => cases reply with
            | none => simp only [native, mem_support_pure_iff] at returned; cases returned
            | some state =>
                simp only [native, mem_support_pure_iff, Option.some.injEq] at returned
                cases returned
                have shape : initialized = (.ok (.Some state), initialized.2) := by rw [← native]
                have actual := frontend_pin created credential.publicKey RegistrationServerRoleBackend.empty generated.2 initialized.2 state
                  (by rw [← shape]; exact reached)
                exact actual

end BeaconcryptCore.Computational.RegistrationNativeServerPinStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinStartup.initialize_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinStartup.initialize_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinStartup.frontend_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinStartup.frontend_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinStartup.start_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinStartup.start_pin
