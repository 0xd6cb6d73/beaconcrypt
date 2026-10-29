-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices

/-! Every reached native outgoing callback keeps the ordinary per-handle joint history synchronized with the current owner history. Actual signing is recorded before attached-buffer packing. Hashes, optional ML signing and all their native side effects retain these identity receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend
open RegistrationNativeIdentityHistoryInvariant
open RegistrationNativeIdentitySourceSimulation (runNew liftAmbient)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem lift_effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    (liftAmbient (StateT.lift ((Ambient n KemSK).query (.inl query))) : M n KemSK Auxiliary source _) = effect query := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [liftAmbient, effect, StateT.run_lift, bind_pure_comp, StateT.run_map,
    simulateQ_map, simulateQ_spec_query, ambientLift]
  rfl

private theorem lift_modify (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary →
    RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (liftAmbient (modify change) : M n KemSK Auxiliary source Unit) = updateEnv change := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [liftAmbient, updateEnv, StateT.run_lift, StateT.run_modify, simulateQ_pure,
    StateT.run_map, bind_pure_comp, map_pure]
  rfl

theorem program_preserves {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (implementation : QueryImpl spec (M n KemSK Auxiliary source))
    (step : ∀ query, Preserves setup checks representation created index handle (implementation query))
    (work : OracleComp spec Value) :
    Preserves setup checks representation created index handle (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_preserves setup checks representation created index handle value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_preserves setup checks representation created index handle _ _ (step query) ih

theorem effect_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Preserves (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle (effect query) := by
  rw [← lift_effect]
  exact ambient_preserves setup checks representation created index handle _

theorem sample_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat) (work : ProbComp Value) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle (sample work) :=
  program_preserves setup checks representation created index handle _
    (fun query => effect_preserves setup checks representation created index handle (.inl query)) work

theorem update_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Preserves (n := n) (source := source) setup checks representation created index handle (updateEnv change) := by
  rw [← lift_modify]
  exact ambient_preserves setup checks representation created index handle _

theorem ed_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (request : registration.Ed25519SigningRequest) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (outgoing setup source index owner (.inr request)) := by
  classical
  by_cases matching : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
  · intro before result prior supported
    have fields := fields_run setup checks representation created _
      (RegistrationNativeIdentityMetadata.outgoing_preserves setup index owner (.inr request)) before result supported
    obtain ⟨current, found, same⟩ := at_owner index owner.identity.handle before.1.1 prior.2
    obtain ⟨seed, receipt⟩ := prior.1.1 current (List.mem_of_getElem? found)
    have seedAt : before.2.identities.seeds[owner.identity.handle]? = some seed := by
      rw [← same]
      exact receipt.1
    rw [runNew, RegistrationNativeIdentityWorldServices.outgoing_ed_source setup checks representation created
      index owner request seed before.1.1 before.1.2 before.2 seedAt matching, map_pure, mem_support_pure_iff] at supported
    cases supported
    apply fields_preserve setup.joint index owner.identity.handle before _ prior fields rfl
    simp only [RegistrationNativeIdentityWorldServices.appendHistory, found]
    rw [← same]
    exact RegistrationNativeIdentityHistorySync.signed_sync before.2.identities before.1.1 index current found
      prior.1.2.1 prior.1.2.2 (TranscriptAuthParts.absSlice request.message)
      (setup.joint.sign seed (TranscriptAuthParts.absSlice request.message))
  · simpa only [outgoing, ite_eq_right matching] using
      (pure_preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index owner.identity.handle
        (core.option.Option.None : RegistrationSigningShared.SignReply))

theorem query_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (outgoing setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_preserves setup checks representation created index owner.identity.handle _
    | sign request payload digest =>
        exact bind_preserves setup checks representation created index owner.identity.handle _ _
          (sample_preserves setup checks representation created index owner.identity.handle _)
          (fun reply => bind_preserves setup checks representation created index owner.identity.handle _ _
            (update_preserves setup checks representation created index owner.identity.handle _)
            (fun _ => pure_preserves setup checks representation created index owner.identity.handle reply))
  | inr request => exact ed_preserves setup checks representation created index owner request

/-- The full actual Ed3, fingerprint, transcript-signing and dynamic publication controller retains synchronized histories through every return path. -/
theorem init_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (simulateQ (outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)) :=
  program_preserves setup checks representation created index owner.identity.handle _
    (query_preserves setup checks representation created index owner) _

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.program_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.program_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.effect_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.effect_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.sample_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.sample_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.update_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.update_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.ed_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.ed_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.query_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.query_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.init_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing.init_preserves
