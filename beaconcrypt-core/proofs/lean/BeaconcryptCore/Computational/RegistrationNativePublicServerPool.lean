-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry

/-! A native Server accept never touches the private owner KEM pool. The receipt preserves the complete pool transcript as well as generated pairs; it is derived through the actual open collector, authentication, source preparation and one-use retention. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicServerPool
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceBackend (State)
open RegistrationNativeKemReferencePrefix (lower sourcePrefix)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat} {ι KemSK Extra Value Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}

private theorem lower_program (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (interpreter : QueryImpl spec (StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK))))
    (work : OracleComp spec Value) : lower setup callbacks (simulateQ interpreter work) =
      simulateQ (fun query => lower setup callbacks (interpreter query)) work := by
  have same : (fun query => lower setup callbacks (interpreter query)) =
      ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT := rfl
  rw [same]
  funext before
  change (lower setup callbacks (simulateQ interpreter work)).run before =
    (simulateQ ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT work).run before
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (implementation setup callbacks) ((simulateQ interpreter work).run before.1)).run before.2 = _
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change id <$> (simulateQ ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT work).run before = _
  exact id_map _

private theorem prep_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain)
    (before : State n KemSK Extra)
    (result : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Range query × State n KemSK Extra)
    (supported : result ∈ support ((lower setup callbacks
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend setup checks) query)).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  cases query <;> simp only [RegistrationAgreementInterpreter.prepImpl] at supported
  all_goals first
    | (rw [lower_program] at supported
       exact RegistrationNativeKemReferenceFrame.program_frame setup checks callbacks _ before result supported)
    | (simp only [lower, StateT.run] at supported
       subst result
       exact ⟨rfl, rfl⟩)

private theorem prefix_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : State n KemSK Extra)
    (result : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Range query × State n KemSK Extra)
    (supported : result ∈ support ((lower setup callbacks (sourcePrefix setup checks query)).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  cases query with
  | staticDh point =>
      simp only [sourcePrefix, PqxdhServerStaticDhSource.prefixImpl,
        RegistrationNativeKemReferenceCompiler.visit, RegistrationNativeKemReferenceCompiler.ordinary,
        RegistrationServerReferenceCompiler.visit, lower, StateT.run,
        StateT.monad_pure_def, StateT.pure, StateT.monad_bind_def, StateT.bind,
        simulateQ_pure, map_pure, pure_bind, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | decode raw => exact prep_frame setup checks callbacks (.decode raw) before result supported
  | identity packet => exact prep_frame setup checks callbacks (.identity packet) before result supported
  | identityPoint key => exact prep_frame setup checks callbacks (.identityPoint key) before result supported
  | pqField packet => exact prep_frame setup checks callbacks (.pqField packet) before result supported
  | preField packet => exact prep_frame setup checks callbacks (.preField packet) before result supported
  | oneField packet => exact prep_frame setup checks callbacks (.oneField packet) before result supported
  | verify key signed => exact prep_frame setup checks callbacks (.verify key signed) before result supported
  | registrationStatus identifier => exact prep_frame setup checks callbacks (.registrationStatus identifier) before result supported
  | reserveRegistration => exact prep_frame setup checks callbacks .reserveRegistration before result supported
  | parseDh point => exact prep_frame setup checks callbacks (.parseDh point) before result supported
  | generate => exact prep_frame setup checks callbacks .generate before result supported
  | parseKem key => exact prep_frame setup checks callbacks (.parseKem key) before result supported
  | encapsulate key => exact prep_frame setup checks callbacks (.encapsulate key) before result supported
  | publicConversion key => exact prep_frame setup checks callbacks (.publicConversion key) before result supported
  | privateConversion => exact prep_frame setup checks callbacks .privateConversion before result supported
  | ephemeralDh secret point => exact prep_frame setup checks callbacks (.ephemeralDh secret point) before result supported

/-- The actual entire Server collector retains every owner private key and the complete pool history. -/
theorem collect_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Extra)
    (result : Option (PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding) × State n KemSK Extra)
    (supported : result ∈ support ((lower setup callbacks
      (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  change result ∈ support ((lower setup callbacks (simulateQ (sourcePrefix setup checks)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run before) at supported
  rw [lower_program] at supported
  generalize PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated) = work at supported
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      obtain ⟨poolFirst, extraFirst⟩ := prefix_frame setup checks callbacks query before step reached
      obtain ⟨poolLast, extraLast⟩ := ih step.1 step.2 result tail
      exact ⟨poolLast.trans poolFirst, extraLast.trans extraFirst⟩

end BeaconcryptCore.Computational.RegistrationNativePublicServerPool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicServerPool.collect_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicServerPool.collect_frame
