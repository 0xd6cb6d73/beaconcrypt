-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood

/-! Every adaptive provider-source client preserves live prepared roots, the canonical selected-owner mask and the actual controller metadata. Startup and the independent reserved-provider draw derive these internal invariants. The original public events and full private ledger are unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Good (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (selected : Nat) (before : FrontState n KemSK ProviderState source) :=
  RegistrationNativePublicSourceProgram.Good setup seed scalar selected (before.1, before.2.1)

theorem execute_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (implementation : QueryImpl spec (RegistrationNativePublicFrontend.M n KemSK source))
    (work : OracleComp spec Value) (before : FrontState n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider (simulateQ implementation work)).run before =
      (simulateQ (fun query => execute setup wire route sign seed scalar provider (implementation query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, RegistrationNativeProviderExecution.execute_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      rintro ⟨reply, after⟩
      exact ih reply after

/-- Every actual typed callback preserves the complete internal provider-source invariant. -/
theorem query_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : FrontState n KemSK ProviderState source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × FrontState n KemSK ProviderState source)
    (good : Good setup seed scalar selectedOwner before)
    (supported : result ∈ support
      ((execute setup wire route sign seed scalar provider
        (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept
          (setup.dh.publicKey scalar) query)).run before)) : Good setup seed scalar selectedOwner result.2 := by
  have roots := RegistrationNativeProviderLiveInvariant.query_live setup checks wire route sign seed scalar provider
    selectedOwner selectedAccept (setup.dh.publicKey scalar) query before result good.live good.memo supported
  have raw := RegistrationNativeProviderSource.observed_support setup wire route sign seed scalar provider _ before result supported
  have mask := RegistrationNativePublicMaskInvariant.query_canonical setup checks wire sign
    selectedOwner selectedAccept (setup.dh.publicKey scalar) query before.1 (result.1, result.2.1) good.mask raw
  have metadata := RegistrationNativePublicInvariantRun.query_good setup checks wire sign selectedOwner selectedAccept
    (setup.dh.publicKey scalar) query before.1 (result.1, result.2.1)
    ⟨(RegistrationNativePublicInvariantOwners.restored_holds scalar before.1.beacons).mpr good.coherent, good.empty⟩ raw
  exact ⟨roots.1, roots.2, mask,
    (RegistrationNativePublicInvariantOwners.restored_holds scalar result.2.1.beacons).mp metadata.1, metadata.2⟩

/-- The complete arbitrary adaptive typed client, including a compiled original secrecy ledger, retains all derived provider-source invariants. -/
theorem program_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (good : Good setup seed scalar selectedOwner before)
    (supported : result ∈ support
      ((execute setup wire route sign seed scalar provider
        (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept
          (setup.dh.publicKey scalar)) work)).run before)) : Good setup seed scalar selectedOwner result.2 := by
  rw [execute_program] at supported
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact good
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact ih middle.1 middle.2 result
        (query_good setup checks wire route sign seed scalar provider selectedOwner selectedAccept query before middle good reached) continued

/-- Actual closed startup and its subsequent reserved-data draw establish the whole invariant without a supplied live-root or coherence condition. -/
theorem startup_good {Data : Type} (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (started : RegistrationNativePublicStartup.Started source) (after : RegistrationNativePublicInterpreter.State n KemSK)
    (initialized : (some started, after) ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
        RegistrationNativePublicInterpreter.initial))
    (draw : ProbComp Data) (data : Data) (world : PqxdhRecordLiftWorld.State n)
    (_sampled : (data, world) ∈ support ((PqxdhRecordLiftWorld.sampled draw).run after.world))
    (providerInitial : Data → ProviderState) :
    Good setup seed scalar selected (started.frontend, ({ after with world := world }, providerInitial data)) := by
  have actual := RegistrationNativePublicSourceStartupGood.start_good setup source seed scalar ensureInit identityIndex serverKeyId
    selected started after initialized
  exact ⟨actual.live, actual.memo, actual.mask, actual.coherent, actual.empty⟩

end BeaconcryptCore.Computational.RegistrationNativeProviderProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderProgram.execute_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderProgram.execute_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderProgram.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderProgram.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderProgram.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderProgram.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderProgram.startup_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderProgram.startup_good
