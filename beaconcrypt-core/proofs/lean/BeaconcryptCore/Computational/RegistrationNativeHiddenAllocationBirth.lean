-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners

/-! The actual native constructor first preserves allocation through every preflight and source draw, then creates its indexed KEM key and appends exactly one physical and one local owner. The retained physical address is derived from the actual allocator reply. No successful-initializer or state-preservation callback is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationBirth
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeBeaconFrontend
open RegistrationNativeHiddenAllocationRuntime (callback)
open RegistrationNativeHiddenAllocationOwners (NativeIndexed)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem source_support {Index : Type} {spec : OracleSpec Index} {Private : Type}
    (implementation : QueryImpl spec (StateT Private ProbComp)) (work : OracleComp spec Value)
    (before : Private) (result : Value × Private)
    (supported : result ∈ support ((simulateQ implementation work).run before)) : result.1 ∈ support work := by
  apply support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- Actual creation preserves the joint physical/local length and literal address invariant on every success and failure branch. -/
theorem create (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeHiddenAllocationRuntime.State n KemSK ProviderState Secret)
    (result : ((RustM (Option Nat) × State source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) ×
      RegistrationNativeHiddenAllocationRuntime.State n KemSK ProviderState Secret)
    (length : before.1.2.owners.length = owners.length) (indexed : NativeIndexed owners)
    (supported : result ∈ support ((simulateQ (callback setup wire sign seed scalar provider service codec route)
      (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run env)).run before)) :
    result.2.1.2.owners.length = result.1.1.2.length ∧ NativeIndexed result.1.1.2 := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have unchanged := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env middle.1
    (source_support _ _ before middle reached)
  have kept := RegistrationNativeHiddenAllocationRuntime.program_noappend setup wire sign seed scalar provider service codec route
    (((prepare source edPin mlPin keyId).run owners).run env) before middle
    (RegistrationNativeHiddenBeaconAllocationCaps.prepare_safe edPin mlPin keyId owners env) reached
  have leadingLength : middle.2.1.2.owners.length = middle.1.1.2.length := by rw [kept, unchanged, length]
  have leadingIndexed : NativeIndexed middle.1.1.2 := by rw [unchanged]; exact indexed
  cases selected : middle.1.1.1 with
  | fail error | div =>
      simp only [selected, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact ⟨leadingLength, leadingIndexed⟩
  | ok chosen => cases chosen with
    | none =>
        simp only [selected, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
        cases continued
        exact ⟨leadingLength, leadingIndexed⟩
    | some prepared =>
        simp only [selected] at continued
        obtain ⟨born, afterBorn, worldOwner, afterAppend, generated, allocated, returned⟩ :=
          RegistrationNativeBeaconBirth.append_supported setup source
            (callback setup wire sign seed scalar provider service codec route) edPin keyId prepared.pin
            prepared.identity prepared.prekey middle.1.1.2 middle.1.2 middle.2 result continued
        have kemKept := RegistrationNativeHiddenAllocationRuntime.query_noappend setup wire sign seed scalar provider service codec route
          (.inr (.inr (.inl .create))) middle.2 (born, afterBorn) trivial generated
        have appendReceipt := RegistrationNativeHiddenAllocationRuntime.query_append setup wire sign seed scalar provider service codec route
          keyId edPin .fresh afterBorn (worldOwner, afterAppend) allocated
        cases returned
        constructor
        · simp only [List.length_append, List.length_singleton]
          exact appendReceipt.2.trans (congrArg (· + 1) (kemKept.trans leadingLength))
        · apply RegistrationNativeHiddenAllocationOwners.append _ _ leadingIndexed
          exact appendReceipt.1.trans (kemKept.trans leadingLength)

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationBirth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationBirth.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationBirth.create
