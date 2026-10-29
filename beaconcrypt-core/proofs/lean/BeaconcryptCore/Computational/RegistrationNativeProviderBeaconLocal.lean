-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativePublicSourceFinishLocal
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport

/-! Restoring the privately retained input scalar reconstructs the entire actual owner after incoming completion. The comparison keeps the full returned owner rather than assuming that an erased scalar remained unchanged; that fact follows from the actual native finish AST. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconLocal
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState)
open RegistrationNativeProviderCallbacks (implementation)
open RegistrationNativeProviderBeaconAgreement (trusted)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationNativeProviderBeaconPreparation (drop)
open RegistrationNativePublicSourceFinishLocal (restorePublic recordView)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconFrontend (Owner Trusted)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem native_restore (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (interpreter : QueryImpl (Trusted n KemSK) (StateT (NativeState n KemSK ProviderState) ProbComp))
    (owner : Owner mlSource) (packet : Option registration.ResponsePacket)
    (env : EnvState RegistrationServerRoleBackend.State) (before : NativeState n KemSK ProviderState) :
    (fun result => (restorePublic owner.prekeyScalar (RegistrationBeaconReferenceNativeContinuation.view result.1), drop result.2)) <$>
      (simulateQ interpreter (((RegistrationBeaconReferenceNativeOwner.finish setup mlSource wire packet :
        RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
          (RustM (Option Pqxdh.Bytes))).run owner).run env)).run before =
      Prod.map recordView drop <$>
        (simulateQ interpreter (((RegistrationBeaconReferenceNativeOwner.finish setup mlSource wire packet :
          RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
            (RustM (Option Pqxdh.Bytes))).run owner).run env)).run before := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  rintro ⟨result, after⟩ supported
  have raw : result ∈ support (((RegistrationBeaconReferenceNativeOwner.finish (n := n) setup mlSource wire packet).run owner).run env) := by
    apply OracleComp.support_simulateQ_run'_subset interpreter
      (((RegistrationBeaconReferenceNativeOwner.finish (n := n) setup mlSource wire packet).run owner).run env) before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have restored := RegistrationNativeOrdinaryFinishSourceScalar.finish_restore setup wire owner packet env result raw
  simp only [restorePublic, RegistrationBeaconReferenceNativeContinuation.view, recordView, Prod.map_def, Function.comp_def, restored]

/-- Both selected and ordinary incoming completion retain the entire privately reconstructed owner and the actual shared source frame. Only the named record-request and memo analysis fields are projected. -/
theorem finish_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (selectedScalar : PqxdhJointGapDh.ScalarBytes)
    (localScalar : Option PqxdhJointGapDh.ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner : Owner mlSource) (packet : Option registration.ResponsePacket)
    (sameScalar : owner.prekeyScalar = localScalar.getD selectedScalar)
    (coherent : ∀ pending oneTime, owner.phase = .initSent pending oneTime →
      pending.control.expected_server_binding = pending.binding.server_pin.binding)
    (env : EnvState RegistrationServerRoleBackend.State) (empty : env.recordRequests = [])
    (erased : Std.Array U8 357#usize) (before : NativeState n KemSK ProviderState) :
    Prod.map (restorePublic owner.prekeyScalar) drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (((RegistrationBeaconReferenceFinish.finish setup mlSource packet :
            RegistrationBeaconReferenceCompletion.M (target := RegistrationBeaconReferenceCompiler.Spec n KemSK)
              (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run
                (RegistrationBeaconReferenceCompiler.eraseOwner owner)).run env))).run before =
      Prod.map recordView drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar provider)
          (((RegistrationBeaconReferenceNativeOwner.finish setup mlSource wire packet :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run owner).run env)).run before := by
  have native := RegistrationNativeProviderBeaconFinish.finish_source setup wire route sign seed selectedScalar localScalar provider
    owner packet sameScalar coherent env empty erased before
  have mapped := congrArg (fun distribution => Prod.map (restorePublic owner.prekeyScalar) id <$> distribution) native
  simp only [Functor.map_map, Prod.map_def, id_eq] at mapped
  exact mapped.trans (native_restore setup wire _ owner packet env before)

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconLocal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconLocal.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconLocal.finish_source
