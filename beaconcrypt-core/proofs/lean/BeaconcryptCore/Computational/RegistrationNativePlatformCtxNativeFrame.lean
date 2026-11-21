-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
/-! All non-hash native record leaves preserve and cannot read CTX addresses. Their actual KDF/AEAD/writer replies and category counters are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxNativeFrame
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
variable {I KemSK Reader Response : Type} {base : OracleSpec I}

private theorem state_pure_apply {S V : Type} {m : Type → Type} [Monad m]
    (value : V) (before : S) :
    (pure value : StateT S m V) before = pure (value, before) := rfl

def NonHash : RawCtxMixedOwner.NativeSpec.Domain → Prop
  | .inr (.inr (.inr (.inl _))) => False
  | _ => True

theorem primitives (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (allowed : NonHash query)
    (before : Primitive) (cache : CtxRomAuth.CtxRO.QueryCache) :
    Prod.map id (fun after => (after.1, cache)) <$>
      (PqxdhRecordLiftWorld.primitives setup codec query).run before =
      (PqxdhRecordLiftWorld.primitives setup codec query).run (before.1, cache) := by
  rcases query with request | input | opening | bytes | frame
  all_goals first
    | exact False.elim allowed
    | simp only [PqxdhRecordLiftWorld.primitives, PqxdhDeploymentNative.primitives,
        RawCtxMixedShared.sharedImpl, QueryImpl.apply_compose, RawCtxMixedShared.sharedAdapter,
        simulateQ_spec_query, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl,
        RawCtxSourceHkdf.kdfImpl, simulateQ_pure, StateT.run, Prod.map_def, id_eq]
  all_goals simp only [state_pure_apply, simulateQ_pure, pure_bind, map_pure]
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxNativeFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxNativeFrame.primitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxNativeFrame.primitives
