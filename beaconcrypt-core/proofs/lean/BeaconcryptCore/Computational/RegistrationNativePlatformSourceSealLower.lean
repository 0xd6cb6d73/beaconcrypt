-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationServerRecordWorldSource
/-! Actual detached sealing is local functional AEAD plus the same stateful allocation service. The stated source view removes only native-call and chronological-kind instrumentation and the separately billed Env coin ledger. It retains uniform/hash/admin counts, cache, protocol state and the entire outer platform computation. This view is explicit and is not literal equality of the omitted instrumentation. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRecordWorldSource (project)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {E Auxiliary Value ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) : QueryImpl (AdapterSealNative.Spec E) m
  | .reserve before capacity => RegistrationNativePlatformSourceSeal.reserve allocation before capacity
  | .aead plaintext associated nonce key =>
    let input := RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key
    pure (.ok (RegistrationNativePlatformSourceSeal.detached failure
      (some (source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))))

def sealing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (request : record_effects.AeadSealRequest) :
    m (RustM AdapterSealNative.Output) :=
  simulateQ (handler source view failure allocation) (AdapterSealNative.execute E request)

private def charged (before : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { before with world := ({ before.world.1 with primitive :=
      ({ before.world.1.primitive.1 with native := Function.update before.world.1.primitive.1.native RawCtxMixedOwner.CallKind.sealing (before.world.1.primitive.1.native .sealing + 1) }, before.world.1.primitive.2) }, before.world.2) }

private theorem query (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (request : (AdapterSealNative.Spec E).Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation request).run before =
      (StateT.lift (handler setup.source view failure allocation request)).run (project before) := by
  cases request with
  | reserve previous capacity =>
    simp only [RegistrationNativePlatformSourceSeal.handler, handler, StateT.run_lift, bind_pure_comp, Functor.map_map]
    rfl
  | aead plaintext associated nonce key =>
    have actual : (RegistrationWorldRecords.record setup codec
        (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))).run before =
      pure (some (setup.source.crypto.aeadSeal
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).key
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).nonce
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).associatedData
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).plaintext), charged before) := rfl
    change Prod.map id project <$> (RegistrationNativePlatformSourceSeal.aead coins setup codec view failure plaintext associated nonce key).run before = _
    rw [RegistrationNativePlatformSourceSeal.aead_run, actual, simulateQ_pure, map_pure, map_pure]
    simp only [handler, StateT.run_lift, pure_bind]
    rfl

omit primitive in
private theorem lifted_program {S : Type} {I : Type} {spec : OracleSpec I}
    (implementation : QueryImpl spec m) (work : OracleComp spec Value) (before : S) :
    (simulateQ (fun query => StateT.lift (implementation query)) work).run before =
      (fun value => (value, before)) <$> simulateQ implementation work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_lift,
      ih, map_bind, bind_assoc, pure_bind]

/-- The actual free seal request program retains every dynamic allocation and native reply after precisely the stated accounting view. -/
theorem program (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (work : OracleComp (AdapterSealNative.Spec E) Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation) work).run before =
      (fun value => (value, project before)) <$> simulateQ (handler setup.source view failure allocation) work := by
  rw [OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query coins setup codec view failure allocation) work before, lifted_program]

/-- The entire actual source detached-seal dispatcher lowers to local functional AEAD and its unchanged common-state allocator, retaining every source failure and divergence. -/
theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (request : record_effects.AeadSealRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request).run before =
      (fun value => (value, project before)) <$> sealing setup.source view failure allocation request := by
  simp only [RegistrationNativePlatformSourceSeal.sealing, StateT.run_bind, StateT.run_map, StateT.run_modify,
    map_pure, bind_pure_comp, Functor.map_map]
  change Prod.map id project <$> (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
    (AdapterSealNative.execute E request)).run before = _
  exact program coins setup codec view failure allocation _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower.source
