-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend
/-! The actual extracted first-record seal and commitment hash operate on the same retained physical backend and fallible allocator. Their source projection erases only Local instrumentation and preserves every Rust outcome and persistent external state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterRecordBackend (project)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {E I KemSK Reader Response : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)

noncomputable def records : QueryImpl RegistrationRecordPrimitives.Spec (StateT (Backend n KemSK) m) :=fun query before=>
  simulateQ coins ((RegistrationNativePlatformPublicAdapterRecordBackend.records setup codec query).run before)

omit primitives in
theorem records_source (pool : PqxdhLiveKemBirth.Pool KemSK) (query : RegistrationRecordPrimitives.Spec.Domain)
    (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationNativePlatformServerCompletion.records coins setup codec query).run before=
      (records coins setup codec query).run (project pool before) := by
  have same:=congrArg (simulateQ coins) (RegistrationNativePlatformPublicAdapterRecordBackend.records_source setup codec pool query before)
  simpa only [simulateQ_map,records,RegistrationNativePlatformServerCompletion.records,
    RegistrationNativePlatformServerCompletion.liftNative,StateT.run] using same

noncomputable def aead (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitives.Nonce) (key : primitives.Key) : StateT (Backend n KemSK) m AdapterSealNative.NativeReply :=fun before=>
  (fun result=>(.ok (RegistrationNativePlatformSourceSeal.detached failure result.1),result.2)) <$>
    simulateQ coins ((RegistrationNativePlatformPublicAdapterRecordBackend.record setup codec
      (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))).run before)

theorem aead_source (pool : PqxdhLiveKemBirth.Pool KemSK)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitives.Nonce) (key : primitives.Key) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationNativePlatformSourceSeal.aead coins setup codec view failure plaintext associated nonce key).run before=
      (aead coins setup codec view failure plaintext associated nonce key).run (project pool before) := by
  have same:=congrArg (fun computation=>(fun result=>(RustM.ok (RegistrationNativePlatformSourceSeal.detached failure result.1),result.2)) <$>
    simulateQ coins computation) (RegistrationNativePlatformPublicAdapterRecordBackend.record_source setup codec pool
      (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key))) before)
  simpa only [aead,RegistrationNativePlatformSourceSeal.aead,StateT.run,simulateQ_map,Functor.map_map,Prod.map,id_eq] using same

noncomputable def handler : QueryImpl (AdapterSealNative.Spec E) (StateT (Backend n KemSK) m)
  | .reserve before capacity=>StateT.lift (RegistrationNativePlatformSourceSeal.reserve allocation before capacity)
  | .aead plaintext associated nonce key=>aead coins setup codec view failure plaintext associated nonce key

theorem handler_source (pool : PqxdhLiveKemBirth.Pool KemSK) (query : (AdapterSealNative.Spec E).Domain)
    (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation query).run before=
      (handler coins setup codec view failure allocation query).run (project pool before) := by
  cases query with
  | aead plaintext associated nonce key=>exact aead_source coins setup codec view failure pool plaintext associated nonce key before
  | reserve bytes capacity=>
    simp only [handler,RegistrationNativePlatformSourceSeal.handler,StateT.run_lift,bind_pure_comp,Functor.map_map]
    rfl

noncomputable def sealing (request : record_effects.AeadSealRequest) : StateT (Backend n KemSK) m (RustM AdapterSealNative.Output) :=
  simulateQ (handler coins setup codec view failure allocation ∘ₛ AdapterSealNative.native)
    (AdapterSealRequestExtraction.execute (E:=E) (m:=AdapterSealRequestMonad.Program E) request).run

theorem sealing_source (pool : PqxdhLiveKemBirth.Pool KemSK)
    (request : record_effects.AeadSealRequest) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request).run before=
      (sealing coins setup codec view failure allocation request).run (project pool before) := by
  unfold sealing
  rw [QueryImpl.simulateQ_compose]
  change _=(simulateQ (handler coins setup codec view failure allocation) (AdapterSealNative.source E request)).run (project pool before)
  rw [AdapterSealNative.source_native]
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project pool)
    (handler_source coins setup codec view failure allocation pool) (AdapterSealNative.execute E request) before
  simp only [RegistrationNativePlatformSourceSeal.sealing,StateT.run_bind,StateT.run_map,StateT.run_modify,
    Functor.map_map,map_pure,bind_pure_comp]
  change Prod.map id (project pool) <$>
    (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation) (AdapterSealNative.execute E request)).run before=_
  exact same

theorem extracted_source (pool : PqxdhLiveKemBirth.Pool KemSK)
    (request : record_effects.AeadSealRequest) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationNativePlatformExtractedSourceSeal.sealing coins setup codec view failure allocation request).run before=
      (sealing coins setup codec view failure allocation request).run (project pool before) := by
  rw [RegistrationNativePlatformExtractedSourceSeal.sealing_source]
  exact sealing_source coins setup codec view failure allocation pool request before

noncomputable def hash (erased transcript : commitment.CommitmentTranscript) :
    StateT (Backend n KemSK) m RegistrationNativePlatformCommitment.HashReply :=do
  let reply←records coins setup codec (.hash transcript)
  pure (.ok (reply,erased))

omit primitives in
theorem hash_source (pool : PqxdhLiveKemBirth.Pool KemSK)
    (erased transcript : commitment.CommitmentTranscript) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript).run before=
      (hash coins setup codec erased transcript).run (project pool before) := by
  have same:=congrArg (fun computation=>(fun result=>(RustM.ok (result.1,erased),result.2)) <$>computation)
    (records_source coins setup codec pool (.hash transcript) before)
  simpa only [hash,RegistrationNativePlatformSourceSeal.hash,bind_pure_comp,StateT.run_map,
    Functor.map_map,Prod.map,id_eq] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.records_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.records_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.aead_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.aead_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.handler_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.sealing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.sealing_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.extracted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.extracted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSealBackend.hash_source
