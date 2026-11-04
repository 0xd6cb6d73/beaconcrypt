-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual public Server first-record body uses the checked prefixed seal and raw writer source programs in the same full Native/platform state. Selected initial/ongoing primitive replies keep their literal native request journal and counters. Every failed reservation, mutable commitment poststate, failed writer and enclosing Rust result propagates before the actual signing continuation. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerRecordNative
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerLocalLens (localState)
variable {n : Nat} {KemSK I Reader Response E : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "LocalM" => StateT (RegistrationServerRootCompiler.Local n) m
variable {target : Type → Type} [Monad target] [LawfulMonad target]
variable (F : ∀ {A : Type}, StateT (RegistrationServerRootCompiler.Local n) m A → target A)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
universe u v w
private theorem call_apply {monad : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction monad (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := monad) source arg = call (m := monad) (source arg) := rfl
private theorem call_result {monad : Type → Type} [AdapterRecordRequestMonad.LiftRust monad] {A : Type} (source : RustM A) :
    call (m := monad) source = AdapterRecordRequestMonad.liftRust source := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [sealingPrimitive : AdapterSealPrimitive.Operations]

@[instance_reducible] noncomputable def localOperations (previous : LocalOperations (RustT target))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m) : LocalOperations (RustT target) :=
  {previous with
    ratchet_initial_ratchet_hkdf := fun request => ⟨RustM.ok <$> F (AdapterPublicServerNativeKdf.initial setup request)⟩
    ratchet_execute_seal_request := fun request => ⟨F (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request)⟩
    ratchet_execute_write_request := fun request => ⟨F (RegistrationNativePlatformSourceBuild.write helper request)⟩}

@[instance_reducible] noncomputable def children (previous : ChildOperations (RustT target))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (erased : commitment.CommitmentTranscript) : ChildOperations (RustT target) :=
  {previous with
    ratchetHkdf := fun request => ⟨RustM.ok <$> F (AdapterPublicServerNativeKdf.ratchet coins setup codec request)⟩
    commitmentHash := fun transcript => ⟨F (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript)⟩}

noncomputable def kdf (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) : AdapterPublicServerRecord.Kdf target where
  initial request := F (AdapterPublicServerNativeKdf.initial setup request)
  ratchet request := F (AdapterPublicServerNativeKdf.ratchet coins setup codec request)

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT target)]

omit material platform ed sealingPrimitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
private theorem borrow_seal (work : target (RustM AdapterSealNative.Output)) :
    (do let detached ← (⟨work⟩ : RustT target AdapterSealNative.Output)
        let borrowed ← AdapterRecordRequestMonad.liftRust (core.option.Option.as_ref detached)
        AdapterPublicWrapperRequestMonad.Option.map
          beaconcrypt_public_request.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816 borrowed ()).run = work := by
  simp only [RustT.run_bind, RustT.run_liftRust]
  conv_rhs => rw [← bind_pure work]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok optional =>
    cases optional with
    | none => simp only [core.option.Option.as_ref, pure_bind]; rfl
    | some pair =>
      simp only [core.option.Option.as_ref, pure_bind, AdapterPublicWrapperRequestMonad.Option.map,
        RustT.run_bind, RustT.run_pure]
      rw [call_apply, call_apply, call_result]
      have closure : beaconcrypt_public_wrapper.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816.call_once () pair = .ok pair := rfl
      rw [closure, RustT.run_liftRust, pure_bind]

omit material platform ed sealingPrimitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
private theorem borrow_write (work : target (RustM (core.option.Option (alloc.vec.Vec U8)))) :
    (do let output ← (⟨work⟩ : RustT target (core.option.Option (alloc.vec.Vec U8)))
        AdapterRecordRequestMonad.liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) output)).run = work := by
  simp only [RustT.run_bind, RustT.run_liftRust]
  conv_rhs => rw [← bind_pure work]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok optional => cases optional <;> rfl

omit [LawfulMonad m] [LawfulMonad target] material platform ed sealingPrimitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
private theorem first_record_congr
    (left right : QueryImpl RegistrationRecordPrimitives.Spec target)
    (sameInitial : ∀ request, left (.initialKdf request) = right (.initialKdf request))
    (sameRatchet : ∀ request, left (.ratchetKdf request) = right (.ratchetKdf request))
    (sealing : record_effects.AeadSealRequest → target (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → target RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → target (RustM (core.option.Option (Slice U8))))
    (initial : registration.ServerInitialKdf) :
    RegistrationNativePlatformSourceRecord.fromInitialWithHash left sealing hash write initial =
      RegistrationNativePlatformSourceRecord.fromInitialWithHash right sealing hash write initial := by
  unfold RegistrationNativePlatformSourceRecord.fromInitialWithHash
  apply congrArg (RegistrationNativePlatformServerRecord.continueWith initial.request)
  funext request
  rw [sameInitial]
  apply bind_congr
  intro response
  apply congrArg (RegistrationNativePlatformServerRecord.continueResult (initial.resume response))
  funext pending
  unfold RegistrationNativePlatformSourceRecord.fromRatchetWithHash
  apply congrArg (RegistrationNativePlatformServerRecord.continueWith pending.request)
  funext request
  rw [sameRatchet]

omit ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
/-- The actual source first-record leaf actions have the same complete result and poststate before the SDK signing continuation. This exposes the exact boundary at which an analysis observer records the returned source first-record result. -/
theorem first_source (hom : Cslib.IsMonadHom LocalM target F) (previousLocal : LocalOperations (RustT target)) (previousChildren : ChildOperations (RustT target))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (initial :registration.ServerInitialKdf) :
    letI :LocalOperations (RustT target):=localOperations F previousLocal coins setup codec view failure allocation helper
    letI :ChildOperations (RustT target):=children F previousChildren coins setup codec erased
    RegistrationNativePlatformSourceRecord.fromInitialWithHash
      (AdapterPublicServerRecord.recordOperations (kdf F coins setup codec)) AdapterPublicServerRecord.sealLeaf
      (fun transcript=>(@ChildOperations.commitmentHash (RustT target) inferInstance transcript).run) AdapterPublicServerRecord.writeLeaf initial=
      F (RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (RegistrationNativePlatformServerCompletion.records coins setup codec)
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper) initial) :=by
  let : LocalOperations (RustT target) := localOperations F previousLocal coins setup codec view failure allocation helper
  let : ChildOperations (RustT target) := children F previousChildren coins setup codec erased
  have sealEq : AdapterPublicServerRecord.sealLeaf (m := target) =
      fun request => F (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request) := by
    funext request
    exact borrow_seal _
  have writeEq : AdapterPublicServerRecord.writeLeaf (m := target) =
      fun request => F (RegistrationNativePlatformSourceBuild.write helper request) := by
    funext request
    exact borrow_write _
  rw [sealEq, writeEq]
  have initialEq : ∀ request, AdapterPublicServerRecord.recordOperations
      (kdf F coins setup codec) (.initialKdf request) =
      F (RegistrationNativePlatformServerCompletion.records coins setup codec (.initialKdf request)) := by
    intro request
    rw [AdapterPublicServerNativeKdf.initial_callback]
    simp only [AdapterPublicServerRecord.recordOperations, kdf,
      map_eq_bind_pure_comp, Function.comp_def, hom.map_bind, hom.map_pure]
  have ratchetEq : ∀ request, AdapterPublicServerRecord.recordOperations
      (kdf F coins setup codec) (.ratchetKdf request) =
      F (RegistrationNativePlatformServerCompletion.records coins setup codec (.ratchetKdf request)) := by
    intro request
    rw [AdapterPublicServerNativeKdf.ratchet_callback]
    simp only [AdapterPublicServerRecord.recordOperations, kdf,
      map_eq_bind_pure_comp, Function.comp_def, hom.map_bind, hom.map_pure]
  rw [first_record_congr _ (fun query => F (RegistrationNativePlatformServerCompletion.records coins setup codec query)) initialEq ratchetEq]
  rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash_map hom]
  rfl

theorem source (hom : Cslib.IsMonadHom LocalM target F) (previousLocal : LocalOperations (RustT target)) (previousChildren : ChildOperations (RustT target))
    (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealingPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (erased : commitment.CommitmentTranscript)
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    letI : LocalOperations (RustT target) := localOperations F previousLocal coins setup codec view failure allocation helper
    letI : ChildOperations (RustT target) := children F previousChildren coins setup codec erased
    (AdapterPublicServerBuildBody.record (m := target) self initial).run = (do
      let recorded ← F (RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (RegistrationNativePlatformServerCompletion.records coins setup codec)
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper) initial)
      AdapterPublicServerRecord.afterRecord self recorded) := by
  let : LocalOperations (RustT target) := localOperations F previousLocal coins setup codec view failure allocation helper
  let : ChildOperations (RustT target) := children F previousChildren coins setup codec erased
  rw [AdapterPublicServerRecord.record (kdf F coins setup codec) ⟨fun _ => rfl, fun _ => rfl⟩]
  have sealEq : AdapterPublicServerRecord.sealLeaf (m := target) =
      fun request => F (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request) := by
    funext request
    exact borrow_seal _
  have writeEq : AdapterPublicServerRecord.writeLeaf (m := target) =
      fun request => F (RegistrationNativePlatformSourceBuild.write helper request) := by
    funext request
    exact borrow_write _
  rw [sealEq, writeEq]
  have initialEq : ∀ request, AdapterPublicServerRecord.recordOperations
      (kdf F coins setup codec) (.initialKdf request) =
      F (RegistrationNativePlatformServerCompletion.records coins setup codec (.initialKdf request)) := by
    intro request
    rw [AdapterPublicServerNativeKdf.initial_callback]
    simp only [AdapterPublicServerRecord.recordOperations, kdf,
      map_eq_bind_pure_comp, Function.comp_def, hom.map_bind, hom.map_pure]
  have ratchetEq : ∀ request, AdapterPublicServerRecord.recordOperations
      (kdf F coins setup codec) (.ratchetKdf request) =
      F (RegistrationNativePlatformServerCompletion.records coins setup codec (.ratchetKdf request)) := by
    intro request
    rw [AdapterPublicServerNativeKdf.ratchet_callback]
    simp only [AdapterPublicServerRecord.recordOperations, kdf,
      map_eq_bind_pure_comp, Function.comp_def, hom.map_bind, hom.map_pure]
  rw [first_record_congr _ (fun query => F (RegistrationNativePlatformServerCompletion.records coins setup codec query)) initialEq ratchetEq]
  rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash_map hom]
  rfl
end BeaconcryptCore.Refinement.AdapterPublicServerRecordNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecordNative.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecordNative.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecordNative.first_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecordNative.first_source
