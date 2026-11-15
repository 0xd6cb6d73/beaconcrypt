-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerLocalLens
import BeaconcryptCore.Refinement.AdapterPublicServerRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Selected functional initial and ongoing HKDF replies retain the actual native request journal and complete Local state. The ongoing response executes the literal native primitive and its counter; neither operation samples fresh independent keys. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf
open BeaconcryptCore.Computational
variable {n : Nat} {KemSK I Reader Response A : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "LocalM" => StateT (RegistrationServerRootCompiler.Local n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

noncomputable def initial (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (request : ratchet.InitialRatchetKdfRequest) : LocalM (Std.Array U8 64#usize) := do
  modify fun before => {before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.initialKdf request)]}
  pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes

noncomputable def ratchet (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (request : ratchet.SymmetricRatchetKdfRequest) :
    LocalM ratchet.RatchetKdfResponse := do
  let response ← RegistrationNativePlatformServerCompletion.liftNative coins
    (RegistrationWorldRecords.record setup codec (.inl request))
  modify fun before => {before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.ratchetKdf request)]}
  pure response

theorem initial_callback (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (request : ratchet.InitialRatchetKdfRequest) :
    RegistrationNativePlatformServerCompletion.records (n := n) coins setup codec (.initialKdf request) =
      (fun bytes => core.option.Option.Some (⟨bytes⟩ : pqxdh.concrete.InitialRatchetKdfResponse)) <$> initial setup request := by
  apply StateT.ext
  intro before
  change simulateQ coins (pure (core.option.Option.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request),
      {before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.initialKdf request)]})) = _
  simp only [simulateQ_pure, StateT.run_map, initial, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, map_pure]

theorem ratchet_callback (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (request : ratchet.SymmetricRatchetKdfRequest) :
    RegistrationNativePlatformServerCompletion.records (n := n) coins setup codec (.ratchetKdf request) =
      core.option.Option.Some <$> ratchet coins setup codec request := by
  apply StateT.ext
  intro before
  change simulateQ coins ((RegistrationWorldRecords.handler setup codec (.ratchetKdf request)).run before) = _
  rw [StateT.run_map]
  unfold ratchet
  rw [StateT.run_bind]
  simp only [StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp, Functor.map_map]
  change simulateQ coins ((fun result => (core.option.Option.Some result.1,
      {before with world := ({before.world.1 with primitive := result.2}, before.world.2), recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.ratchetKdf request)]})) <$>
      (PqxdhRecordLiftWorld.primitives setup codec (.inl request)).run before.world.1.primitive) = _
  simp only [RegistrationNativePlatformServerCompletion.liftNative, RegistrationWorldRecords.record, StateT.run, simulateQ_map, Functor.map_map]

noncomputable def operations (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) : AdapterPublicServerRecord.Kdf NativeM where
  initial request := AdapterPublicServerLocalLens.localState (initial setup request)
  ratchet request := AdapterPublicServerLocalLens.localState (ratchet coins setup codec request)

end BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf.initial_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf.initial_callback
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf.ratchet_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerNativeKdf.ratchet_callback
