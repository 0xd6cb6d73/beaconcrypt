-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport
/-! Actual create, stateful Init publication and terminal-gated ordinary routes make no deferred Word material request. The three unused material branches of the separate ordinary dictionary are pure defaults; the complete dispatcher selects its proved material controllers instead. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinaryCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSecretWordOrdinary
open RegistrationNativeSecretWordInterpreterCaps (IsDemand)
open RegistrationNativePlatformSecretWordCapsTransport (base_bound platform_zero)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem gate_free (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : A → Nat) (output : Option A) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platform (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply isQueryBoundP_bind (n := 0) (m := 0) (platform_zero _ before)
    rintro ⟨result, after⟩ _
    cases result <;> trivial

private theorem record_free (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [IsDemand], ?_⟩
    intro output
    simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsDemand, ite_false] using gate_free reserve _ output before.2
  · simp [record, StateT.run, isQueryBoundP_map_iff, IsDemand, isQueryBoundP_query_iff]
  · simp only [record, StateT.run]
    split
    · trivial
    · rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [IsDemand], ?_⟩
      intro output
      simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsDemand, ite_false] using gate_free reserve _ output before.2
  · simp only [record, StateT.run]
    split
    · trivial
    · simp [isQueryBoundP_map_iff, IsDemand, isQueryBoundP_query_iff]

/-- The actual ordinary dictionary has zero material requests for every input and complete persistent platform outcome. -/
theorem handler_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    ((handler (n := n) setup source selected publicPrekey reserveFrame writer query).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, RegistrationNativeSecretWordFrontend.effect, IsDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  | inr query => cases query with
    | create edPin mlPin keyId =>
      simp only [handler, beacon, StateT.run, isQueryBoundP_map_iff]
      exact base_bound RegistrationNativeSecretWordMessage.zero _ 0
        (RegistrationNativePlatformPublicMaterialLocal.create_zero setup source selected publicPrekey edPin mlPin keyId _ _ _)
    | bundle index =>
      simp only [handler, beacon, StateT.run, map_apply, isQueryBoundP_map_iff]
      exact base_bound RegistrationNativeSecretWordMessage.zero _ 0
        (RegistrationNativePlatformPublicMaterialLocal.bundle_zero setup source writer selected publicPrekey index _ _ _)
    | accept packet | build handle application | finish index packet | hmac key bytes => trivial
    | hash bytes => simp [handler, StateT.run_lift, bind_pure_comp, RegistrationNativeSecretWordFrontend.effect, IsDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | serverSend keyId plaintext => exact record_free reserveFrame (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_free reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free reserveFrame (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact record_free reserveFrame (.inr (index, .inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinaryCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinaryCaps.handler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinaryCaps.handler_free
