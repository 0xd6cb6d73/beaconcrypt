-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap

/-! Corrected Platform authentication, assigned-ID finish and all other non-signing callbacks are parametric in the ML private-key representation. Only the actual verifier is required to agree. The full native state and arbitrary shared platform effects, including repeated pin hashing and reservations, remain together. No closed generation/signing equality or old/new-profile equality is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap
open BeaconcryptCore.Refinement
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaMap (Map owner nativeState)
open PqxdhServerAuthExperiment (Setup Checks)
variable {left right : Source} {n : Nat} {E KemSK Auxiliary Value Other Next OtherNext ι : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

section Finish
open RegistrationNativeMldsaOrdinaryMap

private theorem abort_pure_natural (mapping : Map left right)
    (current : RegistrationNativeBeaconFrontend.Owner left) (value : Value) :
    RegistrationNativeMldsaOrdinaryMap.Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.abort current *> pure value)
      (RegistrationNativeBeaconFrontend.abort (owner mapping current) *> pure value) := by
  simp only [seqRight_eq_bind]
  apply bind_natural mapping id id _ _ _ _ (abort_natural mapping current)
  intro _aborted
  exact pure_natural mapping id value

/-- Literal assigned-ID install is independent of the private ML credential representation. -/
theorem install_natural (mapping : Map left right) (index : Nat) (current : RegistrationNativeBeaconFrontend.Owner left)
    (completed : registration.CompletedBeacon) :
    RegistrationNativeMldsaOrdinaryMap.Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativePlatformBeaconFinish.install index current completed)
      (RegistrationNativePlatformBeaconFinish.install index (owner mapping current) completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact, RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_natural mapping id id _ _ _ _ (effect_natural mapping _)
  intro installed
  simp only [id_eq]
  cases installed with
  | false => exact abort_pure_natural mapping current _
  | true =>
    apply bind_natural mapping id id _ _ _ _ (phase_natural mapping index (.established _))
    intro _changed
    exact pure_natural mapping id _

/-- The actual post-authentication continuation preserves source-state mapping on failed agreement, opening and installation branches. -/
theorem after_natural (mapping : Map left right) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) :
    RegistrationNativeMldsaOrdinaryMap.Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index current oneTime accepted)
      (RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index (owner mapping current) oneTime accepted) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_natural mapping id id _ _ _ _ (simulate_natural mapping _ _ (agreement_natural mapping setup current oneTime) _)
  intro agreed
  simp only [id_eq]
  cases agreed with
  | fail error | div => exact abort_pure_natural mapping current _
  | ok effect =>
    cases effect
    all_goals first
      | exact abort_pure_natural mapping current _
      | apply bind_natural mapping id id _ _ _ _
          (simulate_natural mapping _ _ (RegistrationNativeMldsaControllerMap.record_natural mapping setup wire) _)
        intro opened
        simp only [id_eq]
        cases opened with
        | fail error | div => exact abort_pure_natural mapping current _
        | ok answer => cases answer with
          | Err previous => exact abort_pure_natural mapping current _
          | Ok completed => exact install_natural mapping index current completed

/-- Actual corrected finish depends on the unchanged verifier, public fields and source callbacks, never the ML secret representation. -/
theorem finish_natural (mapping : Map left right) (sameVerify : left.verify = right.verify)
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativeMldsaOrdinaryMap.Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativePlatformBeaconFinish.finish setup left wire index packet)
      (RegistrationNativePlatformBeaconFinish.finish setup right wire index packet) := by
  unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith
  apply bind_natural mapping (RegistrationNativeMldsaMap.owners mapping) id _ _ _ _ (get_natural mapping)
  intro before
  simp only [RegistrationNativeMldsaMap.owners_lookup]
  cases before[index]? with
  | none => exact pure_natural mapping id _
  | some current =>
    simp only [Option.map_some]
    dsimp only [RegistrationNativeMldsaMap.owner]
    cases current.phase with
    | fresh | freshWithCoins oneTime | established completed | aborted previous => exact pure_natural mapping id _
    | initSent pending oneTime =>
      simp only
      cases pending.aborted_state with
      | fail error | div => exact pure_natural mapping id _
      | ok aborted =>
        apply bind_natural mapping id id _ _ _ _ (phase_natural mapping index (.aborted aborted))
        intro _changed
        apply bind_natural mapping id id _ _ _ _ (simulate_natural mapping _ _ (authentication_natural mapping sameVerify setup) _)
        intro authenticated
        simp only [id_eq]
        cases authenticated with
        | fail error | div => exact abort_pure_natural mapping current _
        | ok answer => cases answer with
          | Err previous => exact abort_pure_natural mapping current _
          | Ok accepted => exact after_natural mapping setup wire index current oneTime accepted
end Finish

abbrev Natural (mapping : Map left right) (value : Value → Other)
    (first : RegistrationNativePlatformExperiment.M n KemSK left m Value)
    (second : RegistrationNativePlatformExperiment.M n KemSK right m Other) : Prop :=
  ∀ before, Prod.map value (nativeState mapping) <$> first.run before = second.run (nativeState mapping before)

private theorem pure_natural (mapping : Map left right) (value : Value → Other) (input : Value) :
    Natural (n := n) (KemSK := KemSK) (m := m) mapping value (pure input) (pure (value input)) := by
  intro before
  simp only [StateT.run_pure, map_pure]
  rfl

private theorem bind_natural (mapping : Map left right) (value : Value → Other) (nextValue : Next → OtherNext)
    (first : RegistrationNativePlatformExperiment.M n KemSK left m Value)
    (second : RegistrationNativePlatformExperiment.M n KemSK right m Other)
    (nextFirst : Value → RegistrationNativePlatformExperiment.M n KemSK left m Next)
    (nextSecond : Other → RegistrationNativePlatformExperiment.M n KemSK right m OtherNext)
    (initial : Natural mapping value first second)
    (continued : ∀ input, Natural mapping nextValue (nextFirst input) (nextSecond (value input))) :
    Natural mapping nextValue (first >>= nextFirst) (second >>= nextSecond) := by
  intro before
  simp only [StateT.run_bind, map_bind]
  rw [← initial before, bind_map_left]
  apply bind_congr
  intro result
  exact continued result.1 result.2

/-- Arbitrary common coins preserve an exact native credential-map equality, including complete platform state. -/
theorem liftNative_natural (mapping : Map left right) (value : Value → Other) (coins : QueryImpl unifSpec m)
    (first : RegistrationNativeExperiment.M n KemSK left Value)
    (second : RegistrationNativeExperiment.M n KemSK right Other)
    (law : RegistrationNativeMldsaGlobalMap.Natural mapping value first second) :
    Natural mapping value (RegistrationNativePlatformExperiment.liftNative coins first)
      (RegistrationNativePlatformExperiment.liftNative coins second) := by
  intro before
  simp only [RegistrationNativePlatformExperiment.liftNative, StateT.run]
  have body := law before
  simp only [StateT.run] at body
  rw [← simulateQ_map, body]

private theorem server_natural (mapping : Map left right)
    (work : StateT (RegistrationServerFrontendCompiler.State n) m Value) :
    Natural (KemSK := KemSK) mapping id (RegistrationNativePlatformExperiment.server work)
      (RegistrationNativePlatformExperiment.server work) := by
  intro before
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, Functor.map_map]
  rfl

private theorem parsed_natural (mapping : Map left right) :
    Natural (n := n) (KemSK := KemSK) (m := m) mapping id
      (modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 })
      (modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 }) := by
  intro before
  simp only [StateT.run_modify, map_pure]
  rfl

variable [primitive : AdapterSealPrimitive.Operations]

/-- Every actual non-ML corrected Platform callback commutes with a public-key-preserving credential map. No generation/sign law is assumed. -/
theorem non_ml_natural (mapping : Map left right) (sameVerify : left.verify = right.verify)
    (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential left)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (reserveRegistration reservePeer : m Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : RegistrationNativeMldsaGlobalMap.NonML query) :
    Natural (n := n) mapping id
      (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created left credential view failure allocation
        reserveRegistration reservePeer erased helper writer query)
      (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created right
        (RegistrationNativeMldsaMap.credential mapping credential) view failure allocation reserveRegistration reservePeer erased helper writer query) := by
  cases query with
  | inl coin =>
    exact liftNative_natural mapping id coins _ _
      (RegistrationNativeMldsaGlobalMap.non_ml_natural mapping sameVerify setup checks wire route representation created credential (.inl coin) ordinary)
  | inr command => cases command with
    | create _ _ _ | bundle _ | build _ _ => exact ordinary.elim
    | accept packet =>
      apply bind_natural mapping id id _ _ _ _ (parsed_natural mapping)
      intro _parsed
      simp only [sameVerify]
      exact server_natural mapping _
    | finish index packet =>
      exact liftNative_natural mapping id coins _ _
        (RegistrationNativeMldsaGlobalMap.beacon_natural mapping id setup checks representation created _ _
          (finish_natural mapping sameVerify setup wire index packet))
    | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw =>
      exact liftNative_natural mapping id coins _ _
        (RegistrationNativeMldsaGlobalMap.non_ml_natural mapping sameVerify setup checks wire route representation created credential _ ordinary)

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.install_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.install_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.after_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.after_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.finish_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.finish_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.liftNative_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.liftNative_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.non_ml_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap.non_ml_natural
