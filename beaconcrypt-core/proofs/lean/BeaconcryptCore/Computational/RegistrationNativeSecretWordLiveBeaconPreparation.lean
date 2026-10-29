-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerRun

/-! Actual response authentication and ordered Beacon collection return a Ready only after the precise successful checked preparation. The proof retains terminal abort before parsing and the actual supplied reference used by ordinary owners. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconPreparation
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordLiveServerRun (lower Auxiliary)
open RegistrationNativeSecretWordBeaconCompiler (agreement collect finishPreparation)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
  (RegistrationNativeSecretWordInterpreter.M n KemSK))

private theorem lower_bind {Next : Type}
    (first : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (next : Value → StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Next)
    (before : Auxiliary n KemSK) :
    (lower implementation (first >>= next)).run before = (do
      let reached ← (lower implementation first).run before
      (lower implementation (next reached.1)).run reached.2) := by
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, bind_map_left, map_bind]

private theorem agreement_run (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : Auxiliary n KemSK) :
    (lower implementation (agreement setup owner oneTime authenticated)).run before = (do
      let collected ← (lower implementation (collect setup owner oneTime authenticated)).run before
      match collected.1 with
      | none => pure (.ok none, collected.2)
      | some pending =>
          (fun result => (result.1, (collected.2.1, result.2))) <$>
            (simulateQ implementation (simulateQ RegistrationNativeSecretWordInterface.prepare
              (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run collected.2.2) := by
  simp only [agreement, lower_bind]
  apply bind_congr
  rintro ⟨collected, env, context⟩
  cases collected <;>
    simp only [lower, StateT.run, state_pure_apply, state_lift_apply, state_map_apply, simulateQ_pure, simulateQ_map,
      map_pure, Functor.map_map, Prod.map_def, id_eq]

private theorem agreement_ready (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (rootReceipt : ∀ authenticated pending ready before after,
      (.ok (some ready), after) ∈ support
        ((simulateQ implementation (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before) → after.flags ready.reference = true)
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (ready : BeaconReady)
    (before after : Auxiliary n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((lower implementation (agreement setup owner oneTime authenticated)).run before)) :
    after.2.flags ready.reference = true := by
  rw [agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases formed : collected.1 with
  | none => simp only [formed, mem_support_pure_iff] at supported; cases supported
  | some pending =>
      simp only [formed, support_map] at supported
      obtain ⟨reached, possible, equal⟩ := supported
      have sameValue := congrArg Prod.fst equal
      have sameState := congrArg (fun result => result.2.2) equal
      have pairEqual : reached = (.ok (some ready), after.2) := Prod.ext sameValue sameState
      rw [pairEqual] at possible
      exact rootReceipt authenticated pending ready collected.2.2 after.2 possible

attribute [local irreducible] RegistrationResponseExecutor.begin

private theorem finish_ready (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (rootReceipt : ∀ authenticated pending ready before after,
      (.ok (some ready), after) ∈ support
        ((simulateQ implementation (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before) → after.flags ready.reference = true)
    (packet : Option registration.ResponsePacket) (owner afterOwner : SelectedOwner source)
    (ready : BeaconReady) (before after : Auxiliary n KemSK)
    (supported : ((.ok (some ready), afterOwner), after) ∈ support
      ((lower implementation ((finishPreparation setup source packet).run owner)).run before)) :
    after.2.flags ready.reference = true := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, lower, StateT.run] at supported
      cases supported
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, lower, StateT.run] at supported
          cases supported
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc,
            lower_bind, mem_support_bind_iff] at supported
          obtain ⟨accepted, _checked, supported⟩ := supported
          cases checked : accepted.1 with
          | fail error | div =>
              simp only [checked, lower, StateT.run] at supported
              cases supported
          | ok reply => cases reply with
            | Err error =>
                simp only [checked, lower, StateT.run] at supported
                cases supported
            | Ok authenticated =>
                simp only [checked, lower, StateT.run, state_lift_apply, state_map_apply, simulateQ_map,
                  Functor.map_map, support_map] at supported
                obtain ⟨reached, possible, equal⟩ := supported
                apply agreement_ready implementation setup rootReceipt owner oneTime authenticated ready accepted.2 after
                simp only [lower, StateT.run, support_map]
                refine ⟨reached, possible, ?_⟩
                exact Prod.ext (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)

def routing (setup : Setup base KemSK) (ownScalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
      (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  match ownScalar with
  | none => RegistrationNativeSecretWordInterface.liftLocal false
  | some scalar => RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup scalar

private theorem root_ready (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (handlerChecked setup wire route sign input inside provider ∘ₛ routing setup ownScalar)
        (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before)) :
    after.flags ready.reference = true := by
  rw [← QueryImpl.simulateQ_compose] at supported
  cases ownScalar with
  | none =>
      have same : (handlerChecked setup wire route sign input inside provider ∘ₛ routing setup none) ∘ₛ
          RegistrationNativeSecretWordInterface.prepare =
          RegistrationNativeSecretWordLiveRoot.preparation (n := n) setup wire route sign input inside provider := by
        funext message
        simp only [QueryImpl.compose, routing, RegistrationNativeSecretWordInterface.prepare,
          simulateQ_spec_query, RegistrationNativeSecretWordInterface.liftLocal,
          RegistrationNativeSecretWordLiveRoot.preparation]
      rw [same] at supported
      exact RegistrationNativeSecretWordLiveRoot.beacon setup wire route sign input inside provider authenticated pending ready before after supported
  | some scalar =>
      have same : (handlerChecked setup wire route sign input inside provider ∘ₛ routing setup (some scalar)) ∘ₛ
          RegistrationNativeSecretWordInterface.prepare =
          RegistrationNativeSecretWordLiveRoot.ordinaryPreparation (n := n) setup scalar wire route sign input inside provider := by
        funext message
        simp only [QueryImpl.compose, routing, RegistrationNativeSecretWordInterface.prepare,
          simulateQ_spec_query, RegistrationNativeSecretWordOwners.ordinary,
          RegistrationNativeSecretWordLiveRoot.ordinaryPreparation]
        split <;> simp_all only [simulateQ_pure, simulateQ_spec_query,
          RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordLiveRoot.preparation]
      rw [same] at supported
      exact RegistrationNativeSecretWordLiveRoot.ordinary_beacon setup scalar wire route sign input inside provider authenticated pending ready before after supported

/-- Actual selected and ordinary finish preparation establishes the precise live returned descriptor after authentication and collection, retaining every reached owner, environment and private state. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner afterOwner : SelectedOwner source)
    (ready : BeaconReady) (env afterEnv : RegistrationServerReferenceCompiler.Environment)
    (before after : State n KemSK)
    (supported : (((.ok (some ready), afterOwner), afterEnv), after) ∈ support
      ((simulateQ (handlerChecked setup wire route sign input inside provider)
        (simulateQ (routing setup ownScalar)
          (((finishPreparation (n := n) setup source packet).run owner).run env))).run before)) :
    after.flags ready.reference = true := by
  apply finish_ready (handlerChecked setup wire route sign input inside provider ∘ₛ routing setup ownScalar)
    setup source (root_ready setup wire route sign input inside provider ownScalar) packet owner afterOwner ready
    (env, before) (afterEnv, after)
  simp only [lower, StateT.run, QueryImpl.simulateQ_compose, support_map]
  exact Set.mem_image_of_mem _ supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconPreparation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconPreparation.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconPreparation.finish
