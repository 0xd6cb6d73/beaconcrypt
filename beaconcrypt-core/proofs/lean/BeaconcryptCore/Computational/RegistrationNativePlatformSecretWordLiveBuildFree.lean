-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions
/-! The corrected moved-token build demands only the reference already carried by its taken capability. Actual pin, occupancy, allocation, signing and dynamic writer programs retain their complete common state and have no additional material address. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativeSecretWordLiveSessions (Live)
open RegistrationNativePlatformSecretWordBuildControl
variable {J World Encoded A B : Type} {spec : OracleSpec J}
private abbrev M (World : Type) (spec : OracleSpec J) := StateT World (OracleComp spec)
private def Free (predicate : spec.Domain → Prop) [DecidablePred predicate] (work : M World spec A) : Prop :=
  ∀ previous, (work.run previous).IsQueryBoundP predicate 0
private theorem pure_free (predicate : spec.Domain → Prop) [DecidablePred predicate] (value : A) :
    Free (World := World) predicate (pure value) := fun _ => by trivial
private theorem bind_free (predicate : spec.Domain → Prop) [DecidablePred predicate] (work : M World spec A) (next : A → M World spec B)
    (first : Free predicate work) (rest : ∀ value, Free predicate (next value)) : Free predicate (work >>= next) := by
  intro previous
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (n := 0) (m := 0) (first previous) (fun result _ => rest result.1 result.2)

private theorem afterResult_free (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (flags : Message → Bool) (reserve : M World spec Bool) (service : Service (M World spec) Encoded)
    (reserveFree : Free predicate reserve)
    (serviceFree : ∀ control initial reference, flags reference = true → Free predicate (service control initial reference))
    (control : pqxdh.ServerState) (reference : Message) (prepared : flags reference = true)
    (answer : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) (before : ServerState) :
    Free predicate ((afterResult reserve service control reference answer).run before) := by
  cases answer with
  | fail error | div => exact pure_free predicate _
  | ok answer => cases answer with
    | Err previous => exact pure_free predicate _
    | Ok initial =>
      simp only [afterResult, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
      apply bind_free predicate reserve _ reserveFree
      intro allowed
      cases allowed with
      | false => exact pure_free predicate _
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
        exact bind_free predicate _ _ (serviceFree control initial reference prepared) (fun _ => pure_free predicate _)

private theorem afterOccupancy_free (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (flags : Message → Bool) (deriveAd : RegistrationNativePlatformServerMaterialFrontend.AdHash (M World spec))
    (reserve : M World spec Bool) (service : Service (M World spec) Encoded)
    (deriveAdFree : ∀ pending, Free predicate (deriveAd pending)) (reserveFree : Free predicate reserve)
    (serviceFree : ∀ control initial reference, flags reference = true → Free predicate (service control initial reference))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (reference : Message)
    (prepared : flags reference = true) (occupied : Bool) (before : ServerState) :
    Free predicate ((afterOccupancy deriveAd reserve service control lookup reference occupied).run before) := by
  unfold afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_free predicate _
  | ok result => cases result with
    | Err previous => exact pure_free predicate _
    | Ok pending =>
      simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
      apply bind_free predicate _ _ (deriveAdFree pending)
      intro hashed
      exact afterResult_free predicate flags reserve service reserveFree serviceFree control reference prepared _ before

private theorem afterPin_free (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (flags : Message → Bool) (deriveAd : RegistrationNativePlatformServerMaterialFrontend.AdHash (M World spec))
    (reserve : M World spec Bool) (present : U64 → M World spec Bool)
    (service : Service (M World spec) Encoded)
    (deriveAdFree : ∀ pending, Free predicate (deriveAd pending))
    (reserveFree : Free predicate reserve) (presentFree : ∀ keyId, Free predicate (present keyId))
    (serviceFree : ∀ control initial reference, flags reference = true → Free predicate (service control initial reference))
    (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (prepared : flags ready.reference = true)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : ServerState) :
    Free predicate ((afterPin deriveAd reserve present service control ready application current).run before) := by
  cases current with
  | fail error | div => exact pure_free predicate _
  | ok current => cases current with
    | none => exact pure_free predicate _
    | some pin =>
      unfold afterPin
      dsimp only [StateT.run]
      cases peer.begin_completion_lookup control pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div => exact pure_free predicate _
      | ok answer => cases answer with
        | Err previous => exact pure_free predicate _
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div =>
            simp only [requested]
            exact pure_free predicate _
          | ok keyId =>
            simp only [requested]
            split
            · apply bind_free predicate (present keyId) _ (presentFree keyId)
              intro occupied
              exact afterOccupancy_free predicate flags deriveAd reserve service deriveAdFree reserveFree serviceFree
                control lookup ready.reference prepared occupied before
            · exact pure_free predicate _

/-- Arbitrary stateful prefix services and a name-preserving material service give zero unprepared demands after the actual one-use take. -/
theorem control_free (predicate : spec.Domain → Prop) [DecidablePred predicate] (flags : Message → Bool)
    (deriveAd : RegistrationNativePlatformServerMaterialFrontend.AdHash (M World spec))
    (pin : session.ServerAuthenticationPin → M World spec (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : M World spec Bool) (present : U64 → M World spec Bool) (service : Service (M World spec) Encoded)
    (deriveAdFree : ∀ pending, Free predicate (deriveAd pending))
    (pinFree : ∀ current, Free predicate (pin current)) (reserveFree : Free predicate reserve)
    (presentFree : ∀ keyId, Free predicate (present keyId))
    (serviceFree : ∀ control initial reference, flags reference = true → Free predicate (service control initial reference))
    (handle : Nat) (application : Option (Slice U8)) (before : ServerState) (live : Live before flags) :
    Free predicate ((build deriveAd pin reserve present service handle application).run before) := by
  have receipt := RegistrationNativeSecretWordLiveSessions.take_live handle before flags live
  simp only [build, StateT.run]
  rcases taken : RegistrationNativeSecretWordServerMaterial.take handle before with ⟨selected, current⟩
  rw [taken] at receipt
  cases selected with
  | none => exact pure_free predicate _
  | some ready => cases application with
    | none => exact pure_free predicate _
    | some application =>
      simp only [complete, StateT.run]
      apply bind_free predicate (pin current.pin) _ (pinFree current.pin)
      intro currentPin
      exact afterPin_free predicate flags deriveAd reserve present service deriveAdFree reserveFree presentFree serviceFree current.control
        ready application (receipt.2 ready rfl) currentPin current

section Actual
variable {n : Nat} {Platform KemSK E : Type}

def Bad (flags : Message → Bool) : (RegistrationNativePlatformSecretWordBuild.Spec n).Domain → Prop
  | .inl reference => flags reference = false
  | .inr _ => False
instance (flags : Message → Bool) : DecidablePred (Bad (n := n) flags) := fun query => by
  cases query <;> dsimp only [Bad] <;> infer_instance

private theorem effects_free (flags : Message → Bool)
    (work : StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform)
      (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A) :
    Free (Bad (n := n) flags) (RegistrationNativePlatformSecretWordBuild.liftEffects work) := by
  intro previous
  change (simulateQ RegistrationNativePlatformSecretWordBuild.embed (work.run previous)).IsQueryBoundP (Bad flags) 0
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativePlatformSecretWordBuild.embed, Bad, isQueryBoundP_query_iff]

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)

private theorem service_free (flags : Message → Bool) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : Message) (prepared : flags reference = true) :
    Free (Bad (n := n) flags)
      (RegistrationNativePlatformSecretWordBuild.service source view failure allocation erased helper sign writer control initial reference) := by
  intro previous
  simp only [RegistrationNativePlatformSecretWordBuild.service, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · simp [isQueryBoundP_query_iff, Bad, prepared]
  · intro selected _possible
    cases selected with
    | none => trivial
    | some choice => exact effects_free flags _ previous

/-- The literal corrected dynamic build demands only its already prepared moved reference. -/
theorem body_free (flags : Message → Bool) (handle : Nat) (application : Option (Slice U8))
    (before : ServerState) (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform)
    (live : Live before flags) :
    (((RegistrationNativePlatformSecretWordBuild.body (n := n) source view failure allocation erased helper sign writer reserve
      handle application).run before).run previous).IsQueryBoundP (Bad flags) 0 := by
  exact control_free (Bad flags) flags _ _ _ _ _
    (fun _ => effects_free flags _) (fun _ => effects_free flags _) (effects_free flags _) (fun _ => effects_free flags _)
    (fun control initial reference prepared => service_free source view failure allocation erased helper sign writer flags
      control initial reference prepared) handle application before live previous
end Actual

/-- Local routing retains the exact descriptor tested by the preparation flag. -/
theorem embedded_free {n : Nat} {KemSK Value : Type} (flags : Message → Bool)
    (work : OracleComp (RegistrationNativePlatformSecretWordBuild.Spec n) Value)
    (bounded : work.IsQueryBoundP (Bad flags) 0) :
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ
      RegistrationNativePlatformSecretWordBuild.wordEmbedding (KemSK := KemSK)) work).IsQueryBoundP
        (RegistrationNativeSecretWordLiveCaps.Bad (KemSK := KemSK) flags) 0 := by
  rw [QueryImpl.simulateQ_compose]
  apply RegistrationNativeSecretWordLiveCaps.local_bound flags false
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ 0 bounded
  intro query
  rcases query with reference | effect | coin
  all_goals simp [RegistrationNativePlatformSecretWordBuild.wordEmbedding,
    RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.effect,
    RegistrationNativeSecretWordLiveCaps.BadLocal, Bad, isQueryBoundP_query_iff]
  intro unprepared
  simp only [unprepared, ite_true]
  decide

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree.control_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree.control_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree.body_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree.body_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree.embedded_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree.embedded_free
