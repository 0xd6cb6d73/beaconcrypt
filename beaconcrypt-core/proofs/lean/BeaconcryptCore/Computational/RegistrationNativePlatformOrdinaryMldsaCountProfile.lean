-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart

/-! Actual corrected initialization and every adaptive continuation preserve the whole optional ledger/native/platform outcome under named ML accounting normalization. The view erases only explicit private counters, retaining the actual public platform state and every protocol field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaCountStart (initialProject)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

private noncomputable def continued (initial : Option (RegistrationNativeExperiment.Initial n KemSK source)) :
    M source Platform (Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source)) :=
  match initial with
  | none => pure none
  | some initial => some <$> RegistrationNativePlatformOrdinaryMldsaProfile.run setup checks wire route representation initial.created initial.credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state

def observed
    (result : Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source) × Platform) :=
  (result.1.map (Prod.map id RegistrationNativeMldsaMainView.project), result.2)

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

private theorem continued_normalized (initial : Option (RegistrationNativeExperiment.Initial n KemSK source)) (previous : Platform) :
    observed <$> transform ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial).run previous) =
      observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (initial.map initialProject)).run previous) := by
  cases initial with
  | none => simp only [continued, StateT.run_pure, transform, simulateQ_pure, map_pure, observed, Option.map_none]
  | some initial =>
    have same := congrArg (fun action => Prod.map some id <$> action)
      (RegistrationNativePlatformOrdinaryMldsaCountRun.run setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state previous)
    simp only [continued, StateT.run_map, Functor.map_map, Option.map_some, initialProject,
      transform, simulateQ_map, observed, Prod.map, RegistrationNativePlatformOrdinaryMldsaCountRun.observed, id_eq] at same ⊢
    exact same

private theorem continued_original (initial : Option (RegistrationNativeExperiment.Initial n KemSK source)) (previous : Platform) :
    observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (initial.map initialProject)).run previous) =
      observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial).run previous) := by
  cases initial with
  | none => rfl
  | some initial =>
    have same := congrArg (fun action => Prod.map some id <$> action)
      (RegistrationNativePlatformOrdinaryMldsaCountRun.run_original setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state previous).symm
    simp only [continued, StateT.run_map, Functor.map_map, Option.map_some, initialProject,
      observed, Prod.map, RegistrationNativePlatformOrdinaryMldsaCountRun.observed, id_eq] at same ⊢
    exact same

noncomputable def raw (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    M source Platform (Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source)) := do
  let initial ← StateT.lift (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)
  continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial

/-- Whole corrected optional execution preserves every literal ledger/native/platform outcome under named ML count normalization. -/
theorem normalized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (previous : Platform) :
    observed <$> transform ((raw (source := source) (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased
      helper writer bounds mode adversary ensureInit identityIndex serverKeyId).run previous) =
      observed <$> ((raw setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        ensureInit identityIndex serverKeyId).run previous) := by
  simp only [raw, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, transform, simulateQ_bind, map_bind]
  change (transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
    observed <$> transform ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial).run previous)) = _
  calc
    _ = transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
        observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
          (initial.map initialProject)).run previous) := by
      apply bind_congr
      intro initial
      exact continued_normalized setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial previous
    _ = (Option.map initialProject <$> transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)) >>= fun initial =>
        observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial).run previous) := by
      rw [bind_map_left]
    _ = (Option.map initialProject <$> RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
        observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial).run previous) := by
      rw [RegistrationNativeMldsaCountStart.start]
    _ = RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId >>= fun initial =>
        observed <$> ((continued setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
          (initial.map initialProject)).run previous) := by
      rw [bind_map_left]
    _ = _ := by
      apply bind_congr
      intro initial
      exact continued_original setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary initial previous

private def outcome (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (result : Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source) × Platform) : Bool × Platform :=
  (result.1.elim false (fun selected => event (selected.1.1, (selected.1.2, selected.2))), result.2)

private theorem profile_raw (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) (previous : Platform) :
    ((RegistrationNativePlatformOrdinaryMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => event (result.1, (result.2.1, RegistrationNativeMldsaMainView.project result.2.2)))).run previous) =
      outcome event <$> (observed <$> ((raw setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        bounds mode adversary ensureInit identityIndex serverKeyId).run previous)) := by
  unfold RegistrationNativePlatformOrdinaryMldsaProfile.profile raw
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
  apply bind_congr
  intro initial
  cases initial with
  | none => simp only [continued, StateT.run_pure, map_pure, observed, Option.map_none, outcome, Option.elim_none]
  | some initial =>
    simp only [continued, StateT.run_map, Functor.map_map, observed, outcome, Prod.map,
      Option.map_some, Option.elim_some, id_eq]

/-- The complete corrected initialized free profile is unchanged under ML count normalization for every viewed final event and exact platform poststate. -/
theorem profile (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) (previous : Platform) :
    transform ((RegistrationNativePlatformOrdinaryMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => event (result.1, (result.2.1, RegistrationNativeMldsaMainView.project result.2.2)))).run previous) =
      ((RegistrationNativePlatformOrdinaryMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (fun result => event (result.1, (result.2.1, RegistrationNativeMldsaMainView.project result.2.2)))).run previous) := by
  rw [profile_raw]
  have same := congrArg (fun action => outcome event <$> action)
    (normalized setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      ensureInit identityIndex serverKeyId previous)
  simpa only [transform, simulateQ_map, Functor.map_map] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountProfile.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountProfile.normalized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountProfile.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountProfile.profile
