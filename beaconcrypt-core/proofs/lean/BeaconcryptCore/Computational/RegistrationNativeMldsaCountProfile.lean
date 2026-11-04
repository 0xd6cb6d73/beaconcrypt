-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart

/-! The complete original native capability profile is invariant under normalization of private ML draw receipts when its final event observes the explicitly projected source state. Startup, public adversary input, dynamic owner creation and the original full secrecy ledger remain in the same free program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaCountStart (initialProject)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

private noncomputable def continued (initial : Option (RegistrationNativeExperiment.Initial n KemSK source)) :
    OracleComp (Spec source) (Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))) :=
  match initial with
  | none => pure none
  | some initial => some <$> RegistrationNativeMldsaProfile.run setup checks wire route representation initial.created initial.credential
      bounds mode (adversary initial.public) initial.state

def observed (result : Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))) :=
  result.map RegistrationNativeMldsaCountRun.observed

private theorem continued_normalized (initial : Option (RegistrationNativeExperiment.Initial n KemSK source)) :
    observed <$> transform (continued setup checks wire route representation bounds mode adversary initial) =
      observed <$> continued setup checks wire route representation bounds mode adversary (initial.map initialProject) := by
  cases initial with
  | none => simp only [continued, transform, simulateQ_pure, map_pure, observed, Option.map_none]
  | some initial =>
      have same := congrArg (fun computation => some <$> computation)
        (RegistrationNativeMldsaCountRun.run setup checks wire route representation initial.created initial.credential
          bounds mode (adversary initial.public) initial.state)
      simp only [Functor.map_map] at same
      simp only [continued, Option.map_some,
        initialProject, transform, simulateQ_map, Functor.map_map, observed, Option.map_some]
      exact same

private theorem continued_original (initial : Option (RegistrationNativeExperiment.Initial n KemSK source)) :
    observed <$> continued setup checks wire route representation bounds mode adversary (initial.map initialProject) =
      observed <$> continued setup checks wire route representation bounds mode adversary initial := by
  cases initial with
  | none => rfl
  | some initial =>
      have same := congrArg (fun computation => some <$> computation)
        (RegistrationNativeMldsaCountRun.run_original setup checks wire route representation initial.created initial.credential
          bounds mode (adversary initial.public) initial.state).symm
      simp only [Functor.map_map] at same
      simp only [continued, Option.map_some,
        initialProject, Functor.map_map, observed, Option.map_some]
      exact same

noncomputable def raw (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) :
    OracleComp (Spec source) (Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))) := do
  let initial ← RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId
  continued setup checks wire route representation bounds mode adversary initial

/-- The entire optional native run preserves its exact public outcome, literal ledger/test bit and projected final source state under ML count normalization. -/
theorem normalized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) :
    observed <$> transform (raw (source := source) (n := n) setup checks wire route representation bounds mode adversary
      ensureInit identityIndex serverKeyId) =
      observed <$> raw setup checks wire route representation bounds mode adversary ensureInit identityIndex serverKeyId := by
  simp only [raw, transform, simulateQ_bind, map_bind]
  change (transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
      observed <$> transform (continued setup checks wire route representation bounds mode adversary initial)) = _
  calc
    _ = transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
        observed <$> continued setup checks wire route representation bounds mode adversary (initial.map initialProject) := by
      apply bind_congr
      intro initial
      exact continued_normalized setup checks wire route representation bounds mode adversary initial
    _ = (Option.map initialProject <$> transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)) >>=
        fun initial => observed <$> continued setup checks wire route representation bounds mode adversary initial := by
      rw [bind_map_left]
    _ = (Option.map initialProject <$> RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>=
        fun initial => observed <$> continued setup checks wire route representation bounds mode adversary initial := by
      rw [RegistrationNativeMldsaCountStart.start]
    _ = RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId >>= fun initial =>
        observed <$> continued setup checks wire route representation bounds mode adversary (initial.map initialProject) := by
      rw [bind_map_left]
    _ = _ := by
      apply bind_congr
      intro initial
      exact continued_original setup checks wire route representation bounds mode adversary initial

private def outcome (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (result : Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))) : Bool :=
  result.elim false event

private theorem profile_raw (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    RegistrationNativeMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId
      bounds mode adversary (fun result => event (RegistrationNativeMldsaCountRun.observed result)) =
      outcome event <$> (observed <$> raw setup checks wire route representation bounds mode adversary ensureInit identityIndex serverKeyId) := by
  unfold RegistrationNativeMldsaProfile.profile raw
  simp only [map_bind]
  apply bind_congr
  intro initial
  cases initial with
  | none => simp only [continued, map_pure, outcome, observed, Option.map_none, Option.elim_none]
  | some initial =>
      simp only [continued, Functor.map_map, observed, outcome, Option.map_some, Option.elim_some]

/-- The complete mandatory-ML free profile has unchanged literal behavior when every named primitive draw receipt is normalized, for any explicitly viewed final event. -/
theorem profile (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    transform (RegistrationNativeMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId
      bounds mode adversary (fun result => event (RegistrationNativeMldsaCountRun.observed result))) =
      RegistrationNativeMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId
        bounds mode adversary (fun result => event (RegistrationNativeMldsaCountRun.observed result)) := by
  rw [profile_raw]
  have same := congrArg (fun computation => outcome event <$> computation)
    (normalized setup checks wire route representation bounds mode adversary ensureInit identityIndex serverKeyId)
  simp only [transform, simulateQ_map] at same ⊢
  exact same

end BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile.normalized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile.profile
