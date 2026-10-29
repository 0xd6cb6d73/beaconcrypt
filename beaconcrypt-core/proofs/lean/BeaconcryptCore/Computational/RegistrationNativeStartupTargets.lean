-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup

/-! Actual generated native startup retains the broad original CE APP event and has one canonical parsed-accept by owner target product. Startup failures contribute no success. The successful session remains existential and adds no independent guessing factor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStartupTargets
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open RegistrationNativeEvents (Observed CEAppWin)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def outcome (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) :
    ProbComp (Option (Observed Value (RegistrationNativeExperiment.State n KemSK source))) := do
  let initialized ← RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure none
  | some initial => some <$> (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential
      bounds .P (adversary initial.public) initial.state)

/-- The optional complete native outcome has exactly the original generated-startup event probability. -/
theorem profile_outcome (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (event : Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary event =
      (fun observed => observed.elim false event) <$> outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary := by
  simp only [RegistrationNativeExperiment.profile, outcome, map_bind]
  apply bind_congr
  intro initialized
  cases initialized <;> simp only [map_pure, Functor.map_map, Option.elim_none, Option.elim_some]

/-- Every successful actual whole-startup APP execution belongs to the original canonical target product. -/
theorem outcome_selected (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (budget : Budget)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : some observed ∈ support (outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary))
    (winning : CEAppWin setup.source.crypto wire serverKeyId budget claim observed) :
    ∃ target : Fin budget.accept × Fin budget.capacity,
      RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire serverKeyId budget target claim observed := by
  simp only [outcome, mem_support_bind_iff] at supported
  obtain ⟨initialized, started, continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [support_map, Set.mem_image, Option.some.injEq] at continued
      obtain ⟨actual, reached, rfl⟩ := continued
      have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
      rw [← sender] at winning ⊢
      exact (RegistrationNativeParsedTargetCanonical.broad_selected setup.source.crypto wire _ bounds
        (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        .P (adversary initial.public) budget (bounded initial.public) initial.state claim actual reached).mp winning

/-- The original whole native APP probability pays exactly one canonical parsed-accept by owner sum, including actual generated startup and all native failure paths. -/
theorem broad_probability (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (budget : Budget)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds .P adversary (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
          bounds .P adversary (RegistrationNativeParsedTargetCanonical.event setup.source.crypto wire serverKeyId budget target claim))}[won = true] := by
  classical
  simp only [profile_outcome, prEvent_map]
  calc
    _ ≤ Pr{let observed ← outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary}[
      ∃ target ∈ (Finset.univ : Finset (Fin budget.accept × Fin budget.capacity)),
        observed.elim false (RegistrationNativeParsedTargetCanonical.event setup.source.crypto wire serverKeyId budget target claim) = true] := by
      apply prEvent_mono_of_support
      intro observed supported winning
      cases observed with
      | none => cases winning
      | some actual =>
          have original : CEAppWin setup.source.crypto wire serverKeyId budget claim actual := by
            simpa only [Option.elim_some, RegistrationNativeEvents.ceAppEvent, decide_eq_true_eq] using winning
          obtain ⟨target, selected⟩ := outcome_selected setup checks wire route representation source ensureInit identityIndex serverKeyId
            bounds budget adversary bounded claim actual supported original
          refine ⟨target, Finset.mem_univ target, ?_⟩
          simpa only [Option.elim_some, RegistrationNativeParsedTargetCanonical.event, decide_eq_true_eq] using selected
    _ ≤ _ := prEvent_exists_finset_le Finset.univ _ _

end BeaconcryptCore.Computational.RegistrationNativeStartupTargets
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupTargets.profile_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupTargets.profile_outcome
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupTargets.outcome_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupTargets.outcome_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupTargets.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupTargets.broad_probability
