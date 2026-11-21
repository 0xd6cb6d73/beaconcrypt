-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity
import BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage

/-! The unchanged broad native LR events split once at the actual changed-prekey event. Canonical good-target shares are disjoint in the same real experiment, retain the literal test bit and are bounded by their respective broad event masses. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorCoverage
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def broad (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (winning : Bool) (result : Value × RegistrationNativeLedger.State) : Bool :=
  if winning then RegistrationNativeLorEvents.w crypto wire serverKeyId budget filter guess result
    else RegistrationNativeLorEvents.j crypto wire serverKeyId budget filter result

noncomputable def select (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (winning : Bool) (result : Value × RegistrationNativeLedger.State) : Option (Fin budget.accept × Fin budget.capacity) :=
  (RegistrationNativeLorCanonical.choose crypto wire serverKeyId budget result.2).bind fun target =>
    if RegistrationNativeLorRecordSecurity.observer crypto wire serverKeyId budget filter guess target winning result then some target else none

theorem selected_iff (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (winning : Bool) (result : Value × RegistrationNativeLedger.State) (consistent : RegistrationNativeLedger.Consistent result.2)
    (target : Fin budget.accept × Fin budget.capacity) :
    select crypto wire serverKeyId budget filter guess winning result = some target ↔
      RegistrationNativeLorRecordSecurity.observer crypto wire serverKeyId budget filter guess target winning result = true := by
  constructor
  · intro selected
    unfold select at selected
    cases chosen : RegistrationNativeLorCanonical.choose crypto wire serverKeyId budget result.2 with
    | none => simp only [chosen, Option.bind_none, reduceCtorEq] at selected
    | some actual =>
        simp only [chosen, Option.bind_some] at selected
        split at selected
        next observed => cases Option.some.inj selected; exact observed
        next => cases selected
  · intro observed
    have good := RegistrationNativeLorRecordSecurity.observer_good crypto wire serverKeyId budget filter guess target winning result observed
    have chosen := RegistrationNativeLorCanonical.eligible_choose crypto wire serverKeyId budget filter target result consistent good.1
    simp only [select, chosen, Option.bind_some, observed, ite_true]

theorem share_broad (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (winning : Bool) (result : Value × RegistrationNativeLedger.State) (target : Fin budget.accept × Fin budget.capacity)
    (observed : RegistrationNativeLorRecordSecurity.observer crypto wire serverKeyId budget filter guess target winning result = true) :
    broad crypto wire serverKeyId budget filter guess winning result = true := by
  classical
  have good := RegistrationNativeLorRecordSecurity.observer_good crypto wire serverKeyId budget filter guess target winning result observed
  obtain ⟨session, raw, eligible, _scanned⟩ := good.1
  cases winning with
  | false => exact decide_eq_true ⟨(session, target.2), eligible⟩
  | true =>
      have bit : result.2.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess result.1) := by
        simp only [RegistrationNativeLorRecordSecurity.observer, ite_true,
          RegistrationNativeLorCanonical.w, Bool.and_eq_true, decide_eq_true_eq] at observed
        exact observed.1.2
      exact decide_eq_true ⟨(session, target.2), eligible, bit⟩

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)

/-- The original generated startup and full native compiler preserve the exact ledger transcript. -/
theorem outcome_consistent
    (observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : some observed ∈ support (RegistrationNativeStartupTargets.outcome setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary)) :
    RegistrationNativeLedger.Consistent observed.2.1 := by
  simp only [RegistrationNativeStartupTargets.outcome, mem_support_bind_iff] at supported
  obtain ⟨initialized, _started, continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [support_map, Set.mem_image, Option.some.injEq] at continued
      obtain ⟨actual, reached, rfl⟩ := continued
      exact RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire _ bounds
        (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        .P (adversary initial.public) initial.state actual reached

/-- No extra event assumption is needed to derive private test existence on real startup support. -/
theorem outcome_observer (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool)
    (observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : some observed ∈ support (RegistrationNativeStartupTargets.outcome setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary)) :
    RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target winning (observed.1, observed.2.1) =
      if winning then RegistrationNativeLorCanonical.w setup.source.crypto wire serverKeyId budget filter guess target (observed.1, observed.2.1)
      else RegistrationNativeLorCanonical.j setup.source.crypto wire serverKeyId budget filter target (observed.1, observed.2.1) := by
  simp only [RegistrationNativeStartupTargets.outcome, mem_support_bind_iff] at supported
  obtain ⟨initialized, started, continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [support_map, Set.mem_image, Option.some.injEq] at continued
      obtain ⟨actual, reached, rfl⟩ := continued
      have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
      rw [← sender]
      exact RegistrationNativeLorRecordSecurity.observer_run setup.source.crypto wire _ bounds
        (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        .P (adversary initial.public) initial.state actual reached budget filter guess target winning

theorem outcome_split (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (winning : Bool) (observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : some observed ∈ support (RegistrationNativeStartupTargets.outcome setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary))
    (hit : broad setup.source.crypto wire serverKeyId budget filter guess winning (observed.1, observed.2.1) = true) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire observed.2.1.transcript observed.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target winning (observed.1, observed.2.1) = true := by
  classical
  have eligibility : RegistrationNativeLorEvents.j setup.source.crypto wire serverKeyId budget filter (observed.1, observed.2.1) = true := by
    cases winning with
    | false => exact hit
    | true =>
        have both : RegistrationNativeLorEvents.j setup.source.crypto wire serverKeyId budget filter (observed.1, observed.2.1) = true ∧
            decide (observed.2.1.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess observed.1)) = true := by
          simpa only [broad, Bool.true_eq, ite_true, RegistrationNativeLorEvents.w_eq, Bool.and_eq_true] using hit
        exact both.1
  simp only [RegistrationNativeStartupTargets.outcome, mem_support_bind_iff] at supported
  obtain ⟨initialized, started, continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [support_map, Set.mem_image, Option.some.injEq] at continued
      obtain ⟨actual, reached, rfl⟩ := continued
      have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
      rw [← sender] at eligibility hit ⊢
      rcases RegistrationNativeLorCanonical.real_eligible_split setup checks wire route representation initial.created initial.credential readback shortRejects
        bounds .P (adversary initial.public) budget (bounded initial.public) filter initial.state actual reached eligibility with changed | chosen
      · exact Or.inl changed
      · right
        obtain ⟨target, good⟩ := chosen
        refine ⟨target, ?_⟩
        rw [RegistrationNativeLorRecordSecurity.observer_run setup.source.crypto wire _ bounds
          (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          .P (adversary initial.public) initial.state actual reached budget filter guess target winning]
        cases winning with
        | false => exact decide_eq_true good
        | true =>
            have both : RegistrationNativeLorEvents.j setup.source.crypto wire initial.created.server.server.metadata.sender budget filter (actual.1, actual.2.1) = true ∧
                decide (actual.2.1.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess actual.1)) = true := by
              simpa only [broad, Bool.true_eq, ite_true, RegistrationNativeLorEvents.w_eq, Bool.and_eq_true] using hit
            simpa only [Bool.true_eq, ite_true, RegistrationNativeLorCanonical.w, RegistrationNativeLorCanonical.j,
              Bool.and_eq_true, decide_eq_true_eq] using And.intro good (of_decide_eq_true both.2)

set_option maxHeartbeats 1200000 in
/-- All canonical target masses live in one unchanged real native experiment. -/
theorem share_mass (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool) (winning : Bool) :
    (∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let observed ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
        (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target winning (actual.1, actual.2.1)))}[observed = true]) ≤
    Pr{let observed ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (fun actual => broad setup.source.crypto wire serverKeyId budget filter guess winning (actual.1, actual.2.1)))}[observed = true] := by
  classical
  let chosen := fun outcome : Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) =>
    outcome.bind fun actual => select setup.source.crypto wire serverKeyId budget filter guess winning (actual.1, actual.2.1)
  simp only [RegistrationNativeStartupTargets.profile_outcome, prEvent_map]
  calc
    _ = ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let outcome ← RegistrationNativeStartupTargets.outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary}[chosen outcome = some target] := by
      apply Finset.sum_congr rfl
      intro target _member
      apply prEvent_congr_of_support
      intro outcome supported
      cases outcome with
      | none => simp only [Option.elim_none, chosen, Option.bind_none, reduceCtorEq, Bool.false_eq_true]
      | some actual =>
          exact (selected_iff setup.source.crypto wire serverKeyId budget filter guess winning _
            (outcome_consistent setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary actual supported) target).symm
    _ = Pr{let outcome ← RegistrationNativeStartupTargets.outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary}[(chosen outcome).isSome] :=
      (prEvent_isSome_eq_sum _ chosen).symm
    _ ≤ _ := by
      apply prEvent_mono_of_support
      intro outcome supported selected
      cases outcome with
      | none => cases selected
      | some actual =>
          obtain ⟨target, picked⟩ := Option.isSome_iff_exists.mp selected
          have observed := (selected_iff setup.source.crypto wire serverKeyId budget filter guess winning _
            (outcome_consistent setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary actual supported) target).mp picked
          exact share_broad setup.source.crypto wire serverKeyId budget filter guess winning _ target observed

set_option maxHeartbeats 1200000 in
/-- Both broad observers pay the same single actual origin event. -/
theorem broad_probability (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (winning : Bool) :
    Pr{let observed ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (fun actual => broad setup.source.crypto wire serverKeyId budget filter guess winning (actual.1, actual.2.1)))}[observed = true] ≤
    Pr{let changed ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeIdentityOriginEvents.event setup.joint wire))}[changed = true] +
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let observed ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
        (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target winning (actual.1, actual.2.1)))}[observed = true] := by
  classical
  simp only [RegistrationNativeStartupTargets.profile_outcome, prEvent_map]
  calc
    _ ≤ Pr{let outcome ← RegistrationNativeStartupTargets.outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary}[
        outcome.elim false (RegistrationNativeIdentityOriginEvents.event setup.joint wire) = true ∨
        ∃ target : Fin budget.accept × Fin budget.capacity,
          outcome.elim false (fun actual => RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target winning (actual.1, actual.2.1)) = true] := by
      apply prEvent_mono_of_support
      intro outcome supported observed
      cases outcome with
      | none => cases observed
      | some actual =>
          rcases outcome_split setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary budget filter guess bounded readback shortRejects
            winning actual supported observed with changed | chosen
          · exact Or.inl (decide_eq_true changed)
          · exact Or.inr chosen
    _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_le _ _))

end BeaconcryptCore.Computational.RegistrationNativeLorCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.selected_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.selected_iff

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.share_broad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.share_broad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.outcome_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.outcome_consistent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.outcome_observer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.outcome_observer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.outcome_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.share_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.share_mass

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCoverage.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCoverage.broad_probability
