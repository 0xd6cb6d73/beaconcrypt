-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt
import BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
import BeaconcryptCore.Computational.RegistrationNativePrekeyProbability

/-! The functional public claim selector covers the original broad native APP event on actual bounded executions. A selected good event retains the same public prekey conjunct used by the existing native proof. No unchanged-bundle restriction, private-message selector or security-conclusion premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage
open PqxdhDeploymentInterface (Budget FreshBounds Mode Handle)
open RegistrationNativeLedgerHiding (view)
open RegistrationNativeCanonicalSelector (chooseLedger selected)
open RegistrationNativePublicObservation (firstAccept)
variable {Value NativeState : Type}

theorem choose_at (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (value : Value) (ledger : RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent ledger)
    (index : Nat) (guess : Pqxdh.Bytes) (entry : PqxdhDeploymentSecrecy.FreshEntry)
    (session : Fin budget.accept) (target : Fin budget.accept × Fin budget.capacity) (raw : Pqxdh.Bytes)
    (claimed : claim value = some (index, guess)) (fresh : ledger.ledger.fresh[index]? = some entry)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget ledger.ledger.transcript entry.handle = some (session, target.2))
    (found : firstAccept wire session.val (ledger.transcript.map view) = some (target.1.val, raw)) :
    chooseLedger crypto wire serverKeyId budget ((claim value).map Prod.fst) ledger = some target := by
  rw [RegistrationNativeCanonicalSelector.choose_literal crypto wire serverKeyId budget _ ledger consistent]
  simp only [claimed, Option.map_some, Option.bind_eq_bind, Option.bind_some, fresh, designated, found,
    dite_eq_left target.1.isLt]

theorem broad_choose
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (winning : RegistrationNativeEvents.CEAppWin crypto wire serverKeyId budget claim observed) :
    ∃ target : Fin budget.accept × Fin budget.capacity,
      RegistrationNativeParsedTargetCanonical.CEAppAt crypto wire serverKeyId budget target claim observed ∧
      chooseLedger crypto wire serverKeyId budget ((claim observed.1).map Prod.fst) observed.2.1 = some target := by
  obtain ⟨target, raw, canonical, index, guess, entry, session, claimed, fresh, designated, found⟩ :=
    RegistrationNativeCanonicalReceipt.broad_selected crypto wire serverKeyId bounds typed mode work budget bounded before claim observed supported winning
  exact ⟨target, canonical, choose_at crypto wire serverKeyId budget claim observed.1 observed.2.1
    (RegistrationNativeFullCompiler.ledger_projection crypto wire serverKeyId bounds typed mode work before observed supported)
    index guess entry session target raw claimed fresh designated found⟩

/-- An original APP win and the functional public selection pick the same existing canonical target. -/
theorem selected_at
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (target : Fin budget.accept × Fin budget.capacity)
    (winning : RegistrationNativeEvents.CEAppWin crypto wire serverKeyId budget claim observed)
    (chosen : selected crypto wire serverKeyId budget claim target observed.1 observed.2.1 = true) :
    RegistrationNativeParsedTargetCanonical.CEAppAt crypto wire serverKeyId budget target claim observed := by
  obtain ⟨actual, canonical, selectedActual⟩ := broad_choose crypto wire serverKeyId bounds typed mode work budget bounded before claim observed supported winning
  exact (Option.some.inj (selectedActual.symm.trans (of_decide_eq_true chosen))) ▸ canonical

theorem canonical_good (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (canonical : RegistrationNativeParsedTargetCanonical.CEAppAt crypto wire serverKeyId budget target claim observed)
    (good : RegistrationNativePrekeyEvents.GoodApp crypto wire serverKeyId budget claim observed) :
    RegistrationNativePrekeyEvents.GoodAt crypto wire serverKeyId budget target claim observed := by
  rcases canonical with ⟨index, guess, entry, session, claimed, fresh, designated, receipt, guessed⟩
  rcases good with ⟨otherIndex, _otherGuess, otherEntry, otherClaim, otherFresh, _eligible, _guessed, pinned⟩
  obtain rfl : otherIndex = index := congrArg Prod.fst (Option.some.inj (otherClaim.symm.trans claimed))
  exact ⟨otherIndex, guess, entry, session, claimed, fresh, designated, receipt, guessed,
    (Option.some.inj (otherFresh.symm.trans fresh)) ▸ pinned⟩

def GoodSelectedAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Fin budget.accept × Fin budget.capacity)
    (observed : RegistrationNativeEvents.Observed Value NativeState) : Prop :=
  RegistrationNativePrekeyEvents.GoodAt crypto wire serverKeyId budget target claim observed ∧
    selected crypto wire serverKeyId budget claim target observed.1 observed.2.1 = true

open Classical in
noncomputable def event (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Fin budget.accept × Fin budget.capacity)
    (observed : RegistrationNativeEvents.Observed Value NativeState) : Bool :=
  decide (GoodSelectedAt crypto wire serverKeyId budget claim target observed)

noncomputable def decision (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) : Bool :=
  event crypto wire serverKeyId budget claim target (result.1, (result.2, ()))

theorem event_erase (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Fin budget.accept × Fin budget.capacity)
    (observed : RegistrationNativeEvents.Observed Value NativeState) :
    event crypto wire serverKeyId budget claim target observed =
      decision crypto wire serverKeyId budget claim target (observed.1, observed.2.1) := by
  rfl

theorem good_selected
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (good : RegistrationNativePrekeyEvents.GoodApp crypto wire serverKeyId budget claim observed) :
    ∃ target : Fin budget.accept × Fin budget.capacity, GoodSelectedAt crypto wire serverKeyId budget claim target observed := by
  obtain ⟨target, canonical, chosen⟩ := broad_choose crypto wire serverKeyId bounds typed mode work budget bounded before claim observed supported
    (RegistrationNativePrekeyEvents.good_broad crypto wire serverKeyId budget claim observed good)
  exact ⟨target, canonical_good crypto wire serverKeyId budget target claim observed canonical good, decide_eq_true chosen⟩

theorem good_selected_unique (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (first second : Fin budget.accept × Fin budget.capacity) (observed : RegistrationNativeEvents.Observed Value NativeState)
    (firstChosen : GoodSelectedAt crypto wire serverKeyId budget claim first observed)
    (secondChosen : GoodSelectedAt crypto wire serverKeyId budget claim second observed) : first = second := by
  exact RegistrationNativeCanonicalSelector.selected_unique crypto wire serverKeyId budget claim first second observed.1 observed.2.1
    firstChosen.2 secondChosen.2

/-- The selector masses are disjoint in one and the same experiment. -/
theorem selected_mass (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (work : ProbComp (RegistrationNativeEvents.Observed Value NativeState)) :
    (∑ target : Fin budget.accept × Fin budget.capacity, Pr{let observed ← work}[
      selected crypto wire serverKeyId budget claim target observed.1 observed.2.1 = true]) ≤ 1 := by
  simpa only [selected, decide_eq_true_iff] using sum_prEvent_eq_some_le_one work
    (fun observed => chooseLedger crypto wire serverKeyId budget ((claim observed.1).map Prod.fst) observed.2.1)

theorem good_probability
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    Pr{let observed ← RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
      RegistrationNativePrekeyEvents.GoodApp crypto wire serverKeyId budget claim observed] ≤
    ∑ target : Fin budget.accept × Fin budget.capacity,
      Pr{let observed ← RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
        GoodSelectedAt crypto wire serverKeyId budget claim target observed] := by
  classical
  refine le_trans ?_ (prEvent_exists_le _ (fun target observed => GoodSelectedAt crypto wire serverKeyId budget claim target observed))
  exact prEvent_mono_of_support _ _ _ fun observed supported good =>
    good_selected crypto wire serverKeyId bounds typed mode work budget bounded before claim observed supported good

theorem outcome_split {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (budget : Budget)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : some observed ∈ support (RegistrationNativeStartupTargets.outcome setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary))
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto wire serverKeyId budget claim observed) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire observed.2.1.transcript observed.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity, GoodSelectedAt setup.source.crypto wire serverKeyId budget claim target observed := by
  simp only [RegistrationNativeStartupTargets.outcome, mem_support_bind_iff] at supported
  obtain ⟨initialized, started, continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [support_map, Set.mem_image, Option.some.injEq] at continued
      obtain ⟨actual, reached, rfl⟩ := continued
      have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
      rw [← sender] at winning ⊢
      rcases RegistrationNativePrekeySplit.ceapp_split setup checks wire route representation initial.created initial.credential readback shortRejects bounds .P
        (adversary initial.public) initial.state budget claim actual reached winning with changed | good
      · exact Or.inl changed
      · exact Or.inr (good_selected setup.source.crypto wire _ bounds
          (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          .P (adversary initial.public) budget (bounded initial.public) initial.state claim actual reached good)

/-- The unchanged broad native APP event pays one real origin charge and only the disjoint functional good-target shares. -/
theorem broad_bound {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (budget : Budget)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (count : Nat) (room : budget.create ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      (∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityOriginBound.reduction (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (fun _ => false) count fallback ordinaryFallback target)) +
      ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (event setup.source.crypto wire serverKeyId budget claim target))}[won = true] := by
  classical
  have split : Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
        (RegistrationNativeIdentityOriginEvents.event setup.joint wire))}[won = true] +
      ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (event setup.source.crypto wire serverKeyId budget claim target))}[won = true] := by
    simp only [RegistrationNativeStartupTargets.profile_outcome, prEvent_map]
    calc
      _ ≤ Pr{let observed ← RegistrationNativeStartupTargets.outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary}[
          observed.elim false (RegistrationNativeIdentityOriginEvents.event setup.joint wire) = true ∨
          ∃ target : Fin budget.accept × Fin budget.capacity,
            observed.elim false (event setup.source.crypto wire serverKeyId budget claim target) = true] := by
        apply prEvent_mono_of_support
        intro observed supported winning
        cases observed with
        | none => cases winning
        | some actual =>
            have original : RegistrationNativeEvents.CEAppWin setup.source.crypto wire serverKeyId budget claim actual := of_decide_eq_true winning
            rcases outcome_split setup checks wire route representation source ensureInit identityIndex serverKeyId readback shortRejects bounds budget adversary bounded claim actual supported original with changed | chosen
            · exact Or.inl (decide_eq_true changed)
            · exact Or.inr (Exists.elim chosen fun target good => ⟨target, decide_eq_true good⟩)
      _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_le _ _))
  exact split.trans (add_le_add (RegistrationNativeIdentityOriginProbability.changed_prekey_bound setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds .P adversary budget bounded count room fallback ordinaryFallback) le_rfl)

end BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.choose_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.choose_at
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.broad_choose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.broad_choose
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.selected_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.selected_at
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.canonical_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.canonical_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.event_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.event_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.good_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.good_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.good_selected_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.good_selected_unique
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.selected_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.selected_mass
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.good_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.good_probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.outcome_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.broad_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage.broad_bound
