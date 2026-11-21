-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInitializedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
/-! The one actual warm corrected public client has source-derived private KEM creation/reveal bills. Its ordinary real/uniform KEM comparison retains the original decision/ledger/platform trace and pays the unconditional correctness error plus one startup-inclusive suffix recovery advantage twice. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

abbrev Result (source : RegistrationNativeMldsa.Source) (cap : Nat) (Value Platform : Type) :=
  RegistrationNativePlatformSecretWordInitializedSource.Result source cap Value Platform

def coins : QueryImpl unifSpec (OracleComp (RegistrationNativeOpenKey.Spec KemSK)) :=
  RegistrationNativeOpenKey.keyLift ∘ₛ RegistrationNativeKeyCompiler.coins

noncomputable def after (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform)
    (context : Context source (budget.cap 4 + budget.cap 5)) : OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source (budget.cap 4 + budget.cap 5) Value Platform) :=
  match context.2.2.2.1 with
  | none => pure (context, none)
  | some started => (fun result => (context, some result)) <$>
      RegistrationNativePlatformG3CheckedUniformSource.openProgram setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selected selectedAccept (setup.dh.publicKey context.2.1)
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route context.1 context.2.1
        (setup.joint.staticDh context.1 (setup.dh.publicKey context.2.1)) serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩)
        (RegistrationNativeG3NativeStartupFields.word started.frontend, previous)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2)

noncomputable def program (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) :
    OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source (budget.cap 4 + budget.cap 5) Value Platform) := do
  let context ← simulateQ coins (prior setup source ensureInit identityIndex serverKeyId budget)
  after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous context

omit primitive in
private theorem reference_coins (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : Secret)
    {A : Type} (work : ProbComp A)
    (before : (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) × RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (simulateQ coins work)).run before = (fun reply => (reply, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT _ ProbComp) := by
    funext query
    apply StateT.ext
    rintro ⟨external, table⟩
    simp only [QueryImpl.compose, coins, RegistrationNativeOpenKey.keyLift,
      RegistrationNativeKeyCompiler.coins, simulateQ_spec_query, RegistrationNativeOpenKeyKemEarlySource.reference,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift, StateT.run, PqxdhRegistrationJointKemSecondEntry.lazyImpl]
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- The genuine early interpreter forwards the exact warm source prefix and its reached cache without altering its private KEM state. -/
theorem reference_source (budget : PqxdhDeploymentInterface.Budget) (selectedOwner : Nat) (previous : Platform)
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : Secret) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selectedOwner previous)).run' ((PqxdhLiveKemBirth.empty, none), ∅) =
      (do let context ← prior setup source ensureInit identityIndex serverKeyId budget
          (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
            (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selectedOwner previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
  unfold program
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [reference_coins setup]
  simp only [bind_map_left]


noncomputable def conditional (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool) : ProbComp Bool := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ Secret
  observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
    profile.pairs profile.publicKey profile.challenge candidate)
    (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)

private theorem after_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (context : Context source (budget.cap 4 + budget.cap 5)) (candidate : Secret) :
    (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
        (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
          profile.pairs profile.publicKey profile.challenge candidate)
          (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      RegistrationNativePlatformSecretWordInitializedSource.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous candidate context := by
  cases success : context.2.2.2.1 with
  | none =>
    simp only [after, RegistrationNativePlatformSecretWordInitializedSource.after, success, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact OracleComp.EvalDistEq.bind_const _ _
  | some started =>
    simp only [after, RegistrationNativePlatformSecretWordInitializedSource.after, success, simulateQ_map, StateT.run'_eq, StateT.run_map, bind_pure_comp]
    simp only [Functor.map_map]
    exact _root_.EvalDistEq.rfl

/-- Moving the independent genuine KEM family past the mathematical candidate preserves the full actual initialized result and same P. -/
theorem conditional_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool) :
    conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous observe =ᵈ
      (fun pair => observe pair.1 pair.2) <$> RegistrationNativePlatformSecretWordInitializedSource.game setup checks wire route source ensureInit identityIndex
        serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  unfold conditional RegistrationNativePlatformSecretWordInitializedSource.game
  simp only [map_bind, map_pure]
  apply _root_.EvalDistEq.bind_right
  intro context
  have swapped := OracleComp.EvalDistEq.bind_bind_swap
    (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected) ($ᵗ Secret)
    (fun profile candidate => observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
      profile.pairs profile.publicKey profile.challenge candidate)
      (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅))
  refine swapped.trans ?_
  apply _root_.EvalDistEq.bind_right
  intro candidate
  have actual := (after_source setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous context candidate).map (observe candidate)
  simpa only [map_bind, bind_pure_comp] using actual

omit primitive in
noncomputable def repeatObservation (setup : Setup base KemSK) {cap : Nat} : Secret → Result source cap Value Platform → Bool := by
  classical
  exact fun candidate result => decide (RegistrationNativePlatformSecretWordInitializedSource.Event source setup candidate result)

/-- The same actual conditional native event is bounded by the one warm-start/KEM-inclusive suffix recovery adversary. -/
theorem conditional_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let flag ← (conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous (repeatObservation source setup))}[flag = true] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (RegistrationNativePlatformSecretWordInitializedAlias.actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  rw [(conditional_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous (repeatObservation source setup)).prEvent_eq]
  simpa only [prEvent_map, repeatObservation, decide_eq_true_eq] using RegistrationNativePlatformSecretWordInitializedSource.repeat_bound setup checks wire route source
    ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous


private theorem after_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Nat) (previous : Platform) (context : Context source (budget.cap 4 + budget.cap 5))
    (kind : RegistrationNativeKemBeaconFootprint.Kind) :
    (simulateQ RegistrationNativeOpenKey.native
      (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous context)).IsQueryBoundP
      (RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeOpenKey.Ambient KemSK kind)
      (if kind = .create then budget.create else 0) := by
  unfold after
  split
  · trivial
  · simp only [simulateQ_map, isQueryBoundP_map_iff]
    apply RegistrationNativeOpenKeyKemTransport.native_bound
    apply RegistrationNativeOpenKeyKemTransport.key_bound
    apply RegistrationNativeOpenKeyKemTransport.retained_bound
    apply RegistrationNativeG2Trace.program_bound
    exact RegistrationNativePlatformPublicKemCaps.run_bound setup checks wire source _ selected selectedAccept _
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer kind serverKeyId bounds mode _ budget (bounded _) _

omit primitive in
private theorem coin_bound {V : Type} (predicate : (RegistrationNativeOpenKey.NativeSpec KemSK).Domain → Prop) [DecidablePred predicate]
    (free : ∀ query, ¬ predicate (.inl (.inl (.inl query)))) (work : ProbComp V) :
    (simulateQ (RegistrationNativeOpenKey.native (KemSK := KemSK)) (simulateQ coins work)).IsQueryBoundP predicate 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp only [QueryImpl.compose, coins, simulateQ_spec_query, RegistrationNativeOpenKey.keyLift,
    RegistrationNativeKeyCompiler.coins, RegistrationNativeOpenKey.native, isQueryBoundP_query_iff]
  intro counted
  exact False.elim (free query counted)

private theorem kind_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Nat) (previous : Platform) (kind : RegistrationNativeKemBeaconFootprint.Kind) :
    (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)).IsQueryBoundP
      (RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeOpenKey.Ambient KemSK kind)
      (if kind = .create then budget.create else 0) := by
  unfold program
  rw [simulateQ_bind]
  apply (OracleComp.isQueryBoundP_bind (n := 0) (m := if kind = .create then budget.create else 0) ?_ ?_).mono (by omega)
  · exact coin_bound _ (by intro query; cases kind <;> simp [RegistrationNativeKemCompilerFootprint.predicate]) _
  · intro context _supported
    exact after_bound setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget bounded selected previous context kind

/-- Original Respects derives the exact reserved-row creation and zero-reveal bills for the entire warm actual corrected public client. -/
theorem resource_bounds (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) (selected : Nat) (previous : Platform) :
    (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create ∧
    (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0 := by
  constructor
  · have bill := kind_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget bounded selected previous .create
    simp only [ite_true] at bill
    apply bill.of_imp
    intro query counted
    rcases query with query | (query | key)
    · exact counted.elim
    · cases query <;> simp_all [RegistrationNativeKemReservation.IsCreate, RegistrationNativeKemCompilerFootprint.predicate]
    · exact counted.elim
  · have bill := kind_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget bounded selected previous .reveal
    simp only [reduceCtorEq, ite_false] at bill
    apply bill.of_imp
    intro query counted
    rcases query with query | (query | key)
    · exact counted.elim
    · cases query <;> simp_all [RegistrationNativeKemPoolSource.IsReveal, RegistrationNativeKemCompilerFootprint.predicate]
    · exact counted.elim

private theorem uniform_of_bounds (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool)
    (creates : (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous)).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous)).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)) observe budget.create selected false =ᵈ
      conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous observe := by
  have closed := RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source setup.baseImpl setup.kem
    (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected.val previous) observe budget.create selected creates noReveal
  refine closed.trans ?_
  have exactPrefix : RegistrationNativeOpenKeyKemEarlyObservedUniform.source setup.baseImpl setup.kem
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous) observe budget.create selected =
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let candidate ← $ᵗ Secret
          let context ← prior setup source ensureInit identityIndex serverKeyId budget
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
    unfold RegistrationNativeOpenKeyKemEarlyObservedUniform.source RegistrationNativeG3NativeRepeatUniformBound.prior
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro chosen
    apply bind_congr
    intro others
    apply bind_congr
    intro pair
    apply bind_congr
    intro candidate
    rw [reference_source]
    simp only [map_bind]
  rw [exactPrefix]
  have swapped :
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let candidate ← $ᵗ Secret
          let context ← prior setup source ensureInit identityIndex serverKeyId budget
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let context ← prior setup source ensureInit identityIndex serverKeyId budget
          let candidate ← $ᵗ Secret
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
    apply _root_.EvalDistEq.bind_right
    intro profile
    exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Secret) (prior setup source ensureInit identityIndex serverKeyId budget) _
  exact swapped.trans (OracleComp.EvalDistEq.bind_bind_swap
    (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected)
    (prior setup source ensureInit identityIndex serverKeyId budget) _)


/-- The one ordinary uniform KEM branch of the actual warm client has its same conditional native result and challenge observation. -/
theorem uniform_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)) observe budget.create selected false =ᵈ
      conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous observe := by
  have bill := resource_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected.val previous
  exact uniform_of_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous observe bill.1 bill.2


noncomputable def real (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp Bool :=
  RegistrationNativeOpenKeyKemEarlyObservedReal.source setup.baseImpl setup.kem
    (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected.val previous) (repeatObservation source setup) budget.create selected

noncomputable def loss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ℝ≥0∞ :=
  ENNReal.ofReal ((setup.kem.IND_CCA_Advantage
    (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)) (repeatObservation source setup) budget.create selected).toINDCCA).toReal +
    RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem) +
  2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
    (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses
      (RegistrationNativePlatformSecretWordInitializedAlias.actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)))) +
    (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹)

/-- The actual warm real early-KEM repeated-role event pays one ordinary CCA advantage, its unconditional correctness error and one explicit whole-prefix recovery loss twice. -/
theorem real_bound (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let flag ← (real setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)}[flag = true] ≤
      loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous := by
  have bills := resource_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected.val previous
  have close := RegistrationNativeOpenKeyKemEarlyObservedReal.source_close setup.baseImpl setup.kem functional
    (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected.val previous) (repeatObservation source setup) budget.create selected bills.1 bills.2
  have uniform := conditional_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected previous
  rw [← (uniform_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected previous (repeatObservation source setup)).prEvent_eq (fun flag => flag = true)] at uniform
  have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (real setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)
    (RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)) (repeatObservation source setup) budget.create selected false)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true] at compared
  apply compared.trans
  have lifted := ENNReal.ofReal_le_ofReal close
  simpa only [real, loss] using (add_le_add uniform lifted).trans (le_of_eq (add_comm _ _))

end BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.reference_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.conditional_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.conditional_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.conditional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.conditional_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.resource_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.resource_bounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.uniform_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem.real_bound
