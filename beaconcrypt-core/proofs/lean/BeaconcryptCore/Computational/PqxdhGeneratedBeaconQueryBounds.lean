import BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment
import BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds

/-!
The concrete generated Beacon scheduler charges the optional Phase1 writer, every native record/public/reveal call and all source/CCA primitive work. No uniform cost is inferred from distribution equality or omitted as ambient computation.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhGeneratedBeaconExperiment
open PqxdhGeneratedBeaconSelector (Program driver driver_source_bound driver_class_bound driver_total)
open PqxdhProtocolQueryBounds PqxdhPrivateAcceptedRootBounds
open PqxdhPrivateRootQueryBounds PqxdhPrivateKemQueryBounds PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhPrivateAcceptedRoot
open PqxdhCorrelatedRootQueryBounds
open PqxdhProtocolSelector (SelectorClass)
open PqxdhJointPhase1AcceptanceComposition (IsSigning)
open PqxdhPrivateSourceCoins (translated)

variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K A : Type} {S B : Nat}

/-- Successful registration pays for the native builder and its complete reached-state scheduler. -/
theorem accepted_observer_bounds {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (post : Post program.Selection S (B + 1)) (budget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) budget)
    (qAux : Nat) (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toEnvironment program).State)))
    (ready : Ready) :
    ObserverBounds ((observer env program post).accepted output ready) 0 0
      ((64 + 5 * qAux) + (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))) 0 0 0 := by
  cases output with
  | none => exact ⟨by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩
  | some output =>
      apply coins_observer_bounds
      apply isTotalQueryBound_bind (build_uniform env.source env.recordWriter env.aux qAux auxBound
        env.senderId env.index env.metadata ready output.context.selection.2)
      intro result
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
        schedule_uniform env.source env.recordWriter env.senderId env.route env.decode
          (post output.context.selection.1 result.1) budget (postBound _ _) result.2

/-- Rejection resumes the reached scheduler with the same explicit allowance; impossible missing-prefix output does no work. -/
theorem completed_observer_bounds {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (post : Post program.Selection S (B + 1)) (budget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) budget)
    (qAux : Nat)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toEnvironment program).State)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    ObserverBounds ((observer env program post).completed output execution) 0 0
      ((64 + 5 * qAux) + (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))) 0 0 0 := by
  cases output with
  | none => exact ⟨by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩
  | some output =>
      apply coins_observer_bounds
      apply IsTotalQueryBound.mono (n₁ := budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))
      · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
          schedule_uniform env.source env.recordWriter env.senderId env.route env.decode
            (post output.context.selection.1 (.ok none)) budget (postBound _ _) output.context.selection.2
      · omega

/-- Exactly the source signing allowance survives native generation/publication and both public entry outcomes. -/
theorem prefix_sign_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : Program baseSpec setup.Context S (B + 1))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) IsSigning)) 0) :
    (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toEnvironment program)).IsQueryBoundP
      (fun query => IsSigning (translated query)) 3 :=
  PqxdhGeneratedPhase1Prefix.program_sign_bound baseImpl kem setup (driver env.toEnvironment program)
    (fun index identity generated transcript => driver_source_bound env.toEnvironment program IsSigning 0
      noSign index identity generated transcript)

/-- Direct source accounting includes the Phase1 writer and every later native response/record effect without a free ambient allowance. -/
theorem actual_uniform_ledger {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (prefixBudget : Budget) (postBudget : RawCtxRevealBudgets.Budget)
    (prefixBound : ∀ reply, Bounded (program.main reply) prefixBudget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qPrekey qKeygen qOneTime qBase qDecap qSource qB qD qWrite qAux uEphemeral uNative bEphemeral bNative : Nat)
    (prekeyBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating)) 0)
    (sourceCoins : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) SourceUniform)) qSource)
    (bases : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery)) qB)
    (decaps : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)) qD)
    (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (ephemeralUniform : (ccaAmbient env.ephemeralGen).IsQueryBoundP IsMlKemUniformQuery uEphemeral)
    (nativeUniform : ∀ target, (ccaAmbient (env.native.encaps target)).IsQueryBoundP IsMlKemUniformQuery uNative)
    (ephemeralBase : (ccaAmbient env.ephemeralGen).IsQueryBoundP IsMlKemBaseQuery bEphemeral)
    (nativeBase : ∀ target, (ccaAmbient (env.native.encaps target)).IsQueryBoundP IsMlKemBaseQuery bNative) :
    (actual env baseImpl kem attachedVerify primitives program post).IsTotalQueryBound
      ((32 + ((qPrekey + (qKeygen + qOneTime)) +
        (qSource + (qWrite + compilerBill prefixBudget) + qBase * qB + qDecap * qD))) +
        ((uEphemeral + (uNative + ((64 + 5 * qAux) +
          (postBudget.1 .coin + 64 * (postBudget.1 .send + postBudget.1 .raw + postBudget.1 .hash))))) +
          qBase * (bEphemeral + bNative))) := by
  have afterBound := nativeNext_observer_bounds kem env.parameters attachedVerify primitives setup
    (observer env program post) uEphemeral uNative bEphemeral bNative 0 0
    ((64 + 5 * qAux) + (postBudget.1 .coin + 64 * (postBudget.1 .send + postBudget.1 .raw + postBudget.1 .hash))) 0 0 0
    ephemeralUniform nativeUniform ephemeralBase nativeBase
    (completed_observer_bounds env program post postBudget postBound qAux)
    (accepted_observer_bounds env program post postBudget postBound qAux auxBound)
  have beforeCoins : ∀ index identity generated transcript,
      ((driver env.toEnvironment program).main index identity generated transcript).IsQueryBoundP
        (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) (qWrite + compilerBill prefixBudget) := by
    intro index identity generated transcript
    exact (driver_total env.toEnvironment program qWrite writerBound prefixBudget prefixBound
      index identity generated transcript).isQueryBoundP
  simpa only [actual, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
    PqxdhGeneratedRootQueryBounds.actualGame_uniform_from_calls baseImpl kem env.parameters attachedVerify primitives setup
      (driver env.toEnvironment program) (observer env program post) qPrekey qKeygen qOneTime qBase qDecap 0 qSource
      (qWrite + compilerBill prefixBudget) qB qD _ _ 0 prekeyBound keygenBound oneTimeBound baseBound decapBound
      (fun index identity generated transcript => driver_source_bound env.toEnvironment program _ 0 noCreate index identity generated transcript)
      (fun index identity generated transcript => driver_source_bound env.toEnvironment program _ qSource sourceCoins index identity generated transcript)
      beforeCoins
      (fun index identity generated transcript => driver_class_bound env.toEnvironment program _
        (by intro coin; simp [SelectorCCA, IsMlKemBaseQuery]) qB bases index identity generated transcript)
      (fun index identity generated transcript => driver_class_bound env.toEnvironment program _
        (by intro coin; simp [SelectorCCA, IsMlKemLogicalDecapsulationQuery]) qD decaps index identity generated transcript)
      (fun prepared => (afterBound prepared).1) (fun prepared => (afterBound prepared).2.1)
      (fun prepared => (afterBound prepared).2.2)

end BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.completed_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.completed_observer_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.prefix_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.prefix_sign_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.actual_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds.actual_uniform_ledger
