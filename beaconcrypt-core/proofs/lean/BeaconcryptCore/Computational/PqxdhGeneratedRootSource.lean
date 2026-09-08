import BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix
import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot

/-!
The generated driver remains inside the exact source sampling continuation when the target KEM pair is moved into its ordinary challenger. Both private generated records, the original signed transcript and the entire driver/source state are retained; the driver and later accepted-root continuation receive only the erased target handle. This compiler preserves every candidate and rejection branch and uses the existing correlated private-root interface. The resulting bound charges the existing joint-use weak-EUF and ordinary IND-CCA endpoints once each; matching private roots retain one supplied shared secret. Native target installation, outer Phase2 routing, evolving-key distributions and final reveal freshness still require concrete interpretation theorems.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedRootSource
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhSecretInputInitializer
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhPrivateRootSource
open PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

open PqxdhPrivateAcceptedRoot PqxdhGeneratedPhase1Prefix

/-- The one-key CCA reduction generates its own identity/prekey/one-time material, then preserves the entire source driver state. The target KEM secret is absent. -/
def borrowedPrefix
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (target : TargetKemPublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Outcome (Retained setup Unit driver.State) × BareState 1) := do
  let seed ← ccaCoins sampleSeed
  let before ← ccaAmbient (setup.prekey (primitives.publicKeys seed).ed25519)
  let after ← ccaAmbient (setup.oneTime (primitives.publicKeys seed).ed25519 before target)
  let generated : Generated setup Unit := ⟨before, target, (), after⟩
  let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
  let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
  let initial := singletonState primitives 1 seed
  let selected ← (simulateQ (borrowedSelector attachedVerify primitives 1)
    (driver.main 0 (primitives.publicKeys seed) generated (transcript bundle material.context))).run
    (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
     signedState primitives seed 0 material.keyTuple initial.2)
  pure (⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.1.2⟩,
    ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2)

/-- Evaluating the ordinary borrowed prefix retains all generated source values and the full adaptive source-state result. -/
theorem borrowedPrefix_evaluated
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (target : TargetKemPublicKey) :
    evalKem baseImpl kem secret (borrowedPrefix attachedVerify primitives setup driver target) = (do
      let seed ← sampleSeed
      let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey (primitives.publicKeys seed).ed25519)
      let after ← simulateQ (kemAmbientImpl baseImpl) (setup.oneTime (primitives.publicKeys seed).ed25519 before target)
      let generated : Generated setup Unit := ⟨before, target, (), after⟩
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let initial := singletonState primitives 1 seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives 1)
        (simulateQ (localSelector baseImpl kem secret) (driver.main 0 (primitives.publicKeys seed) generated (transcript bundle material.context)))).run
        (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
         signedState primitives seed 0 material.keyTuple initial.2)
      pure (⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.1.2⟩,
        ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2)) := by
  simp only [borrowedPrefix, evalKem_bind, evalKem_coins, evalKem_ambient,
    ← localSelector_complete]
  rfl

/-- The actual source retains its generated KEM secret solely in the ordinary interpreter; the complete next protocol interface receives only the secret-erased context and source state. -/
def continuedSource {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (next : Outcome (Retained setup Unit driver.State) × BareState 1 →
      OracleComp (MlKemCCAOracleSpec baseSpec) Result) (fallback : Result) : ProbComp Result := do
  let stopped ← privateRun attachedVerify primitives 1 (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)
  match stopped.1 with
  | none => pure fallback
  | some output =>
      evalKem baseImpl kem output.context.generated.secret (next (eraseOutput output, stopped.2))

/-- Exact evaluated one-key embedding through the entire next protocol continuation. Source order is preserved on the left; the right moves only the independent KEM key pair and never supplies its secret to the reduction. -/
theorem continuedSource_keyfirst {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (next : Outcome (Retained setup Unit driver.State) × BareState 1 →
      OracleComp (MlKemCCAOracleSpec baseSpec) Result) (fallback : Result) :
    𝒟[continuedSource attachedVerify primitives baseImpl kem setup driver next fallback] =
      𝒟[do let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
           evalKem baseImpl kem pair.2
             (borrowedPrefix attachedVerify primitives setup driver pair.1 >>= next)] := by
  have commute := generators_complete_continuation baseImpl primitives kem setup
    (fun seed generated => do
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let initial := singletonState primitives 1 seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives 1)
        (simulateQ (localSelector baseImpl kem generated.secret)
          (driver.main 0 (primitives.publicKeys seed) (eraseGenerated generated) (transcript bundle material.context)))).run
        (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
         signedState primitives seed 0 material.keyTuple initial.2)
      evalKem baseImpl kem generated.secret (next
        (⟨⟨0, primitives.publicKeys seed, eraseGenerated generated, bundle, selected.1.2⟩,
          ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2)))
  simpa only [continuedSource, PqxdhGeneratedPhase1Prefix.program_complete, bind_assoc, pure_bind, evalKem_bind,
    borrowedPrefix_evaluated, identityPreSample, eraseOutput, eraseRetained, eraseGenerated,
    publicMaterial, setupMaterial] using commute

/-- The borrowed prefix retains the challenger public key in the exact generated position through all driver replies. -/
theorem borrowedPrefix_target
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (target : TargetKemPublicKey) (prepared : Prepared setup driver.State)
    (supported : prepared ∈ support (evalKem baseImpl kem secret
      (borrowedPrefix attachedVerify primitives setup driver target))) :
    prepared.1.context.generated.target = target := by
  rw [borrowedPrefix_evaluated] at supported
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, before, _, after, _, selected, _, same⟩ := supported
  subst prepared
  rfl

/-- Source game uses the real optional native interface and the source-shaped private prefix before the observer sees any root-dependent output. -/
noncomputable def actualGame
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State) : ProbComp Bool :=
  continuedSource attachedVerify primitives baseImpl kem setup driver
    (PqxdhPrivateAcceptedRoot.nativeNext kem parameters attachedVerify primitives setup observer) false


/-- The entire real source game agrees with target-only total encapsulation after proving support from the same source generation. No selected-candidate honesty or external target-support premise is used. -/
theorem actualGame_eq_total
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State) :
    𝒟[actualGame baseImpl kem parameters attachedVerify primitives setup driver observer] =
      𝒟[continuedSource attachedVerify primitives baseImpl kem setup driver
        (PqxdhPrivateAcceptedRoot.totalNext kem parameters attachedVerify primitives setup observer) false] := by
  simp only [actualGame, continuedSource, PqxdhGeneratedPhase1Prefix.program_complete, bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro seed
  apply evalDist_bind_congr
  intro generated generatedSupport
  apply evalDist_bind_congr'
  intro selected
  simp only [PqxdhPrivateAcceptedRoot.nativeNext, PqxdhPrivateAcceptedRoot.totalNext]
  split
  · apply PqxdhPrivateAcceptedRoot.nativeTarget_eq_total baseImpl kem parameters compatible attachedVerify primitives setup observer
    exact generate_key_support baseImpl kem setup _ generated generatedSupport
  · rfl


/-- The actual generated source prefix is private ordinary CCA context, with no target secret-key field. -/
noncomputable def rootProtocol
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State) : Protocol baseSpec where
  State := Mode setup driver.State
  prepare target := borrowedPrefix attachedVerify primitives setup driver target >>=
    PqxdhPrivateAcceptedRoot.dispatch kem parameters attachedVerify primitives setup observer
  initialCoordinates _ _ mode := match mode with
    | .completed _ => none
    | .pending prepared ephemeral => some
        (serverCoordinates parameters.source.crypto parameters.server.ikSk ephemeral.toList
          prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
          prepared.1.context.generated.after.publicKey)
  resume _ ciphertext mode root := match mode with
    | .completed decision => pure decision
    | .pending prepared ephemeral => match root with
        | none => pure false
        | some value => PqxdhPrivateAcceptedRoot.finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext value

/-- Native completion preserves every filtered source branch and private root continuation. -/
theorem dispatch_complete_eq_source
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State) (prepared : Prepared setup driver.State)
    (target : TargetKemPublicKey) (secret : KemSK)
    (target_eq : prepared.1.context.generated.target = target) :
    𝒟[do
      let mode ← evalKem baseImpl kem secret
        (PqxdhPrivateAcceptedRoot.dispatch kem parameters attachedVerify primitives setup observer prepared)
      simulateQ (kemAmbientImpl baseImpl)
        (PqxdhPrivateAcceptedRoot.complete parameters.source kem
          (rootProtocol kem parameters attachedVerify primitives setup driver observer)
          target secret mode)] =
      𝒟[evalKem baseImpl kem secret
        (PqxdhPrivateAcceptedRoot.filteredNext kem parameters attachedVerify primitives setup observer prepared)] := by
  by_cases bad : changedBit (some prepared.1, prepared.2) = true
  · apply evalDist_ext
    intro output
    simp [PqxdhPrivateAcceptedRoot.dispatch, PqxdhPrivateAcceptedRoot.filteredNext, bad, evalKem, PqxdhPrivateAcceptedRoot.complete, rootProtocol]
  · by_cases eligible : targetEligible parameters prepared = true
    · simp only [PqxdhPrivateAcceptedRoot.dispatch, PqxdhPrivateAcceptedRoot.filteredNext, bad, Bool.false_eq_true, if_false, eligible, if_true,
        PqxdhPrivateAcceptedRoot.totalNext, PqxdhPrivateAcceptedRoot.totalTargetContinuation, evalKem_bind, evalKem_ambient, bind_assoc]
      apply evalDist_bind_congr'
      intro ephemeral
      cases failure : rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
        prepared.1.context.generated.after.publicKey with
      | none =>
          simp only [PqxdhPrivateAcceptedRoot.complete, rootProtocol, simulateQ_bind, evalKem_pure, pure_bind,
            PqxdhPrivateAcceptedRoot.targetAfterEncapsulation, failure, Option.map_some, target_eq, PqxdhPrivateAcceptedRoot.finishTarget_actual]
      | some reason =>
          simp only [evalKem_bind, evalKem_ambient, evalKem_pure, bind_assoc, pure_bind,
            PqxdhPrivateAcceptedRoot.targetAfterEncapsulation, failure]
          apply evalDist_bind_congr'
          intro encapsulated
          apply evalDist_ext
          intro output
          simp [PqxdhPrivateAcceptedRoot.complete, rootProtocol, probOutput_bind_eq_tsum]
    · apply evalDist_ext
      intro output
      simp [PqxdhPrivateAcceptedRoot.dispatch, PqxdhPrivateAcceptedRoot.filteredNext, bad, eligible, PqxdhPrivateAcceptedRoot.totalNext, evalKem, PqxdhPrivateAcceptedRoot.complete,
        rootProtocol, probOutput_bind_eq_tsum]

set_option backward.isDefEq.respectTransparency false in
/-- The actual filtered prefix and complete native correlated continuation form the ordinary source experiment. -/
theorem filteredSource_eq_sourceMain
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State) :
    𝒟[continuedSource attachedVerify primitives baseImpl kem setup driver
      (PqxdhPrivateAcceptedRoot.filteredNext kem parameters attachedVerify primitives setup observer) false] =
      𝒟[simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem
        (rootProtocol kem parameters attachedVerify primitives setup driver observer))] := by
  rw [continuedSource_keyfirst]
  simp only [sourceMain, rootProtocol, simulateQ_bind, bind_assoc, evalKem_bind]
  apply evalDist_bind_congr'
  intro pair
  apply evalDist_bind_congr
  intro prepared supported
  simpa only [PqxdhPrivateAcceptedRoot.complete, rootProtocol, simulateQ_bind, evalKem, localKemPreChallengeImpl] using
    (dispatch_complete_eq_source baseImpl kem parameters attachedVerify primitives setup driver
    observer prepared pair.1 pair.2
    (borrowedPrefix_target attachedVerify primitives baseImpl kem pair.2 setup driver pair.1 prepared supported)).symm
/-- The filtered source presentation changes only its named bad branch, preserving the same complete private prefix. -/
theorem continuedSource_filtered
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State) :
    continuedSource attachedVerify primitives baseImpl kem setup driver
      (PqxdhPrivateAcceptedRoot.filteredNext kem parameters attachedVerify primitives setup observer) false = (do
      let stopped ← privateRun attachedVerify primitives 1 (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)
      if changedBit stopped then pure false else
        match stopped.1 with
        | none => pure false
        | some output =>
            evalKem baseImpl kem output.context.generated.secret
              (PqxdhPrivateAcceptedRoot.totalNext kem parameters attachedVerify primitives setup observer (eraseOutput output, stopped.2))) := by
  unfold continuedSource
  apply bind_congr
  rintro ⟨output, state⟩
  cases output with
  | none => rfl
  | some output =>
      simp only [PqxdhPrivateAcceptedRoot.filteredNext, erase_changedBit]
      split <;> simp only [evalKem_pure]

/-- The complete actual optional source reaches the correlated native protocol through one concrete joint-use weak-EUF reduction. -/
theorem authentication_hop
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (driverNoSign : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (driverNoCreate : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) (observer : Continuation setup driver.State) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup driver observer).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem
        (rootProtocol kem parameters attachedVerify primitives setup driver observer))) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback)).toReal := by
  have auth := PqxdhGeneratedPhase1Prefix.authentication_continuation_bound attachedVerify primitives adapter baseImpl kem setup driver
    driverNoSign driverNoCreate fallback ordinaryFallback
    (fun stopped => match stopped.1 with
      | none => pure false
      | some output =>
          evalKem baseImpl kem output.context.generated.secret
            (PqxdhPrivateAcceptedRoot.totalNext kem parameters attachedVerify primitives setup observer (eraseOutput output, stopped.2)))
    (fun _ => pure false)
  have totalBound :
      tvDist (continuedSource attachedVerify primitives baseImpl kem setup driver
        (PqxdhPrivateAcceptedRoot.totalNext kem parameters attachedVerify primitives setup observer) false)
        (continuedSource attachedVerify primitives baseImpl kem setup driver
          (PqxdhPrivateAcceptedRoot.filteredNext kem parameters attachedVerify primitives setup observer) false) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback)).toReal := by
    rw [continuedSource_filtered]
    exact auth
  have output := (abs_probOutput_toReal_sub_le_tvDist _ _).trans totalBound
  simpa only [ProbComp.boolDistAdvantage, probOutput_def,
    actualGame_eq_total baseImpl kem parameters compatible attachedVerify primitives setup driver observer,
    ← filteredSource_eq_sourceMain baseImpl kem parameters attachedVerify primitives setup driver observer] using output


/-- The actual authenticated prefix reaches one jointly random shared-secret world. Roots are never replaced independently. -/
theorem authenticated_correlated_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (driverNoSign : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (driverNoCreate : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (observer : Continuation setup driver.State) :
    let protocol := rootProtocol kem parameters attachedVerify primitives setup driver observer
    (actualGame baseImpl kem parameters attachedVerify primitives setup driver observer).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl)
        (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (reduction parameters.source kem protocol).toINDCCA := by
  dsimp only
  have authenticated := authentication_hop baseImpl kem parameters compatible attachedVerify primitives adapter
    setup driver driverNoSign driverNoCreate fallback ordinaryFallback observer
  have correlated := source_correlated_indCCA parameters.source baseImpl kem functional correct
    (rootProtocol kem parameters attachedVerify primitives setup driver observer)
  have loss :
      (simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem
        (rootProtocol kem parameters attachedVerify primitives setup driver observer))).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl) (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl))
        (rootProtocol kem parameters attachedVerify primitives setup driver observer))) =
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (reduction parameters.source kem
          (rootProtocol kem parameters attachedVerify primitives setup driver observer)).toINDCCA := by
    exact correlated.symm
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add authenticated (le_of_eq loss))


end BeaconcryptCore.Computational.PqxdhGeneratedRootSource

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.borrowedPrefix_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.borrowedPrefix_evaluated

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.continuedSource_keyfirst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.continuedSource_keyfirst

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.borrowedPrefix_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.borrowedPrefix_target

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.actualGame_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.actualGame_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.dispatch_complete_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.dispatch_complete_eq_source

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.filteredSource_eq_sourceMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.filteredSource_eq_sourceMain

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.continuedSource_filtered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.continuedSource_filtered

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.authentication_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.authentication_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootSource.authenticated_correlated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootSource.authenticated_correlated_bound
