import BeaconcryptCore.Computational.PqxdhPrivateRootSource

/-!
A trusted generated-prefix driver receives the actual private prekey and one-time records with the target KEM secret erased. The unchanged three-message signing block runs before this driver receives the original public transcript. The driver is a private compiler interface, not an adversarial disclosure interface; concrete optional serialization and native owner publication must be established by its instantiation. No identity seed or KEM secret is passed as a driver argument; declared source reveal operations retain their existing behavior, and the charged authentication event uses the actual reveal history. Explicit zero-extra-signing and zero-extra-creation restrictions support the same coefficient-one joint weak-EUF reduction. No native target installation, reveal freshness or global registration theorem follows from this interface alone.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports PqxdhPhase1AcceptanceOracle PqxdhJointPhase1AcceptanceComposition
open PqxdhJointPhase1SourceWriter PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemQueryBounds
open PrivateSourceInvariants
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

open PqxdhPrivatePhase1Prefix PqxdhPrivateRootSource

/-- Private compiler hook after signing. It receives no Ed25519 seed or target KEM secret. -/
structure Driver (setup : StatefulPhase1Setup baseSpec) where
  State : Type
  main : Nat → PublicIdentity → Generated setup Unit → Phase1PublicTranscript setup.Context →
    OracleComp (SelectorSpec baseSpec) (Phase1Candidate × State)

/-- At fixed private generated inputs, the driver is precisely the existing selector interface. -/
def Driver.selector {setup : StatefulPhase1Setup baseSpec} (driver : Driver setup)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit) :
    Selector baseSpec setup.Context :=
  ⟨driver.State, driver.main index publicIdentity generated⟩

/-- The original source signing block runs first; only its successful result invokes the private generated driver. Its optional result represents missing identity/signing service, while serialization and native publication remain inside the concrete driver. -/
def afterGeneration (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup KemSK) :
    OracleComp PrivateSourceSpec (Option (Retained setup KemSK driver.State × CandidateReport)) :=
  PqxdhPrivatePhase1Prefix.afterGeneration baseImpl kem setup
    (driver.selector index publicIdentity (eraseGenerated generated)) index publicIdentity generated

/-- Actual source key generation runs on the private coin channel in the production order before the signing block. -/
def generatedBody (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (index : Nat) (publicIdentity : PublicIdentity) :
    OracleComp PrivateSourceSpec (Option (Retained setup KemSK driver.State × CandidateReport)) := do
  let generated ← localCoins (generate baseImpl kem setup publicIdentity.ed25519)
  afterGeneration baseImpl kem setup driver index publicIdentity generated

/-- The initial identity creation is an actual source operation; all candidate branches and early missing-service rejection stay in one program. -/
def beforeCandidate (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) :
    OracleComp PrivateSourceSpec (Option (Retained setup KemSK driver.State × CandidateReport)) := do
  let created ← publicSource (SourceSpec.query (.inl (.inr .create)))
  match created with
  | none => pure none
  | some (index, publicIdentity) => generatedBody baseImpl kem setup driver index publicIdentity

/-- Full private Phase-1 source execution, ending at its actual optional attached acceptance. -/
def program (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) :
    OracleComp PrivateSourceSpec (Option (Outcome (Retained setup KemSK driver.State))) :=
  candidateProgram (beforeCandidate baseImpl kem setup driver)

/-- The complete source signing state is retained before the driver receives the original signed bundle. -/
theorem afterGeneration_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup KemSK) (state : BareState count) (seed : IdentitySeed)
    (created : state.2.seeds[index]? = some seed) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (afterGeneration baseImpl kem setup driver index publicIdentity generated)).run state =
      (fun selected => (some (⟨index, publicIdentity, generated,
          signedCandidate primitives seed publicIdentity.ed25519 (publicMaterial setup publicIdentity.ed25519 generated).keyTuple,
          selected.1.2⟩, ⟨index, selected.1.1⟩), selected.2)) <$>
        (simulateQ (privateImpl attachedVerify primitives count)
          (simulateQ (localSelector baseImpl kem generated.secret)
            (driver.main index publicIdentity (eraseGenerated generated) (transcript
              (signedCandidate primitives seed publicIdentity.ed25519 (publicMaterial setup publicIdentity.ed25519 generated).keyTuple)
              (publicMaterial setup publicIdentity.ed25519 generated).context)))).run
          (signedGlobalState primitives seed count index (publicMaterial setup publicIdentity.ed25519 generated).keyTuple state.1,
           signedState primitives seed index (publicMaterial setup publicIdentity.ed25519 generated).keyTuple state.2) := by
  exact PqxdhPrivatePhase1Prefix.afterGeneration_complete attachedVerify primitives count baseImpl kem setup
    (driver.selector index publicIdentity (eraseGenerated generated)) index publicIdentity generated state seed created

/-- Private generation leaves the complete actual source state intact before the unchanged signing/driver continuation. -/
theorem generatedBody_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (index : Nat) (publicIdentity : PublicIdentity)
    (state : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (generatedBody baseImpl kem setup driver index publicIdentity)).run state = (do
        let generated ← generate baseImpl kem setup publicIdentity.ed25519
        (simulateQ (privateImpl attachedVerify primitives count)
          (afterGeneration baseImpl kem setup driver index publicIdentity generated)).run state) := by
  simp only [generatedBody, simulateQ_bind, StateT.run_bind, private_local_complete, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- Identity creation really samples and installs index zero before all private key generation, with its exact public creation observation. -/
theorem beforeCandidate_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) :
    privateRun attachedVerify primitives count (beforeCandidate baseImpl kem setup driver) = (do
      let seed ← sampleSeed
      let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
      (simulateQ (privateImpl attachedVerify primitives count)
        (afterGeneration baseImpl kem setup driver 0 (primitives.publicKeys seed) generated)).run
        (singletonState primitives count seed)) := by
  simp only [privateRun, beforeCandidate, simulateQ_bind, StateT.run_bind, private_public_complete, simulateQ_spec_query]
  rw [show (PqxdhPhase1AcceptanceOracle.initialState count).2.source = initialSource count from rfl,
    bare_create_initial]
  simp only [bind_map_left, generatedBody_complete]

/-- Complete source-generated prefix: actual identity, prekey, KEM, one-time generation, the complete three-signature block, adaptive driver, and real optional acceptance. -/
theorem program_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) :
    privateRun attachedVerify primitives count (program baseImpl kem setup driver) = (do
      let seed ← sampleSeed
      let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let prior := singletonState primitives count seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives count)
        (simulateQ (localSelector baseImpl kem generated.secret)
          (driver.main 0 (primitives.publicKeys seed) (eraseGenerated generated) (transcript bundle material.context)))).run
        (signedGlobalState primitives seed count 0 material.keyTuple prior.1,
         signedState primitives seed 0 material.keyTuple prior.2)
      pure (some ⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.1.2⟩,
          ⟨0, selected.1.1⟩, sourceAccept attachedVerify selected.1.1⟩, selected.2)) := by
  rw [program, privateRun, candidateProgram_complete]
  change (privateRun attachedVerify primitives count (beforeCandidate baseImpl kem setup driver) >>= _) = _
  rw [beforeCandidate_complete]
  simp only [bind_assoc]
  apply bind_congr
  intro seed
  apply bind_congr
  intro generated
  rw [afterGeneration_complete attachedVerify primitives count baseImpl kem setup driver 0
    (primitives.publicKeys seed) generated (singletonState primitives count seed) seed (by rfl)]
  simp only [bind_map_left, Option.map_some]

/-- Actual retained source support establishes the exact three signing messages, unchanged generated identity seed, and honest key-generation support for its target key pair. -/
theorem program_supported
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (noSign : ∀ index publicIdentity generated secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (driver.main index publicIdentity generated publicTranscript)).IsQueryBoundP
        (fun query => IsSigning (translated query)) 0)
    (result : Option (Outcome (Retained setup KemSK driver.State)) × BareState (count + 1))
    (supported : result ∈ support (privateRun attachedVerify primitives (count + 1)
      (program baseImpl kem setup driver))) :
    ∃ seed generated candidate selection,
      result.1 = some ⟨⟨0, primitives.publicKeys seed, generated,
        signedCandidate primitives seed (primitives.publicKeys seed).ed25519
          (publicMaterial setup (primitives.publicKeys seed).ed25519 generated).keyTuple, selection⟩,
        ⟨0, candidate⟩, sourceAccept attachedVerify candidate⟩ ∧
      signedMessages (result.2.1.histories 0) =
        [prekeyMessage generated.before.publicKey, oneTimeMessage generated.after.publicKey, pqMessage generated.target] ∧
      result.2.2.seeds[0]? = some seed ∧
      (generated.target, generated.secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen) := by
  rw [program_complete] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨seed, _, generated, generatedSupport, selected, selectedSupport, finished⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ finished
  refine ⟨seed, generated, selected.1.1, selected.1.2, rfl, ?_, ?_,
    generate_key_support baseImpl kem setup _ generated generatedSupport⟩
  · have preserved := private_run_noSign attachedVerify primitives (count + 1) 0
      _ (noSign 0 (primitives.publicKeys seed) (eraseGenerated generated) generated.secret _) _ selected selectedSupport
    exact preserved.trans (signedGlobalState_three_messages primitives seed 0
      (publicMaterial setup (primitives.publicKeys seed).ed25519 generated).keyTuple
      (singletonState primitives (count + 1) seed).1 rfl)
  · exact private_run_created attachedVerify primitives (count + 1) 0 seed _ _ rfl selected selectedSupport

/-- Fresh changed accepted source fields yield the ordinary fresh-message event, with the actual generator support and signing history derived from this same run. -/
theorem changed_origin
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (noSign : ∀ index publicIdentity generated secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (driver.main index publicIdentity generated publicTranscript)).IsQueryBoundP
        (fun query => IsSigning (translated query)) 0)
    (result : Option (Outcome (Retained setup KemSK driver.State)) × BareState (count + 1))
    (supported : result ∈ support (privateRun attachedVerify primitives (count + 1)
      (program baseImpl kem setup driver))) (changed : Changed result) : OriginEvent primitives result := by
  obtain ⟨seed, generated, candidate, selection, returned, messages, retained, _⟩ :=
    program_supported attachedVerify primitives count baseImpl kem setup driver noSign result supported
  obtain ⟨output, decoded, same, accepted, different, fresh⟩ := changed
  have exactOutput := Option.some.inj (same.symm.trans returned)
  subst output
  refine ⟨_, returned, ?_⟩
  rw [candidateAccepted_iff]
  apply singleBundle_fieldOrigin primitives ⟨0, candidate⟩ (sourceSnapshot primitives result.2)
    (Nat.zero_lt_succ count) (primitives.publicKeys seed)
    (publicMaterial setup (primitives.publicKeys seed).ed25519 generated)
  · simp [sourceSnapshot, sourceKeys, retained]
  · exact fresh
  · exact messages
  · apply (phase1FieldSubstitutionBit_eq_true_iff primitives.verify _ _ candidate).mpr
    exact ⟨decoded, (sourceAccept_eq attachedVerify primitives adapter candidate).symm.trans accepted, different⟩

/-- The actual private source event is bounded by the constructed ordinary joint-use forgery reductions, with every candidate branch present. -/
theorem changed_advantage_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (noSign : ∀ index publicIdentity generated secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (driver.main index publicIdentity generated publicTranscript)).IsQueryBoundP
        (fun query => IsSigning (translated query)) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : (program baseImpl kem setup driver).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass IsCreate) (translated query)) (count + 1)) :
    Pr[Changed | privateRun attachedVerify primitives (count + 1) (program baseImpl kem setup driver)] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (routedAdversary count ordinaryFallback
            (reportExtractor primitives (count + 1) fallback
              (routedClient primitives (count + 1) (instrumentedClient primitives
                ((simulateQ compile (program baseImpl kem setup driver)).run [])))))) := by
  exact (probEvent_mono (fun result supported changed =>
    changed_origin attachedVerify primitives adapter count baseImpl kem setup driver noSign result supported changed)).trans
    (origin_advantage_bound attachedVerify primitives adapter count
      (beforeCandidate baseImpl kem setup driver) fallback ordinaryFallback creates)

/-- Complete signing and driver service counts preserve optional missing-handle rejection and arbitrary CCA side work. -/
theorem afterGeneration_source_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup KemSK)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (coinsExcluded : ∀ coin, ¬ predicate (.inl (.inl coin))) (qWriter qDriver : Nat)
    (writerBound : (signingProgram index publicIdentity.ed25519
      (publicMaterial setup publicIdentity.ed25519 generated).keyTuple).IsQueryBoundP
      (fun query => predicate (.inl query)) qWriter)
    (driverBound : ∀ publicTranscript, (driver.main index publicIdentity (eraseGenerated generated) publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) predicate) qDriver) :
    (afterGeneration baseImpl kem setup driver index publicIdentity generated).IsQueryBoundP
      (fun query => predicate (translated query)) (qWriter + qDriver) := by
  exact PqxdhPrivatePhase1Prefix.afterGeneration_source_bound baseImpl kem setup
    (driver.selector index publicIdentity (eraseGenerated generated)) index publicIdentity generated
    predicate coinsExcluded qWriter qDriver writerBound driverBound

/-- Source-service accounting includes real creation, all optional signing/driver branches and the final unchanged candidate call. Private and primitive coins have a separate ledger. -/
theorem program_source_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (coinsExcluded : ∀ coin, ¬ predicate (.inl (.inl coin)))
    (qCreate qWriter qDriver qAccept : Nat)
    (creation : (SourceSpec.query (.inl (.inr .create)) : OracleComp SourceSpec _).IsQueryBoundP predicate qCreate)
    (writerBound : ∀ (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup KemSK),
      (signingProgram index publicIdentity.ed25519
        (publicMaterial setup publicIdentity.ed25519 generated).keyTuple).IsQueryBoundP
        (fun query => predicate (.inl query)) qWriter)
    (driverBound : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) predicate) qDriver)
    (acceptance : ∀ candidate, (SourceSpec.query (.inr candidate) : OracleComp SourceSpec _).IsQueryBoundP predicate qAccept) :
    (program baseImpl kem setup driver).IsQueryBoundP
      (fun query => predicate (translated query)) (qCreate + (qWriter + qDriver) + qAccept) := by
  have generatedBound : ∀ index publicIdentity,
      (generatedBody baseImpl kem setup driver index publicIdentity).IsQueryBoundP
        (fun query => predicate (translated query)) (qWriter + qDriver) := by
    intro index publicIdentity
    have bound := isQueryBoundP_bind
      (localCoins_excluded (generate baseImpl kem setup publicIdentity.ed25519) predicate coinsExcluded)
      (fun generated _ => afterGeneration_source_bound baseImpl kem setup driver index publicIdentity generated
        predicate coinsExcluded qWriter qDriver (writerBound index publicIdentity generated)
        (driverBound index publicIdentity (eraseGenerated generated)))
    simpa only [generatedBody, Nat.zero_add] using bound
  have beforeBound : (beforeCandidate baseImpl kem setup driver).IsQueryBoundP
      (fun query => predicate (translated query)) (qCreate + (qWriter + qDriver)) := by
    apply isQueryBoundP_bind (publicSource_bound _ predicate qCreate creation)
    intro created _
    cases created with
    | none => trivial
    | some created => exact generatedBound created.1 created.2
  apply isQueryBoundP_bind beforeBound
  intro prepared _
  cases prepared with
  | none => trivial
  | some prepared =>
      simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        publicSource_bound _ predicate qAccept (acceptance prepared.2)

/-- The one-session schedule creates exactly one possible honest source handle and performs no hidden creation in the KEM interpreter. -/
theorem program_create_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (driverNoCreate : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) 0) :
    (program baseImpl kem setup driver).IsQueryBoundP
      (fun query => Creating (translated query)) 1 := by
  exact program_source_bound baseImpl kem setup driver Creating (fun _ => by simp [Creating, IsSourceClass, sourceQuery, SourceClass, IsCreate])
    1 0 0 0
    (by rw [isQueryBoundP_query_iff]; intro _; omega)
    (fun index publicIdentity generated => signingProgram_excluded_bound index publicIdentity.ed25519
      (publicMaterial setup publicIdentity.ed25519 generated).keyTuple
      (fun query => Creating (.inl query))
      (fun _ => by simp [Creating, IsSourceClass, sourceQuery, SourceClass, IsCreate]))
    driverNoCreate
    (fun _ => by rw [isQueryBoundP_query_iff]; simp [Creating, IsSourceClass, sourceQuery, SourceClass])

/-- Constructed coefficient-one joint identity reduction; target Ed seed comes only from its challenger and all KEM private work is locally generated. -/
def privateReduction (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    PublicIdentity → OracleComp AdversarySpec Forgery :=
  globalReduction primitives (0 : Fin 1) ordinaryFallback
    (routedAdversary 0 ordinaryFallback
      (reportExtractor primitives 1 fallback
        (routedClient primitives 1 (instrumentedClient primitives
          ((simulateQ compile (program baseImpl kem setup driver)).run [])))))

/-- Actual private generation and all candidate branches have a coefficient-one ordinary joint weak-EUF bound. Zero signing/creation driver caps are checked schedule restrictions, not a target-honesty premise. -/
theorem authentication_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (driverNoSign : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (driverNoCreate : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    Pr[Changed | privateRun attachedVerify primitives 1 (program baseImpl kem setup driver)] ≤
      advantage primitives (privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback) := by
  have bounded := changed_advantage_bound attachedVerify primitives adapter 0 baseImpl kem setup driver
    (fun index publicIdentity generated secret publicTranscript =>
      localSelector_source_bound baseImpl kem secret (driver.main index publicIdentity generated publicTranscript)
      IsSigning (fun _ => by simp [IsSigning, dynamicClass, IsClass]) 0 (driverNoSign index publicIdentity generated publicTranscript))
    fallback ordinaryFallback (program_create_bound baseImpl kem setup driver driverNoCreate)
  rw [Fin.sum_univ_succ] at bounded
  simpa [privateReduction] using bounded

/-- The actual source signing block pays for all three signatures, with no extra signing request hidden in private KEM generation or interpretation. -/
theorem program_sign_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (driverNoSign : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0) :
    (program baseImpl kem setup driver).IsQueryBoundP
      (fun query => IsSigning (translated query)) 3 := by
  exact program_source_bound baseImpl kem setup driver IsSigning
    (fun _ => by simp [IsSigning, dynamicClass, IsClass]) 0 3 0 0
    (by rw [isQueryBoundP_query_iff]; simp [IsSigning, dynamicClass])
    (fun index publicIdentity generated =>
      signingProgram_class_bound index publicIdentity.ed25519
        (publicMaterial setup publicIdentity.ed25519 generated).keyTuple .sign)
    driverNoSign
    (fun _ => by rw [isQueryBoundP_query_iff]; simp [IsSigning])

/-- Authentication changes only the charged source branch through an arbitrary complete private continuation. The stopped EUF reduction need not execute the later KEM-secret-dependent work. -/
theorem authentication_continuation_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (driverNoSign : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (driverNoCreate : ∀ index publicIdentity generated publicTranscript,
      (driver.main index publicIdentity generated publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (next onChanged : Option (Outcome (Retained setup KemSK driver.State)) × BareState 1 → ProbComp Result) :
    (𝒟[privateRun attachedVerify primitives 1 (program baseImpl kem setup driver) >>= next]).tvDist
      (𝒟[privateRun attachedVerify primitives 1 (program baseImpl kem setup driver) >>= fun state =>
        if changedBit state then onChanged state else next state]) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback)).toReal := by
  refine (tvDist_bind_left_event_le (privateRun attachedVerify primitives 1 (program baseImpl kem setup driver))
    next _ (fun state => changedBit state = true) (fun state good => by simp [good])).trans ?_
  apply ENNReal.toReal_mono (show advantage primitives
    (privateReduction primitives baseImpl kem setup driver fallback ordinaryFallback) ≠ ∞ from probOutput_ne_top)
  simpa only [changedBit_iff] using authentication_bound attachedVerify primitives adapter baseImpl kem setup driver
    driverNoSign driverNoCreate fallback ordinaryFallback

end BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.afterGeneration_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.afterGeneration_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.generatedBody_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.generatedBody_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.beforeCandidate_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.beforeCandidate_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_supported

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.changed_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.changed_origin

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.changed_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.changed_advantage_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.afterGeneration_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.afterGeneration_source_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_source_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_create_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.authentication_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.program_sign_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.authentication_continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.authentication_continuation_bound
