import BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance
import BeaconcryptCore.Computational.PqxdhPrivateKemSource
import BeaconcryptCore.Computational.PrivateSourceInvariants
import BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds

/-!
Actual source creation, private key generation, three original signing messages, arbitrary candidate selection and optional acceptance share one complete experiment. Zero extra signing/creation caps are explicit schedule restrictions, not derived native lifetime policies. Source support proves the exact signing log and honest target KEM support. The retained KEM secret is analysis state and must be erased before a borrowed root continuation.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports PqxdhPhase1AcceptanceOracle PqxdhJointPhase1AcceptanceComposition
open PqxdhJointPhase1SourceWriter PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemQueryBounds
open PrivateSourceInvariants
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Private source continuation state; the secret KEM field is used only by its local CCA interpreter. -/
structure Retained (setup : StatefulPhase1Setup baseSpec) (KemSK Selection : Type) where
  index : Nat
  publicIdentity : PublicIdentity
  generated : Generated setup KemSK
  bundle : Phase1Candidate
  selection : Selection

/-- The selector sees original signed fields and the source's public context, with no private generated key argument. -/
def transcript {Context : Type} (bundle : Phase1Candidate) (context : Context) : Phase1PublicTranscript Context :=
  ⟨bundle.identityKey, bundle.preKey, bundle.oneTimeKey, bundle.pqKey, context⟩

/-- Source signing finishes before adaptive candidate selection, preserving all private generation and selector continuation state. -/
def afterGeneration (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup KemSK) :
    OracleComp PrivateSourceSpec (Option (Retained setup KemSK selector.State × CandidateReport)) := do
  let material := publicMaterial setup publicIdentity.ed25519 generated
  let signed ← publicSource (liftDynamic (signingProgram index publicIdentity.ed25519 material.keyTuple))
  match signed with
  | none => pure none
  | some bundle =>
      let selected ← simulateQ (localSelector baseImpl kem generated.secret)
        (selector.main (transcript bundle material.context))
      pure (some (⟨index, publicIdentity, generated, bundle, selected.2⟩, ⟨index, selected.1⟩))

/-- Actual source key generation runs on the private coin channel in the production order before the signing block. -/
def generatedBody (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (index : Nat) (publicIdentity : PublicIdentity) :
    OracleComp PrivateSourceSpec (Option (Retained setup KemSK selector.State × CandidateReport)) := do
  let generated ← localCoins (generate baseImpl kem setup publicIdentity.ed25519)
  afterGeneration baseImpl kem setup selector index publicIdentity generated

/-- The initial identity creation is an actual source operation; all candidate branches and early missing-service rejection stay in one program. -/
def beforeCandidate (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) :
    OracleComp PrivateSourceSpec (Option (Retained setup KemSK selector.State × CandidateReport)) := do
  let created ← publicSource (SourceSpec.query (.inl (.inr .create)))
  match created with
  | none => pure none
  | some (index, publicIdentity) => generatedBody baseImpl kem setup selector index publicIdentity

/-- Full private Phase-1 source execution, ending at its actual optional attached acceptance. -/
def program (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) :
    OracleComp PrivateSourceSpec (Option (Outcome (Retained setup KemSK selector.State))) :=
  candidateProgram (beforeCandidate baseImpl kem setup selector)

/-- The complete retained writer state is installed before the selector receives the original signed bundle. -/
theorem afterGeneration_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup KemSK) (state : BareState count) (seed : IdentitySeed)
    (created : state.2.seeds[index]? = some seed) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (afterGeneration baseImpl kem setup selector index publicIdentity generated)).run state =
      (fun selected => (some (⟨index, publicIdentity, generated,
          signedCandidate primitives seed publicIdentity.ed25519 (publicMaterial setup publicIdentity.ed25519 generated).keyTuple,
          selected.1.2⟩, ⟨index, selected.1.1⟩), selected.2)) <$>
        (simulateQ (privateImpl attachedVerify primitives count)
          (simulateQ (localSelector baseImpl kem generated.secret)
            (selector.main (transcript
              (signedCandidate primitives seed publicIdentity.ed25519 (publicMaterial setup publicIdentity.ed25519 generated).keyTuple)
              (publicMaterial setup publicIdentity.ed25519 generated).context)))).run
          (signedGlobalState primitives seed count index (publicMaterial setup publicIdentity.ed25519 generated).keyTuple state.1,
           signedState primitives seed index (publicMaterial setup publicIdentity.ed25519 generated).keyTuple state.2) := by
  simp only [afterGeneration, simulateQ_bind, StateT.run_bind, private_public_complete,
    liftDynamic_complete, signingProgram_complete primitives count index publicIdentity.ed25519
      (publicMaterial setup publicIdentity.ed25519 generated).keyTuple state.1 state.2 seed created,
    pure_bind, bind_pure_comp, simulateQ_map, StateT.run_map]

/-- Private generation leaves the complete actual source state intact before the unchanged writer/selector continuation. -/
theorem generatedBody_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (index : Nat) (publicIdentity : PublicIdentity)
    (state : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (generatedBody baseImpl kem setup selector index publicIdentity)).run state = (do
        let generated ← generate baseImpl kem setup publicIdentity.ed25519
        (simulateQ (privateImpl attachedVerify primitives count)
          (afterGeneration baseImpl kem setup selector index publicIdentity generated)).run state) := by
  simp only [generatedBody, simulateQ_bind, StateT.run_bind, private_local_complete, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- Identity creation really samples and installs index zero before all private key generation, with its exact public creation observation. -/
theorem beforeCandidate_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) :
    privateRun attachedVerify primitives count (beforeCandidate baseImpl kem setup selector) = (do
      let seed ← sampleSeed
      let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
      (simulateQ (privateImpl attachedVerify primitives count)
        (afterGeneration baseImpl kem setup selector 0 (primitives.publicKeys seed) generated)).run
        (singletonState primitives count seed)) := by
  simp only [privateRun, beforeCandidate, simulateQ_bind, StateT.run_bind, private_public_complete, simulateQ_spec_query]
  rw [show (PqxdhPhase1AcceptanceOracle.initialState count).2.source = initialSource count from rfl,
    bare_create_initial]
  simp only [bind_map_left, generatedBody_complete]

/-- Complete source-generated prefix: actual identity, prekey, KEM, one-time generation, the full writer, adaptive selector, and real optional acceptance. -/
theorem program_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) :
    privateRun attachedVerify primitives count (program baseImpl kem setup selector) = (do
      let seed ← sampleSeed
      let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let prior := singletonState primitives count seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives count)
        (simulateQ (localSelector baseImpl kem generated.secret)
          (selector.main (transcript bundle material.context)))).run
        (signedGlobalState primitives seed count 0 material.keyTuple prior.1,
         signedState primitives seed 0 material.keyTuple prior.2)
      pure (some ⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.1.2⟩,
          ⟨0, selected.1.1⟩, sourceAccept attachedVerify selected.1.1⟩, selected.2)) := by
  rw [program, privateRun, candidateProgram_complete]
  change (privateRun attachedVerify primitives count (beforeCandidate baseImpl kem setup selector) >>= _) = _
  rw [beforeCandidate_complete]
  simp only [bind_assoc]
  apply bind_congr
  intro seed
  apply bind_congr
  intro generated
  rw [afterGeneration_complete attachedVerify primitives count baseImpl kem setup selector 0
    (primitives.publicKeys seed) generated (singletonState primitives count seed) seed (by rfl)]
  simp only [bind_map_left, Option.map_some]

/-- Actual retained source support establishes the exact three signing messages, unchanged generated identity seed, and honest key-generation support for its target key pair. -/
theorem program_supported
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (noSign : ∀ secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript)).IsQueryBoundP
        (fun query => IsSigning (translated query)) 0)
    (result : Option (Outcome (Retained setup KemSK selector.State)) × BareState (count + 1))
    (supported : result ∈ support (privateRun attachedVerify primitives (count + 1)
      (program baseImpl kem setup selector))) :
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
      _ (noSign generated.secret _) _ selected selectedSupport
    exact preserved.trans (signedGlobalState_three_messages primitives seed 0
      (publicMaterial setup (primitives.publicKeys seed).ed25519 generated).keyTuple
      (singletonState primitives (count + 1) seed).1 rfl)
  · exact private_run_created attachedVerify primitives (count + 1) 0 seed _ _ rfl selected selectedSupport

/-- The source's actual optional acceptance identifies changed signed keys under its fresh generated identity. -/
def Changed {setup : StatefulPhase1Setup baseSpec} {Selection : Type} {count : Nat}
    (result : Option (Outcome (Retained setup KemSK Selection)) × BareState (count + 1)) : Prop :=
  ∃ output decoded, result.1 = some output ∧
    output.accepted = some (output.context.publicIdentity.ed25519, decoded) ∧
    decoded ≠ (publicMaterial setup output.context.publicIdentity.ed25519 output.context.generated).keyTuple ∧
    (0 : Fin (count + 1)) ∉ result.2.1.reveals

/-- Fresh changed accepted source fields yield the ordinary fresh-message event, with the actual generator support and signing history derived from this same run. -/
theorem changed_origin
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (noSign : ∀ secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript)).IsQueryBoundP
        (fun query => IsSigning (translated query)) 0)
    (result : Option (Outcome (Retained setup KemSK selector.State)) × BareState (count + 1))
    (supported : result ∈ support (privateRun attachedVerify primitives (count + 1)
      (program baseImpl kem setup selector))) (changed : Changed result) : OriginEvent primitives result := by
  obtain ⟨seed, generated, candidate, selection, returned, messages, retained, _⟩ :=
    program_supported attachedVerify primitives count baseImpl kem setup selector noSign result supported
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
    (selector : Selector baseSpec setup.Context)
    (noSign : ∀ secret publicTranscript,
      (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript)).IsQueryBoundP
        (fun query => IsSigning (translated query)) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass IsCreate) (translated query)) (count + 1)) :
    Pr[Changed | privateRun attachedVerify primitives (count + 1) (program baseImpl kem setup selector)] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (routedAdversary count ordinaryFallback
            (reportExtractor primitives (count + 1) fallback
              (routedClient primitives (count + 1) (instrumentedClient primitives
                ((simulateQ compile (program baseImpl kem setup selector)).run [])))))) := by
  exact (probEvent_mono (fun result supported changed =>
    changed_origin attachedVerify primitives adapter count baseImpl kem setup selector noSign result supported changed)).trans
    (origin_advantage_bound attachedVerify primitives adapter count
      (beforeCandidate baseImpl kem setup selector) fallback ordinaryFallback creates)

/-- Complete writer and selector service counts preserve optional missing-handle rejection and arbitrary CCA side work. -/
theorem afterGeneration_source_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup KemSK)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (coinsExcluded : ∀ coin, ¬ predicate (.inl (.inl coin))) (qWriter qSelector : Nat)
    (writerBound : (signingProgram index publicIdentity.ed25519
      (publicMaterial setup publicIdentity.ed25519 generated).keyTuple).IsQueryBoundP
      (fun query => predicate (.inl query)) qWriter)
    (selectorBound : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) predicate) qSelector) :
    (afterGeneration baseImpl kem setup selector index publicIdentity generated).IsQueryBoundP
      (fun query => predicate (translated query)) (qWriter + qSelector) := by
  apply isQueryBoundP_bind
    (publicSource_bound _ predicate qWriter (liftDynamic_query_bound _ predicate qWriter writerBound))
  intro bundle _
  cases bundle with
  | none => trivial
  | some bundle =>
      simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        localSelector_source_bound baseImpl kem generated.secret
          (selector.main (transcript bundle (publicMaterial setup publicIdentity.ed25519 generated).context))
          predicate coinsExcluded qSelector (selectorBound _)

/-- Source-service accounting includes real creation, all optional writer/selector branches and the final unchanged candidate call. Private and primitive coins have a separate ledger. -/
theorem program_source_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (coinsExcluded : ∀ coin, ¬ predicate (.inl (.inl coin)))
    (qCreate qWriter qSelector qAccept : Nat)
    (creation : OracleComp.IsQueryBoundP
      (SourceSpec.query (.inl (.inr .create)) : OracleComp SourceSpec _) predicate qCreate)
    (writerBound : ∀ (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup KemSK),
      (signingProgram index publicIdentity.ed25519
        (publicMaterial setup publicIdentity.ed25519 generated).keyTuple).IsQueryBoundP
        (fun query => predicate (.inl query)) qWriter)
    (selectorBound : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) predicate) qSelector)
    (acceptance : ∀ candidate, OracleComp.IsQueryBoundP
      (SourceSpec.query (.inr candidate) : OracleComp SourceSpec _) predicate qAccept) :
    (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => predicate (translated query)) (qCreate + (qWriter + qSelector) + qAccept) := by
  have generatedBound : ∀ index publicIdentity,
      (generatedBody baseImpl kem setup selector index publicIdentity).IsQueryBoundP
        (fun query => predicate (translated query)) (qWriter + qSelector) := by
    intro index publicIdentity
    have bound := isQueryBoundP_bind
      (localCoins_excluded (generate baseImpl kem setup publicIdentity.ed25519) predicate coinsExcluded)
      (fun generated _ => afterGeneration_source_bound baseImpl kem setup selector index publicIdentity generated
        predicate coinsExcluded qWriter qSelector (writerBound index publicIdentity generated) selectorBound)
    simpa only [generatedBody, Nat.zero_add] using bound
  have beforeBound : (beforeCandidate baseImpl kem setup selector).IsQueryBoundP
      (fun query => predicate (translated query)) (qCreate + (qWriter + qSelector)) := by
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

/-- Exact source identity-creation class, excluding all private protocol coins. -/
abbrev Creating := IsSourceClass (SourceClass IsCreate)

/-- The one-session schedule creates exactly one possible honest source handle and performs no hidden creation in the KEM interpreter. -/
theorem program_create_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) 0) :
    (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => Creating (translated query)) 1 := by
  exact program_source_bound baseImpl kem setup selector Creating (fun _ => by simp [Creating, IsSourceClass, sourceQuery, SourceClass, IsCreate])
    1 0 0 0
    (by rw [isQueryBoundP_query_iff]; intro _; omega)
    (fun index publicIdentity generated => signingProgram_excluded_bound index publicIdentity.ed25519
      (publicMaterial setup publicIdentity.ed25519 generated).keyTuple
      (fun query => Creating (.inl query))
      (fun _ => by simp [Creating, IsSourceClass, sourceQuery, SourceClass, IsCreate]))
    selectorNoCreate
    (fun _ => by rw [isQueryBoundP_query_iff]; simp [Creating, IsSourceClass, sourceQuery, SourceClass])

/-- Constructed coefficient-one joint identity reduction; target Ed seed comes only from its challenger and all KEM private work is locally generated. -/
def privateReduction (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    PublicIdentity → OracleComp AdversarySpec Forgery :=
  globalReduction primitives (0 : Fin 1) ordinaryFallback
    (routedAdversary 0 ordinaryFallback
      (reportExtractor primitives 1 fallback
        (routedClient primitives 1 (instrumentedClient primitives
          ((simulateQ compile (program baseImpl kem setup selector)).run [])))))

/-- Actual private generation and all candidate branches have a coefficient-one ordinary joint weak-EUF bound. Zero signing/creation selector caps are checked schedule restrictions, not a target-honesty premise. -/
theorem authentication_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    Pr[Changed | privateRun attachedVerify primitives 1 (program baseImpl kem setup selector)] ≤
      advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback) := by
  have bounded := changed_advantage_bound attachedVerify primitives adapter 0 baseImpl kem setup selector
    (fun secret publicTranscript => localSelector_source_bound baseImpl kem secret (selector.main publicTranscript)
      IsSigning (fun _ => by simp [IsSigning, dynamicClass, IsClass]) 0 (selectorNoSign publicTranscript))
    fallback ordinaryFallback (program_create_bound baseImpl kem setup selector selectorNoCreate)
  rw [Fin.sum_univ_succ] at bounded
  simpa [privateReduction] using bounded

/-- Executable test for precisely the charged fresh changed acceptance branch. -/
def changedBit {setup : StatefulPhase1Setup baseSpec} {Selection : Type} {count : Nat}
    (result : Option (Outcome (Retained setup KemSK Selection)) × BareState (count + 1)) : Bool :=
  match result.1 with
  | none => false
  | some output => match output.accepted with
    | none => false
    | some (identity, keys) => decide (identity = output.context.publicIdentity.ed25519 ∧
        keys ≠ (publicMaterial setup output.context.publicIdentity.ed25519 output.context.generated).keyTuple ∧
        (0 : Fin (count + 1)) ∉ result.2.1.reveals)

/-- The branch test refers to actual decoded acceptance and actual source reveal history. -/
theorem changedBit_iff {setup : StatefulPhase1Setup baseSpec} {Selection : Type} {count : Nat}
    (result : Option (Outcome (Retained setup KemSK Selection)) × BareState (count + 1)) :
    changedBit result = true ↔ Changed result := by
  cases returned : result.1 with
  | none => simp [changedBit, Changed, returned]
  | some output =>
      cases accepted : output.accepted with
      | none => simp [changedBit, Changed, returned, accepted]
      | some pair =>
          rcases pair with ⟨identity, keys⟩
          simp [changedBit, Changed, returned, accepted, Prod.mk.injEq, and_assoc]

/-- The actual source writer pays for all three signatures, with no extra signing request hidden in private KEM generation or interpretation. -/
theorem program_sign_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0) :
    (program baseImpl kem setup selector).IsQueryBoundP
      (fun query => IsSigning (translated query)) 3 := by
  exact program_source_bound baseImpl kem setup selector IsSigning
    (fun _ => by simp [IsSigning, dynamicClass, IsClass]) 0 3 0 0
    (by rw [isQueryBoundP_query_iff]; simp [IsSigning, dynamicClass])
    (fun index publicIdentity generated =>
      signingProgram_class_bound index publicIdentity.ed25519
        (publicMaterial setup publicIdentity.ed25519 generated).keyTuple .sign)
    selectorNoSign
    (fun _ => by rw [isQueryBoundP_query_iff]; simp [IsSigning])

/-- Authentication changes only the charged source branch through an arbitrary complete private continuation. The stopped EUF reduction need not execute the later KEM-secret-dependent work. -/
theorem authentication_continuation_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (next onChanged : Option (Outcome (Retained setup KemSK selector.State)) × BareState 1 → ProbComp Result) :
    tvDist (privateRun attachedVerify primitives 1 (program baseImpl kem setup selector) >>= next)
      (privateRun attachedVerify primitives 1 (program baseImpl kem setup selector) >>= fun state =>
        if changedBit state then onChanged state else next state) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal := by
  refine (tvDist_bind_left_event_le (privateRun attachedVerify primitives 1 (program baseImpl kem setup selector))
    next _ (fun state => changedBit state = true) (fun state good => by simp [good])).trans ?_
  apply ENNReal.toReal_mono (show advantage primitives
    (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback) ≠ ∞ from prEvent_ne_top _)
  simpa only [changedBit_iff] using authentication_bound attachedVerify primitives adapter baseImpl kem setup selector
    selectorNoSign selectorNoCreate fallback ordinaryFallback

end BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.afterGeneration_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.afterGeneration_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.generatedBody_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.generatedBody_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.beforeCandidate_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.beforeCandidate_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_supported

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.changed_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.changed_origin

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.changed_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.changed_advantage_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.afterGeneration_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.afterGeneration_source_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_source_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_create_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.authentication_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.changedBit_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.changedBit_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.program_sign_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.authentication_continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.authentication_continuation_bound
