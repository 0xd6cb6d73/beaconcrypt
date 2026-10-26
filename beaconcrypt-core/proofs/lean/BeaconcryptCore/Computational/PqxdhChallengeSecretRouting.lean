import BeaconcryptCore.Computational.PqxdhPrivateRootSource
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
This component routes the ordinary CCA-supplied shared secret through an initial private root and every later private derivation at the same ciphertext. Actual Beacon coordinates include arbitrary ephemeral inputs. The public CCA channel retains its standard block; private processing is not forbidden by freshness. Ordinary perfect correctness on actual generated/encapsulated support identifies the secret. Full arbitrary-stateful substitution additionally uses the explicit pure functional decapsulation interface, so evaluated output equality never erases primitive effects. The correlated real/random hop has coefficient one. Protocol state and root replies are private interpreter values; native registration/role instantiation, correlated multi-input Extract and the global security theorem remain separate.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhChallengeSecretRouting
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhHiddenRoot PqxdhJointKdfGame PqxdhSecretInputKdf

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Evaluated ordinary correctness determines the complete stateless decapsulation distribution on actual honest support. -/
theorem honest_decapsulation
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    {pk : MlKem768PublicKey} {sk : KemSK}
    (generated : (pk, sk) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen))
    {ciphertext : MlKem768Ciphertext} {secret : MlKemSharedSecret}
    (encapsulated : (ciphertext, secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps pk))) :
    EvalDistEq (simulateQ (kemAmbientImpl baseImpl) (kem.decaps sk ciphertext))
      (pure (some secret) : ProbComp (Option MlKemSharedSecret)) := by
  let : MeasurableSpace MlKem768PublicKey := ⊤
  let : DiscreteMeasurableSpace MlKem768PublicKey := ⟨fun _ => by simp⟩
  let : MeasurableSpace MlKem768Ciphertext := ⊤
  let : DiscreteMeasurableSpace MlKem768Ciphertext := ⟨fun _ => by simp⟩
  let : MeasurableSpace MlKemSharedSecret := ⊤
  let : DiscreteMeasurableSpace MlKemSharedSecret := ⟨fun _ => by simp⟩
  let : MeasurableSpace KemSK := ⊤
  let : DiscreteMeasurableSpace KemSK := ⟨fun _ => by simp⟩
  let : MeasurableSpace (MlKem768PublicKey × KemSK) := ⊤
  let : DiscreteMeasurableSpace (MlKem768PublicKey × KemSK) := ⟨fun _ => by simp⟩
  let : MeasurableSpace (MlKem768Ciphertext × MlKemSharedSecret) := ⊤
  let : DiscreteMeasurableSpace (MlKem768Ciphertext × MlKemSharedSecret) := ⟨fun _ => by simp⟩
  let : MeasurableSpace (Option MlKemSharedSecret) := ⊤
  let : DiscreteMeasurableSpace (Option MlKemSharedSecret) := ⟨fun _ => by simp⟩
  let decapsulation := simulateQ (kemAmbientImpl baseImpl) (kem.decaps sk ciphertext)
  have unique : ∀ recovered ∈ support decapsulation, recovered = some secret := by
    intro recovered supported
    exact mlKem768RecipientCorrectness_recovered_eq kem
      (runtimeOfImpl (kemAmbientImpl baseImpl))
      (runtimeOfImpl_evalDist_pure _) (runtimeOfImpl_evalDist_bind _) correct
      (pk := pk) (sk := sk)
      (by simpa only [runtimeOfImpl_evalDist] using
        ((OracleComp.mem_support_iff_evalDist_singleton_pos _ _).1 generated).ne')
      (by simpa only [runtimeOfImpl_evalDist] using
        ((OracleComp.mem_support_iff_evalDist_singleton_pos _ _).1 encapsulated).ne')
      (by simpa only [runtimeOfImpl_evalDist] using
        ((OracleComp.mem_support_iff_evalDist_singleton_pos _ _).1 supported).ne')
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun recovered => ?_
  rw [prEvent_pure]
  by_cases same : recovered = some secret
  · subst recovered
    rw [ite_eq_left rfl]
    exact OracleComp.prEvent_eq_one_of_forall_mem_support _ _ unique
  · rw [ite_eq_right fun equal => same equal.symm]
    exact prEvent_eq_zero_of_not_mem_support _ fun supported => same (unique _ supported)

/-- A functional primitive implementation uses no ambient oracle effects during decapsulation. -/
structure FunctionalDecapsulation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) where
  result : KemSK → MlKem768Ciphertext → Option MlKemSharedSecret
  exact : ∀ sk ciphertext, kem.decaps sk ciphertext = pure (result sk ciphertext)

/-- Correctness plus the explicit functional interface gives a program equality, so arbitrary later oracle state is preserved. -/
theorem honest_decapsulation_program
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    {pk : MlKem768PublicKey} {sk : KemSK}
    (generated : (pk, sk) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen))
    {ciphertext : MlKem768Ciphertext} {secret : MlKemSharedSecret}
    (encapsulated : (ciphertext, secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps pk))) :
    kem.decaps sk ciphertext = pure (some secret) := by
  have evaluated := honest_decapsulation baseImpl kem correct generated encapsulated
  simp only [functional.exact, simulateQ_pure] at evaluated
  have values : functional.result sk ciphertext = some secret := by
    have mass := evaluated.prEvent_eq fun recovered => recovered = functional.result sk ciphertext
    rw [prEvent_pure, prEvent_pure, ite_eq_left rfl] at mass
    by_contra different
    rw [ite_eq_right fun equal => different equal.symm] at mass
    exact one_ne_zero mass
  rw [functional.exact, values]

/-- A private protocol request carries the actual ciphertext and all four actual DH coordinates. -/
structure RootRequest where
  ciphertext : MlKem768Ciphertext
  coordinates : KnownPqxdhRootCoordinates

/-- Public CCA traffic and private protocol root derivations have distinct channels. -/
abbrev LocalPostSpec (baseSpec : OracleSpec ι) :=
  MlKemCCAOracleSpec baseSpec + (RootRequest →ₒ Option RootOutput)

/-- The reduction owns the supplied secret. Matching private requests reuse it; other private requests use ordinary permitted decapsulation. -/
noncomputable def route
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret) :
    QueryImpl (LocalPostSpec baseSpec) (OracleComp (MlKemCCAOracleSpec baseSpec))
  | .inl request => (MlKemCCAOracleSpec baseSpec).query request
  | .inr request => do
      let recovered ← if request.ciphertext = challenge then pure (some supplied)
        else (MlKemCCAOracleSpec baseSpec).query (.inr request.ciphertext)
      return recovered.map (productionHiddenRoot source request.coordinates)

/-- The ordinary public post-challenge service at the explicit source-facing query type. -/
noncomputable def publicImpl
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (MlKemCCAOracleSpec baseSpec) (OracleComp (unifSpec + baseSpec)) :=
  kem.IND_CCA_postChallengeImpl secret challenge

theorem publicImpl_other
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge ciphertext : MlKem768Ciphertext)
    (different : ciphertext ≠ challenge) :
    publicImpl kem secret challenge (.inr ciphertext) = kem.decaps secret ciphertext :=
  indCCA_postChallengeImpl_nonchallenge kem secret challenge ciphertext different

/-- Actual private requests all decapsulate; only the separate public CCA channel applies the standard challenge block. -/
noncomputable def actualImpl
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (LocalPostSpec baseSpec) (OracleComp (unifSpec + baseSpec))
  | .inl request => publicImpl kem secret challenge request
  | .inr request => do
      let recovered ← kem.decaps secret request.ciphertext
      return recovered.map (productionHiddenRoot source request.coordinates)

/-- Exact handler equality retains every ambient effect and every actual optional root reply. -/
theorem route_interpreter
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied)) :
    publicImpl kem secret challenge ∘ₛ route source challenge supplied =
      actualImpl source kem secret challenge := by
  funext request
  cases request with
  | inl request =>
      exact simulateQ_spec_query (publicImpl kem secret challenge) request
  | inr request =>
      by_cases same : request.ciphertext = challenge
      · simp only [QueryImpl.compose, route, actualImpl, same, ite_true, agreement, pure_bind]
        exact simulateQ_pure _ _
      · simp only [QueryImpl.compose, route, actualImpl, same, ite_false]
        change simulateQ (publicImpl kem secret challenge)
          (((MlKemCCAOracleSpec baseSpec).query (.inr request.ciphertext) :
            OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret)) >>=
              fun (recovered : Option MlKemSharedSecret) =>
                pure (recovered.map (productionHiddenRoot source request.coordinates))) = _
        rw [simulateQ_bind, simulateQ_spec_query,
          publicImpl_other kem secret challenge request.ciphertext same]
        simp only [simulateQ_pure]
        rfl

/-- The complete adaptive program, including any private state in its result, is unchanged. -/
theorem route_complete {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (client : OracleComp (LocalPostSpec baseSpec) Result) :
    simulateQ (publicImpl kem secret challenge) (simulateQ (route source challenge supplied) client) =
      simulateQ (actualImpl source kem secret challenge) client := by
  rw [← QueryImpl.simulateQ_compose, route_interpreter source kem secret challenge supplied agreement]

/-- Any stateful ambient interpreter retains its complete final state after the substitution. -/
theorem route_stateful {Result State : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (client : OracleComp (LocalPostSpec baseSpec) Result)
    (ambient : QueryImpl (unifSpec + baseSpec) (StateT State ProbComp)) (state : State) :
    (simulateQ ambient (simulateQ (publicImpl kem secret challenge)
      (simulateQ (route source challenge supplied) client))).run state =
      (simulateQ ambient (simulateQ (actualImpl source kem secret challenge) client)).run state := by
  rw [route_complete source kem secret challenge supplied agreement]

/-- This exact source input follows the Beacon's original four role-reversed DH calls. -/
def beaconCoordinates (c : Pqxdh.Crypto) (identity prekey oneTime pinned ephemeral : Pqxdh.Bytes) :
    KnownPqxdhRootCoordinates :=
  ⟨⟨c.x25519 prekey pinned, c.x25519_length _ _⟩,
   ⟨c.x25519 (c.xsk identity) ephemeral, c.x25519_length _ _⟩,
   ⟨c.x25519 prekey ephemeral, c.x25519_length _ _⟩,
   ⟨c.x25519 oneTime ephemeral, c.x25519_length _ _⟩⟩

/-- The routed root is the original Beacon root for every supplied ephemeral, without an honest-ephemeral premise. -/
theorem beacon_root_exact (source : FixedHkdfSha512NoSaltSource)
    (identity prekey oneTime pinned ephemeral : Pqxdh.Bytes) (supplied : MlKemSharedSecret) :
    (productionHiddenRoot source (beaconCoordinates source.crypto identity prekey oneTime pinned ephemeral)
      supplied).toList = Pqxdh.beaconRoot source.crypto identity prekey oneTime pinned ephemeral supplied.toList := by
  rfl

/-- A matching private request reuses the supplied secret and issues no ordinary decapsulation request. -/
theorem route_challenge (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (coordinates : KnownPqxdhRootCoordinates) :
    route (baseSpec := baseSpec) source challenge supplied (.inr ⟨challenge, coordinates⟩) =
      pure (some (productionHiddenRoot source coordinates supplied)) := by
  simp only [route, ite_true, pure_bind, Option.map_some]

/-- The complete private protocol context and continuation are internal to the reduction. Only the eventual Boolean is the game observation. -/
structure Protocol (baseSpec : OracleSpec ι) where
  State : Type
  prepare : MlKem768PublicKey → OracleComp (MlKemCCAOracleSpec baseSpec) State
  initialCoordinates : MlKem768PublicKey → MlKem768Ciphertext → State → Option KnownPqxdhRootCoordinates
  resume : MlKem768PublicKey → MlKem768Ciphertext → State → Option RootOutput →
    OracleComp (LocalPostSpec baseSpec) Bool

/-- The initial Server root and every later matching private request use this same supplied secret. -/
noncomputable def reduction
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    OneKeyAdversary kem where
  Context := protocol.State
  preChallenge := protocol.prepare
  postChallenge transcript supplied := simulateQ (route source transcript.ciphertext supplied)
    (protocol.resume transcript.publicKey transcript.ciphertext transcript.context
      ((protocol.initialCoordinates transcript.publicKey transcript.ciphertext transcript.context).map
        (fun coordinates => productionHiddenRoot source coordinates supplied)))

/-- The actual correlated execution uses the encapsulated secret for the initial root and actual private decapsulation thereafter. The ordinary challenger's unused secret sample is retained explicitly. -/
noncomputable def nativeMain
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (protocol : Protocol baseSpec) : OracleComp (unifSpec + baseSpec) Bool := do
  let (publicKey, secretKey) ← kem.keygen
  let state ← simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey)
  let (ciphertext, secret) ← kem.encaps publicKey
  let _unused ← runtime.liftProbComp ($ᵗ MlKemSharedSecret)
  simulateQ (actualImpl source kem secretKey ciphertext)
    (protocol.resume publicKey ciphertext state
      ((protocol.initialCoordinates publicKey ciphertext state).map
        (fun coordinates => productionHiddenRoot source coordinates secret)))

/-- Ordinary perfect correctness discharges routing eligibility on actual generated and encapsulated support, with no honest-target premise supplied by the protocol. -/
theorem native_eq_real
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (protocol : Protocol baseSpec) :
    𝒟[simulateQ (kemAmbientImpl baseImpl)
      (nativeMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)] =
      oneKeyBranch kem (runtimeOfImpl (kemAmbientImpl baseImpl)) (reduction source kem protocol) true := by
  simp only [nativeMain, oneKeyBranch, runtimeOfImpl_evalDist, oneKeyBranchMain, oneKeyPrefix,
    oneKeyFinish, reduction, ite_true, simulateQ_bind, pure_bind, bind_assoc]
  apply EvalDistEq.evalDist_eq
  apply OracleComp.EvalDistEq.bind_congr_of_support
  rintro ⟨publicKey, secretKey⟩ generated
  apply EvalDistEq.bind_right
  intro state
  apply OracleComp.EvalDistEq.bind_congr_of_support
  rintro ⟨ciphertext, secret⟩ encapsulated
  apply EvalDistEq.bind_right
  intro unused
  have agreement := honest_decapsulation_program baseImpl kem functional correct generated encapsulated
  rw [(route_complete source kem secretKey ciphertext secret agreement _).symm]
  exact EvalDistEq.refl _

/-- One uniform secret drives the initial root and every later matching request. The real encapsulation still runs and its secret is unused in this world. -/
noncomputable def randomMain
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (protocol : Protocol baseSpec) : OracleComp (unifSpec + baseSpec) Bool := do
  let (publicKey, secretKey) ← kem.keygen
  let state ← simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey)
  let (ciphertext, _real) ← kem.encaps publicKey
  let supplied ← runtime.liftProbComp ($ᵗ MlKemSharedSecret)
  simulateQ (publicImpl kem secretKey ciphertext) (simulateQ (route source ciphertext supplied)
    (protocol.resume publicKey ciphertext state
      ((protocol.initialCoordinates publicKey ciphertext state).map
        (fun coordinates => productionHiddenRoot source coordinates supplied))))

/-- The correlated random-secret world is exactly the ordinary false branch. -/
theorem random_eq_branch
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    𝒟[simulateQ (kemAmbientImpl baseImpl)
      (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)] =
      oneKeyBranch kem (runtimeOfImpl (kemAmbientImpl baseImpl)) (reduction source kem protocol) false := by
  simp only [randomMain, oneKeyBranch, runtimeOfImpl_evalDist, oneKeyBranchMain, oneKeyPrefix,
    oneKeyFinish, reduction, Bool.false_eq_true, ite_false, publicImpl, pure_bind, bind_assoc]
  rfl

/-- The complete correlated source hop is one ordinary IND-CCA advantage. It replaces the shared secret jointly, not each derived root independently. -/
theorem correlated_indCCA
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (protocol : Protocol baseSpec) :
    (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (reduction source kem protocol).toINDCCA).toReal =
      (simulateQ (kemAmbientImpl baseImpl)
        (nativeMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).boolDistance
        (simulateQ (kemAmbientImpl baseImpl)
          (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) := by
  rw [ProbComp.boolDistance_eq_toReal_boolDist]
  rw [native_eq_real source baseImpl kem functional correct, random_eq_branch]
  apply congrArg ENNReal.toReal
  exact oneKey_indCCAAdvantage_eq_branchDist kem (runtimeOfImpl (kemAmbientImpl baseImpl))
    (reduction source kem protocol)
    (runtimeOfImpl_evalDist_pure _) (runtimeOfImpl_evalDist_bind _)
    (runtimeOfImpl_evalDist_liftProbComp _) (runtimeOfImpl_noFail_bool _)

/-- The source execution has no unused challenger secret draw. All real private decapsulations remain. -/
noncomputable def sourceMain
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (protocol : Protocol baseSpec) : OracleComp (unifSpec + baseSpec) Bool := do
  let (publicKey, secretKey) ← kem.keygen
  let state ← simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey)
  let (ciphertext, secret) ← kem.encaps publicKey
  simulateQ (actualImpl source kem secretKey ciphertext)
    (protocol.resume publicKey ciphertext state
      ((protocol.initialCoordinates publicKey ciphertext state).map
        (fun coordinates => productionHiddenRoot source coordinates secret)))

/-- Erasing only the independent unused challenger draw preserves the evaluated complete protocol decision. -/
theorem source_eq_native
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    𝒟[simulateQ (kemAmbientImpl baseImpl) (sourceMain source kem protocol)] =
      𝒟[simulateQ (kemAmbientImpl baseImpl)
        (nativeMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)] := by
  apply EvalDistEq.evalDist_eq
  simp only [sourceMain, nativeMain, simulateQ_bind, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp]
  apply EvalDistEq.bind_right
  rintro ⟨publicKey, secretKey⟩
  apply EvalDistEq.bind_right
  intro state
  apply EvalDistEq.bind_right
  rintro ⟨ciphertext, secret⟩
  exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- The source execution with no ghost sample has exactly the same coefficient-one ordinary CCA hop. -/
theorem source_correlated_indCCA
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (protocol : Protocol baseSpec) :
    (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (reduction source kem protocol).toINDCCA).toReal =
      (simulateQ (kemAmbientImpl baseImpl) (sourceMain source kem protocol)).boolDistance
        (simulateQ (kemAmbientImpl baseImpl)
          (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) := by
  simp only [ProbComp.boolDistance]
  rw [source_eq_native]
  exact correlated_indCCA source baseImpl kem functional correct protocol

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.honest_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.honest_decapsulation

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.honest_decapsulation_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.honest_decapsulation_program

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.publicImpl_other' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.publicImpl_other

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_interpreter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_interpreter

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_stateful' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_stateful

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.beacon_root_exact' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.beacon_root_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_challenge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.route_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.native_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.native_eq_real

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.random_eq_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.random_eq_branch

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.correlated_indCCA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.correlated_indCCA

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.source_eq_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.source_eq_native

/--
info: 'BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.source_correlated_indCCA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhChallengeSecretRouting.source_correlated_indCCA

end BeaconcryptCore.Computational.PqxdhChallengeSecretRouting
