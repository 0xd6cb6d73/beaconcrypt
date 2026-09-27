import BeaconcryptCore.Computational.PqxdhPrivateRootSource

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
    𝒮[simulateQ (kemAmbientImpl baseImpl) (kem.decaps sk ciphertext)] = pure (some secret) := by
  letI : MeasurableSpace MlKem768PublicKey := ⊤
  letI : DiscreteMeasurableSpace MlKem768PublicKey := ⟨fun _ => by simp⟩
  letI : MeasurableSpace MlKem768Ciphertext := ⊤
  letI : DiscreteMeasurableSpace MlKem768Ciphertext := ⟨fun _ => by simp⟩
  letI : MeasurableSpace MlKemSharedSecret := ⊤
  letI : DiscreteMeasurableSpace MlKemSharedSecret := ⟨fun _ => by simp⟩
  letI : MeasurableSpace KemSK := ⊤
  letI : DiscreteMeasurableSpace KemSK := ⟨fun _ => by simp⟩
  letI : MeasurableSpace (MlKem768PublicKey × KemSK) := ⊤
  letI : DiscreteMeasurableSpace (MlKem768PublicKey × KemSK) := ⟨fun _ => by simp⟩
  letI : MeasurableSpace (MlKem768Ciphertext × MlKemSharedSecret) := ⊤
  letI : DiscreteMeasurableSpace (MlKem768Ciphertext × MlKemSharedSecret) := ⟨fun _ => by simp⟩
  letI : MeasurableSpace (Option MlKemSharedSecret) := ⊤
  letI : DiscreteMeasurableSpace (Option MlKemSharedSecret) := ⟨fun _ => by simp⟩
  let decapsulation := simulateQ (kemAmbientImpl baseImpl) (kem.decaps sk ciphertext)
  have unique : ∀ recovered ∈ support decapsulation, recovered = some secret := by
    intro recovered supported
    exact mlKem768RecipientCorrectness_recovered_eq kem
      (runtimeOfImpl (kemAmbientImpl baseImpl))
      (runtimeOfImpl_evalDist_pure _) (runtimeOfImpl_evalDist_bind _) correct
      (pk := pk) (sk := sk)
      (by simpa only [runtimeOfImpl_evalDist, evalDist_apply_singleton] using
        probOutput_ne_zero_of_mem_support generated)
      (by simpa only [runtimeOfImpl_evalDist, evalDist_apply_singleton] using
        probOutput_ne_zero_of_mem_support encapsulated)
      (by simpa only [runtimeOfImpl_evalDist, evalDist_apply_singleton] using
        probOutput_ne_zero_of_mem_support supported)
  have certain : Pr[= some secret | decapsulation] = 1 :=
    probOutput_eq_one_of_support_subset_singleton (by simp) unique
  apply SPMF.ext
  intro recovered
  change Pr[= recovered | decapsulation] = (pure (some secret) : SPMF _) recovered
  by_cases same : recovered = some secret
  · subst recovered
    simpa only [SPMF.pure_apply_self] using certain
  · have absent : Pr[= recovered | decapsulation] = 0 :=
      (probOutput_eq_zero_iff _ _).mpr (fun supported => same (unique _ supported))
    simpa only [SPMF.pure_apply, if_neg same] using absent

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
  simp only [functional.exact, simulateQ_pure, evalSPMF_pure] at evaluated
  have values := congrArg SPMF.support evaluated
  simp only [SPMF.support_pure, Set.singleton_eq_singleton_iff] at values
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
      · simp only [QueryImpl.compose, route, actualImpl, same, if_true, agreement, pure_bind]
        exact simulateQ_pure _ _
      · simp only [QueryImpl.compose, route, actualImpl, same, if_false]
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
  simp only [route, if_true, pure_bind, Option.map_some]

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
    oneKeyFinish, reduction, if_true, simulateQ_bind, pure_bind, bind_assoc]
  apply evalDist_eq_of_evalSPMF_eq
  apply evalSPMF_bind_congr
  rintro ⟨publicKey, secretKey⟩ generated
  apply evalSPMF_bind_congr'
  intro state
  apply evalSPMF_bind_congr
  rintro ⟨ciphertext, secret⟩ encapsulated
  apply evalSPMF_bind_congr'
  intro unused
  have agreement := honest_decapsulation_program baseImpl kem functional correct generated encapsulated
  apply congrArg evalSPMF
  apply congrArg (simulateQ (kemAmbientImpl baseImpl))
  exact (route_complete source kem secretKey ciphertext secret agreement _).symm

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
    oneKeyFinish, reduction, Bool.false_eq_true, if_false, publicImpl, pure_bind, bind_assoc]
  rfl

/-- The complete correlated source hop is one ordinary IND-CCA advantage. It replaces the shared secret jointly, not each derived root independently. -/
theorem correlated_indCCA
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (protocol : Protocol baseSpec) :
    kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (reduction source kem protocol).toINDCCA =
      (simulateQ (kemAmbientImpl baseImpl)
        (nativeMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).boolDistAdvantage
        (simulateQ (kemAmbientImpl baseImpl)
          (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) := by
  simp only [ProbComp.boolDistAdvantage]
  rw [native_eq_real source baseImpl kem functional correct, random_eq_branch]
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
  apply evalDist_eq_of_evalSPMF_eq
  simp only [sourceMain, nativeMain, simulateQ_bind, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp]
  apply evalSPMF_bind_congr'
  rintro ⟨publicKey, secretKey⟩
  apply evalSPMF_bind_congr'
  intro state
  apply evalSPMF_bind_congr'
  rintro ⟨ciphertext, secret⟩
  apply evalSPMF_ext
  intro decision
  simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- The source execution with no ghost sample has exactly the same coefficient-one ordinary CCA hop. -/
theorem source_correlated_indCCA
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (protocol : Protocol baseSpec) :
    kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (reduction source kem protocol).toINDCCA =
      (simulateQ (kemAmbientImpl baseImpl) (sourceMain source kem protocol)).boolDistAdvantage
        (simulateQ (kemAmbientImpl baseImpl)
          (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) := by
  simp only [ProbComp.boolDistAdvantage]
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
