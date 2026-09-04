import BeaconcryptCore.Computational.PqxdhKemIndCca
import BeaconcryptCore.Computational.PqxdhHiddenRoot

/-!
# One-session PQXDH initializer secrecy composition

This module composes two existing computational endpoints without opening either primitive. The real game generates one honest ML-KEM-768 keypair, runs an unrestricted pre-challenge client, encapsulates once, and uses the encapsulated 32-byte secret as the fifth secret coordinate of BeaconCrypt's exact 192-byte `FF^32 || DH1 || DH2 || DH3 || DH4 || ss` fixed-HKDF-SHA-512/no-salt input. The terminal game retains the same selected 1184-byte public key, 1088-byte challenge ciphertext, arbitrary public context, challenge-blocked decapsulation surface, and typed KDF projection surface, but gives the caller an independent uniform 32-byte root.

The four DH coordinates and public context are arbitrary functions of the pre-challenge state, honest public key, and challenge ciphertext. They may be mutually correlated and correlated with that public transcript. They never receive the real or replacement ML-KEM shared secret. Selection of this honest target public key is an explicit authentication premise; a future composition is intended to discharge it using HB-63 and the symbolic protocol proof, but it is not reproved here.

The proof follows the explicit real-to-uniform-KEM-to-independent-root hybrid. The first hop is exactly one generic VCVio ML-KEM IND-CCA advantage, the second exactly one fixed HKDF-SHA-512 joint-stream advantage, and the final information-theoretic loss is `qRoot / 2^256`. The false KEM branch and hidden-root reduction share one uniform replacement-secret sample, so there is no second sampling hop or duplicate bad-event charge.

Query accounting keeps the source clients' pre/post uniform, base, and logical decapsulation calls separate. Exact challenge-ciphertext attempts remain logical calls but invoke no primitive decapsulation; unequal ciphertexts are forwarded once. For the KDF challenger, callers prove direct transformed-prefix and transformed-post uniform caps using slack allowances `qKemPrefix` and `qKemPost`, whose sum is bounded by `qKemAmbient`; these allowances cover the chosen interpreter's opaque KEM/base work but do not derive or assign any concrete ML-KEM-internal count. The resulting uniform cap is `qKemAmbient + qUPre + qUPost + 32`; root, symmetric, and total stream caps are `qRoot + 1`, `qSym`, and `qRoot + qSym + 1`, with zero untyped stream addresses.

This endpoint does not prove ML-KEM, HKDF, X25519, or Ed25519 internals; KEM cross-key binding; multi-user, multi-session, PPT, QPT, or QROM lifting; Rust, FFI, compiler, or serialization refinement; projection collision freedom; or end-to-end correspondence with ProVerif. HB-54's projection-collision conditioning and the remaining protocol-composition obligations stay separate.
-/

open OracleSpec OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhInitializerSecrecy

open PqxdhKemIndCca PqxdhHiddenRoot PqxdhJointKdf PqxdhJointKdfGame

variable {iota : Type} {baseSpec : OracleSpec iota} {SK : Type}

/-- Interpret the opaque KEM ambient oracle through one fixed stateless handler. -/
noncomputable def runtimeOfImpl
    (impl : QueryImpl (unifSpec + baseSpec) ProbComp) :
    ProbCompRuntime (OracleComp (unifSpec + baseSpec)) where
  toSPMFSemantics :=
    { Sem := ProbComp
      instMonadSem := inferInstance
      interpret := simulateQ' impl
      observe := fun computation => liftM computation }
  toProbCompLift := ProbCompLift.ofMonadLift _

@[simp] theorem runtimeOfImpl_evalDist
    (impl : QueryImpl (unifSpec + baseSpec) ProbComp)
    {alpha : Type} (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (runtimeOfImpl impl).evalDist computation =
      𝒟[simulateQ impl computation] := by
  rfl

@[simp] theorem runtimeOfImpl_liftProbComp
    (impl : QueryImpl (unifSpec + baseSpec) ProbComp)
    {alpha : Type} (computation : ProbComp alpha) :
    (runtimeOfImpl impl).liftProbComp computation =
      OracleComp.liftComp computation (unifSpec + baseSpec) := by
  rfl

/-- The source post phase retains the complete IND-CCA surface and adds only the typed KDF view. -/
abbrev InitializerPostSpec (baseSpec : OracleSpec iota) :=
  MlKemCCAOracleSpec baseSpec + JointKdfViewSpec

/-- Public data fixed by the honest target KEM transcript; the candidate shared secret and root are absent. -/
structure InitializerPublicTranscript (Context : Type) where
  publicKey : MlKem768PublicKey
  ciphertext : MlKem768Ciphertext
  context : Context

/-- One authenticated-honest-target, one-session initializer distinguisher. -/
structure InitializerAdversary
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)) where
  State : Type
  Context : Type
  preChallenge : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec State
  knownCoordinates : State → MlKem768PublicKey → MlKem768Ciphertext →
    KnownPqxdhRootCoordinates
  publicContext : State → MlKem768PublicKey → MlKem768Ciphertext → Context
  main : InitializerPublicTranscript Context → KnownPqxdhRootCoordinates →
    HiddenRootCoordinate → OracleComp (InitializerPostSpec baseSpec) Bool

/-- Production KDF projections are deterministic while the full CCA surface remains available. -/
def initializerPostRealImpl
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)) :
    QueryImpl (InitializerPostSpec baseSpec)
      (OracleComp kem.IND_CCA_oracleSpec)
  | .inl query => liftM (kem.IND_CCA_oracleSpec.query query)
  | .inr query => pure (query.project (productionStream source.crypto query.address))

/-- The KEM reduction derives the exact 192-byte production root from the privately supplied candidate secret. -/
def toKemOneKeyAdversary
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) : OneKeyAdversary kem where
  Context := adversary.State
  preChallenge := adversary.preChallenge
  postChallenge transcript kStar :=
    let known := adversary.knownCoordinates transcript.context
      transcript.publicKey transcript.ciphertext
    let publicContext := adversary.publicContext transcript.context
      transcript.publicKey transcript.ciphertext
    simulateQ (initializerPostRealImpl source kem)
      (adversary.main
        ⟨transcript.publicKey, transcript.ciphertext, publicContext⟩ known
        (productionHiddenRoot source known kStar))

/-- Fixed source branch: `true` uses the honest encapsulated secret and `false` the single ghost-uniform replacement. -/
def initializerKemBranch
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (adversary : InitializerAdversary kem) (b : Bool) : SPMF Bool :=
  oneKeyBranch kem runtime (toKemOneKeyAdversary source kem adversary) b

/-- Fixed interpretation of the KEM's ambient uniform/base surface. -/
def kemAmbientImpl (baseImpl : QueryImpl baseSpec ProbComp) :
    QueryImpl (unifSpec + baseSpec) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + baseImpl

/-- The fixed ambient interpreter is transparent on locally lifted probabilistic work. -/
theorem simulateQ_kemAmbient_liftProbComp
    (baseImpl : QueryImpl baseSpec ProbComp)
    {alpha : Type} (computation : ProbComp alpha) :
    simulateQ (kemAmbientImpl baseImpl)
        (OracleComp.liftComp computation (unifSpec + baseSpec)) =
      computation := by
  unfold kemAmbientImpl
  rw [QueryImpl.simulateQ_add_liftComp_left]
  exact simulateQ_id' computation

/-- `liftM` normal form of `simulateQ_kemAmbient_liftProbComp`. -/
theorem simulateQ_kemAmbient_liftM_ProbComp
    (baseImpl : QueryImpl baseSpec ProbComp)
    {alpha : Type} (computation : ProbComp alpha) :
    simulateQ (kemAmbientImpl baseImpl)
        (liftM computation : OracleComp (unifSpec + baseSpec) alpha) =
      computation := by
  rw [← OracleComp.liftComp_eq_liftM]
  exact simulateQ_kemAmbient_liftProbComp baseImpl computation

/-- Prefix retained by the sampled-prefix KDF reduction after discarding the real encapsulated secret. -/
structure InitializerKdfPrefix
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) where
  publicKey : MlKem768PublicKey
  secretKey : SK
  state : adversary.State
  ciphertext : MlKem768Ciphertext

/-- One key generation, source pre phase, and one honest encapsulation under the fixed ambient interpreter. -/
noncomputable def initializerKdfPrefixProb
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    ProbComp (InitializerKdfPrefix kem adversary) := do
  let (pk, sk) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let state ← simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl sk)
      (adversary.preChallenge pk))
  let (cStar, _kReal) ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps pk)
  return ⟨pk, sk, state, cStar⟩

/-- Interpret ambient KEM work locally while leaving source uniform and typed KDF queries visible. -/
def ambientToJointKdfViewImpl
    (baseImpl : QueryImpl baseSpec ProbComp) :
    QueryImpl (unifSpec + baseSpec)
      (OracleComp JointKdfViewAdversarySpec) :=
  (fun query : unifSpec.Domain =>
    (liftM (JointKdfViewAdversarySpec.query (.inl query)) :
      OracleComp JointKdfViewAdversarySpec (unifSpec.Range query))) +
  (fun query : baseSpec.Domain =>
    (OracleComp.liftComp (baseImpl query) JointKdfViewAdversarySpec :
      OracleComp JointKdfViewAdversarySpec (baseSpec.Range query)))

/-- Challenge-blocked post KEM handler plus the exact typed KDF projection surface. -/
def initializerPostToJointKdfViewImpl
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext) :
    QueryImpl (InitializerPostSpec baseSpec)
      (OracleComp JointKdfViewAdversarySpec)
  | .inl query => simulateQ (ambientToJointKdfViewImpl baseImpl)
      (kem.IND_CCA_postChallengeImpl sk cStar query)
  | .inr query => liftM (JointKdfViewAdversarySpec.query (.inr query))

/-- Post phase seen by the hidden-root hop for one sampled honest KEM transcript. -/
def toHiddenRootAdversary
    {qU qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (sampled : InitializerKdfPrefix kem adversary)
    (uniformBound : ∀ known publicContext root,
      (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
          sampled.secretKey sampled.ciphertext)
        (adversary.main
          ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
        IsJointKdfViewUniformQuery qU)
    (rootBound : ∀ known publicContext root,
      (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
          sampled.secretKey sampled.ciphertext)
        (adversary.main
          ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
        IsHiddenRootDomainQuery qRoot)
    (symmetricBound : ∀ known publicContext root,
      (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
          sampled.secretKey sampled.ciphertext)
        (adversary.main
          ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
        IsHiddenRootSymmetricQuery qSym) :
    HiddenRootSourceAdversary adversary.Context qU qRoot qSym where
  main known publicContext root :=
    simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
      sampled.secretKey sampled.ciphertext)
      (adversary.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)
  uniformQueryBound := uniformBound
  rootQueryBound := rootBound
  symmetricQueryBound := symmetricBound

/-- Exact sampled-prefix and transformed-post budgets used by one concrete KDF reduction. -/
structure InitializerKdfReductionBounds
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (qPrefix qPost qRoot qSym : ℕ) where
  prefixUniform :
    (OracleComp.liftComp (initializerKdfPrefixProb baseImpl kem adversary)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512UniformQuery qPrefix
  postUniform : ∀ (sampled : InitializerKdfPrefix kem adversary)
      (known : KnownPqxdhRootCoordinates) (publicContext : adversary.Context)
      (root : HiddenRootCoordinate),
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (adversary.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
      IsJointKdfViewUniformQuery qPost
  postRoot : ∀ (sampled : InitializerKdfPrefix kem adversary)
      (known : KnownPqxdhRootCoordinates) (publicContext : adversary.Context)
      (root : HiddenRootCoordinate),
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (adversary.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
      IsHiddenRootDomainQuery qRoot
  postSymmetric : ∀ (sampled : InitializerKdfPrefix kem adversary)
      (known : KnownPqxdhRootCoordinates) (publicContext : adversary.Context)
      (root : HiddenRootCoordinate),
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (adversary.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
      IsHiddenRootSymmetricQuery qSym

/-- Specialize the generic hidden-root client at one sampled honest KEM transcript. -/
def sampledHiddenRootAdversary
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym)
    (sampled : InitializerKdfPrefix kem adversary) :
    HiddenRootSourceAdversary adversary.Context qPost qRoot qSym :=
  toHiddenRootAdversary baseImpl kem adversary sampled
    (bounds.postUniform sampled) (bounds.postRoot sampled)
    (bounds.postSymmetric sampled)

/-- The single randomized fixed-HKDF reduction: sample the honest public KEM transcript once, replace its secret once, and run the exact hidden-root reduction. -/
noncomputable def initializerKdfReductionMain
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    OracleComp FixedHkdfSha512JointStreamSpec Bool := do
  let sampled ← OracleComp.liftComp
    (initializerKdfPrefixProb baseImpl kem adversary)
    FixedHkdfSha512JointStreamSpec
  let known := adversary.knownCoordinates sampled.state
    sampled.publicKey sampled.ciphertext
  let publicContext := adversary.publicContext sampled.state
    sampled.publicKey sampled.ciphertext
  hiddenRootReductionMain
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    known publicContext

/-- Proof-erased production-root hybrid body used to align the KEM and KDF presentations. -/
noncomputable def initializerUniformKemCore
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) : ProbComp Bool := do
  let sampled ← initializerKdfPrefixProb baseImpl kem adversary
  let known := adversary.knownCoordinates sampled.state
    sampled.publicKey sampled.ciphertext
  let publicContext := adversary.publicContext sampled.state
    sampled.publicKey sampled.ciphertext
  let hidden ← $ᵗ HiddenRootCoordinate
  simulateQ (jointKdfViewRealImpl source)
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (adversary.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known
        (productionHiddenRoot source known hidden)))

/-- Uniform-KEM hybrid with the production fixed-HKDF root and production KDF projections. -/
noncomputable def initializerUniformKemGame
    {qPrefix qPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) : ProbComp Bool := do
  let sampled ← initializerKdfPrefixProb baseImpl kem adversary
  let known := adversary.knownCoordinates sampled.state
    sampled.publicKey sampled.ciphertext
  let publicContext := adversary.publicContext sampled.state
    sampled.publicKey sampled.ciphertext
  hiddenRootRealGame source
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    known publicContext

/-- The bounded hidden-root packaging erases to the same production-root hybrid body. -/
theorem initializerUniformKemGame_eq_core
    {qPrefix qPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    initializerUniformKemGame source baseImpl kem adversary bounds =
      initializerUniformKemCore source baseImpl kem adversary := by
  rfl

/-- Shared-stream hybrid after replacing fixed HKDF by one lazy random joint-stream oracle. -/
noncomputable def initializerSharedRootGame
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) : ProbComp Bool := do
  let sampled ← initializerKdfPrefixProb baseImpl kem adversary
  let known := adversary.knownCoordinates sampled.state
    sampled.publicKey sampled.ciphertext
  let publicContext := adversary.publicContext sampled.state
    sampled.publicKey sampled.ciphertext
  hiddenRootSharedRandomGame
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    known publicContext

/-- Terminal one-session ideal: preserve the public KEM transcript and both oracle surfaces, but supply an independent uniform root. -/
noncomputable def initializerIndependentRootGame
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) : ProbComp Bool := do
  let sampled ← initializerKdfPrefixProb baseImpl kem adversary
  let known := adversary.knownCoordinates sampled.state
    sampled.publicKey sampled.ciphertext
  let publicContext := adversary.publicContext sampled.state
    sampled.publicKey sampled.ciphertext
  hiddenRootIndependentGame
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    known publicContext

/-- The randomized reduction's fixed-HKDF real run is exactly the uniform-KEM production-root hybrid. -/
theorem initializerKdfReduction_real_eq_uniformKem
    {qPrefix qPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    simulateQ (fixedHkdfSha512JointStreamRealImpl source)
        (initializerKdfReductionMain baseImpl kem adversary bounds) =
      initializerUniformKemGame source baseImpl kem adversary bounds := by
  unfold initializerKdfReductionMain initializerUniformKemGame
  rw [simulateQ_bind]
  have hprefix : simulateQ (fixedHkdfSha512JointStreamRealImpl source)
      (OracleComp.liftComp (initializerKdfPrefixProb baseImpl kem adversary)
        FixedHkdfSha512JointStreamSpec) =
      initializerKdfPrefixProb baseImpl kem adversary := by
    unfold fixedHkdfSha512JointStreamRealImpl
    rw [QueryImpl.simulateQ_add_liftComp_left]
    simp
  rw [hprefix]
  apply bind_congr
  intro sampled
  simpa [fixedHkdfSha512JointStreamRealExp, hiddenRootReduction] using
    (hiddenRootRealGame_eq_fixedHkdfSha512JointStreamRealExp source
      (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
      (adversary.knownCoordinates sampled.state sampled.publicKey
        sampled.ciphertext)
      (adversary.publicContext sampled.state sampled.publicKey
        sampled.ciphertext)).symm

/-- The randomized reduction's fixed-HKDF random run is exactly the shared-root hybrid. -/
theorem initializerKdfReduction_random_eq_sharedRoot
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (simulateQ fixedHkdfSha512JointStreamRandomImpl
        (initializerKdfReductionMain baseImpl kem adversary bounds)).run' ∅ =
      initializerSharedRootGame baseImpl kem adversary bounds := by
  unfold initializerKdfReductionMain initializerSharedRootGame
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have hprefix :
      (simulateQ fixedHkdfSha512JointStreamRandomImpl
        (OracleComp.liftComp (initializerKdfPrefixProb baseImpl kem adversary)
          FixedHkdfSha512JointStreamSpec)).run ∅ =
        (do
          let sampled ← initializerKdfPrefixProb baseImpl kem adversary
          pure (sampled, (∅ : JointKdfRO.QueryCache))) := by
    unfold fixedHkdfSha512JointStreamRandomImpl
    rw [QueryImpl.simulateQ_add_liftComp_left]
    rw [simulateQ_liftTarget]
    simp only [QueryImpl.ofLift_eq_id', simulateQ_id']
    rw [StateT.run_liftM]
  rw [hprefix]
  simp only [bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro sampled
  rfl

/-- Production's KDF-view handler is transparent on a lifted local probabilistic computation. -/
theorem simulateQ_jointKdfViewReal_liftProbComp
    (source : FixedHkdfSha512NoSaltSource)
    {alpha : Type} (computation : ProbComp alpha) :
    simulateQ (jointKdfViewRealImpl source)
        (OracleComp.liftComp computation JointKdfViewAdversarySpec) = computation := by
  unfold jointKdfViewRealImpl
  rw [QueryImpl.simulateQ_compose]
  have hforward :
      simulateQ jointKdfViewForwardImpl
          (OracleComp.liftComp computation JointKdfViewAdversarySpec) =
        OracleComp.liftComp computation FixedHkdfSha512JointStreamSpec := by
    induction computation using OracleComp.inductionOn with
    | pure output => rfl
    | query_bind query rest ih =>
        simp only [OracleComp.liftComp_bind, simulateQ_bind]
        rw [OracleComp.liftComp_query]
        change (do
          let response ← jointKdfViewForwardImpl (.inl query)
          simulateQ jointKdfViewForwardImpl
            (OracleComp.liftComp (rest response) JointKdfViewAdversarySpec)) = _
        simp only [jointKdfViewForwardImpl_uniform]
        rw [OracleComp.liftComp_query]
        apply bind_congr
        exact ih
  rw [hforward]
  unfold fixedHkdfSha512JointStreamRealImpl
  rw [QueryImpl.simulateQ_add_liftComp_left]
  exact simulateQ_id' computation

/-- The local ambient interpreter commutes exactly with the production KDF-view interpreter. -/
theorem simulateQ_ambientToJointKdfView_real
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    {alpha : Type} (computation : OracleComp (unifSpec + baseSpec) alpha) :
    simulateQ (jointKdfViewRealImpl source)
        (simulateQ (ambientToJointKdfViewImpl baseImpl) computation) =
      simulateQ (kemAmbientImpl baseImpl) computation := by
  simp only [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with uniformQuery | baseQuery
  · simp [ambientToJointKdfViewImpl, kemAmbientImpl, jointKdfViewRealImpl,
      fixedHkdfSha512JointStreamRealImpl, jointKdfViewForwardImpl]
  · simpa [ambientToJointKdfViewImpl, kemAmbientImpl] using
      simulateQ_jointKdfViewReal_liftProbComp source (baseImpl baseQuery)

theorem simulateQ_initializerPostRealImpl_left
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (impl : QueryImpl kem.IND_CCA_oracleSpec m)
    (query : kem.IND_CCA_oracleSpec.Domain) :
    simulateQ impl (initializerPostRealImpl source kem (.inl query)) =
      impl query := by
  change simulateQ impl (liftM (kem.IND_CCA_oracleSpec.query query)) = impl query
  exact simulateQ_spec_query impl query

/-- Both hybrid presentations give every post query the same blocked-CCA or production-KDF answer. -/
theorem simulateQ_initializerPost_real_composition
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext)
    {alpha : Type} (computation : OracleComp (InitializerPostSpec baseSpec) alpha) :
    simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_postChallengeImpl sk cStar)
          (simulateQ (initializerPostRealImpl source kem) computation)) =
      simulateQ (jointKdfViewRealImpl source)
        (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
          computation) := by
  simp only [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with ccaQuery | viewQuery
  · rcases ccaQuery with ambientQuery | ciphertext
    · rcases ambientQuery with uniformQuery | baseQuery
      · simp only [QueryImpl.apply_compose, initializerPostToJointKdfViewImpl]
        exact (congrArg (simulateQ (kemAmbientImpl baseImpl))
          (simulateQ_initializerPostRealImpl_left source kem
            (kem.IND_CCA_postChallengeImpl sk cStar)
            (.inl (.inl uniformQuery)))).trans
          (simulateQ_ambientToJointKdfView_real source baseImpl
            (kem.IND_CCA_postChallengeImpl sk cStar
              (.inl (.inl uniformQuery)))).symm
      · simp only [QueryImpl.apply_compose, initializerPostToJointKdfViewImpl]
        exact (congrArg (simulateQ (kemAmbientImpl baseImpl))
          (simulateQ_initializerPostRealImpl_left source kem
            (kem.IND_CCA_postChallengeImpl sk cStar)
            (.inl (.inr baseQuery)))).trans
          (simulateQ_ambientToJointKdfView_real source baseImpl
            (kem.IND_CCA_postChallengeImpl sk cStar
              (.inl (.inr baseQuery)))).symm
    · simp only [QueryImpl.apply_compose, initializerPostToJointKdfViewImpl]
      exact (congrArg (simulateQ (kemAmbientImpl baseImpl))
        (simulateQ_initializerPostRealImpl_left source kem
          (kem.IND_CCA_postChallengeImpl sk cStar) (.inr ciphertext))).trans
        (simulateQ_ambientToJointKdfView_real source baseImpl
          (kem.IND_CCA_postChallengeImpl sk cStar (.inr ciphertext))).symm
  · simp [initializerPostRealImpl, initializerPostToJointKdfViewImpl,
      jointKdfViewRealImpl, fixedHkdfSha512JointStreamRealImpl,
      jointKdfViewForwardImpl]

/-- Explicit common body of the false KEM branch before converting its KDF presentation. -/
noncomputable def initializerKemFalseCore
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) : ProbComp Bool := do
  let (pk, sk) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let state ← simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl sk)
      (adversary.preChallenge pk))
  let (cStar, _kReal) ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps pk)
  let kRand ← $ᵗ MlKemSharedSecret
  simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_postChallengeImpl sk cStar)
      (simulateQ (initializerPostRealImpl source kem)
        (adversary.main
          ⟨pk, cStar, adversary.publicContext state pk cStar⟩
          (adversary.knownCoordinates state pk cStar)
          (productionHiddenRoot source
            (adversary.knownCoordinates state pk cStar) kRand))))

/-- Interpreting the false one-key syntax yields its explicit common body. -/
theorem simulateQ_initializerOneKeyFalse_eq_falseCore
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    simulateQ (kemAmbientImpl baseImpl)
        (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
          (toKemOneKeyAdversary source kem adversary) false) =
      initializerKemFalseCore source baseImpl kem adversary := by
  simp [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish,
    toKemOneKeyAdversary, initializerKemFalseCore,
    runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftM_ProbComp]

/-- The explicit false KEM body and KDF hybrid differ only by the already-proved post-handler presentation. -/
theorem initializerKemFalseCore_eq_uniformKemCore
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    initializerKemFalseCore source baseImpl kem adversary =
      initializerUniformKemCore source baseImpl kem adversary := by
  unfold initializerKemFalseCore initializerUniformKemCore
    initializerKdfPrefixProb
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro pksk
  apply bind_congr
  intro state
  apply bind_congr
  intro encapsulation
  apply bind_congr
  intro kRand
  exact simulateQ_initializerPost_real_composition source baseImpl kem
    pksk.2 encapsulation.1
    (adversary.main
      ⟨pksk.1, encapsulation.1,
        adversary.publicContext state pksk.1 encapsulation.1⟩
      (adversary.knownCoordinates state pksk.1 encapsulation.1)
      (productionHiddenRoot source
        (adversary.knownCoordinates state pksk.1 encapsulation.1) kRand))

/-- The false one-key branch and the production-KDF hybrid share the exact sampled prefix and one replacement-secret draw. -/
theorem initializerKemBranch_false_eq_uniformKemCore
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    initializerKemBranch source kem
        (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary false =
      𝒟[initializerUniformKemCore source baseImpl kem adversary] := by
  unfold initializerKemBranch oneKeyBranch
  rw [runtimeOfImpl_evalDist,
    simulateQ_initializerOneKeyFalse_eq_falseCore,
    initializerKemFalseCore_eq_uniformKemCore]

/-! ## Source-interface query accounting -/

/-- Public-uniform calls made by the source post phase, excluding ambient KEM interpretation. -/
def IsInitializerUniformQuery {iota : Type} :
    (((unifSpec.Domain ⊕ iota) ⊕ MlKem768Ciphertext) ⊕
      JointKdfViewSpec.Domain) → Prop
  | .inl query => IsMlKemUniformQuery query
  | .inr _ => False

/-- Arbitrary base-oracle calls made by the source post phase. -/
def IsInitializerBaseQuery {iota : Type} :
    (((unifSpec.Domain ⊕ iota) ⊕ MlKem768Ciphertext) ⊕
      JointKdfViewSpec.Domain) → Prop
  | .inl query => IsMlKemBaseQuery query
  | .inr _ => False

/-- Logical post-challenge decapsulation calls, including blocked `cStar` attempts. -/
def IsInitializerLogicalDecapsulationQuery {iota : Type} :
    (((unifSpec.Domain ⊕ iota) ⊕ MlKem768Ciphertext) ⊕
      JointKdfViewSpec.Domain) → Prop
  | .inl query => IsMlKemLogicalDecapsulationQuery query
  | .inr _ => False

/-- Typed root-domain KDF projections made by the source post phase. -/
def IsInitializerRootQuery {iota : Type} :
    (((unifSpec.Domain ⊕ iota) ⊕ MlKem768Ciphertext) ⊕
      JointKdfViewSpec.Domain) → Prop
  | .inl _ => False
  | .inr query => IsHiddenRootDomainQuery (.inr query)

/-- Typed symmetric-domain KDF projections made by the source post phase. -/
def IsInitializerSymmetricQuery {iota : Type} :
    (((unifSpec.Domain ⊕ iota) ⊕ MlKem768Ciphertext) ⊕
      JointKdfViewSpec.Domain) → Prop
  | .inl _ => False
  | .inr query => IsHiddenRootSymmetricQuery (.inr query)

noncomputable instance instDecidablePredIsInitializerUniformQuery :
    DecidablePred (@IsInitializerUniformQuery iota) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsInitializerBaseQuery :
    DecidablePred (@IsInitializerBaseQuery iota) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsInitializerLogicalDecapsulationQuery :
    DecidablePred (@IsInitializerLogicalDecapsulationQuery iota) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsInitializerRootQuery :
    DecidablePred (@IsInitializerRootQuery iota) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsInitializerSymmetricQuery :
    DecidablePred (@IsInitializerSymmetricQuery iota) :=
  Classical.decPred _

/-- Exact logical caps on the source clients. Opaque KEM operations and their chosen ambient interpreter are deliberately outside these caps. -/
def InitializerAdversary.MakesAtMostQueries
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : InitializerAdversary kem)
    (qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym : ℕ) : Prop :=
  (∀ pk,
    (adversary.preChallenge pk).IsQueryBoundP IsMlKemUniformQuery qUPre ∧
    (adversary.preChallenge pk).IsQueryBoundP IsMlKemBaseQuery qBPre ∧
    (adversary.preChallenge pk).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDPre) ∧
  (∀ transcript known root,
    (adversary.main transcript known root).IsQueryBoundP
        IsInitializerUniformQuery qUPost ∧
    (adversary.main transcript known root).IsQueryBoundP
        IsInitializerBaseQuery qBPost ∧
    (adversary.main transcript known root).IsQueryBoundP
        IsInitializerLogicalDecapsulationQuery qDPost ∧
    (adversary.main transcript known root).IsQueryBoundP
        IsInitializerRootQuery qRoot ∧
    (adversary.main transcript known root).IsQueryBoundP
        IsInitializerSymmetricQuery qSym)

theorem initializerPostRealImpl_uniform_query_bound_step
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (query : (InitializerPostSpec baseSpec).Domain) :
    (initializerPostRealImpl source kem query).IsQueryBoundP
      IsMlKemUniformQuery
      (if IsInitializerUniformQuery query then 1 else 0) := by
  rcases query with ccaQuery | viewQuery
  · simp only [initializerPostRealImpl, IsInitializerUniformQuery]
    change (liftM (kem.IND_CCA_oracleSpec.query ccaQuery) :
      OracleComp kem.IND_CCA_oracleSpec _).IsQueryBoundP
        IsMlKemUniformQuery (if IsMlKemUniformQuery ccaQuery then 1 else 0)
    rw [OracleComp.isQueryBoundP_query_iff]
    split <;> simp_all
  · simp [initializerPostRealImpl, IsInitializerUniformQuery]

theorem initializerPostRealImpl_base_query_bound_step
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (query : (InitializerPostSpec baseSpec).Domain) :
    (initializerPostRealImpl source kem query).IsQueryBoundP
      IsMlKemBaseQuery
      (if IsInitializerBaseQuery query then 1 else 0) := by
  rcases query with ccaQuery | viewQuery
  · simp only [initializerPostRealImpl, IsInitializerBaseQuery]
    change (liftM (kem.IND_CCA_oracleSpec.query ccaQuery) :
      OracleComp kem.IND_CCA_oracleSpec _).IsQueryBoundP
        IsMlKemBaseQuery (if IsMlKemBaseQuery ccaQuery then 1 else 0)
    rw [OracleComp.isQueryBoundP_query_iff]
    split <;> simp_all
  · simp [initializerPostRealImpl, IsInitializerBaseQuery]

theorem initializerPostRealImpl_decapsulation_query_bound_step
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (query : (InitializerPostSpec baseSpec).Domain) :
    (initializerPostRealImpl source kem query).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery
      (if IsInitializerLogicalDecapsulationQuery query then 1 else 0) := by
  rcases query with ccaQuery | viewQuery
  · simp only [initializerPostRealImpl,
      IsInitializerLogicalDecapsulationQuery]
    change (liftM (kem.IND_CCA_oracleSpec.query ccaQuery) :
      OracleComp kem.IND_CCA_oracleSpec _).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery
        (if IsMlKemLogicalDecapsulationQuery ccaQuery then 1 else 0)
    rw [OracleComp.isQueryBoundP_query_iff]
    split <;> simp_all
  · simp [initializerPostRealImpl,
      IsInitializerLogicalDecapsulationQuery]

/-- Predicate-bound forwarding does not require the arbitrary target base oracle to be sampleable. -/
theorem isQueryBoundP_simulateQ_of_step_noUniform
    {sourceIndex targetIndex : Type}
    {sourceSpec : OracleSpec sourceIndex}
    {targetSpec : OracleSpec targetIndex}
    {alpha : Type}
    {sourcePredicate : sourceIndex → Prop} [DecidablePred sourcePredicate]
    {targetPredicate : targetIndex → Prop} [DecidablePred targetPredicate]
    {impl : QueryImpl sourceSpec (OracleComp targetSpec)}
    {computation : OracleComp sourceSpec alpha} {n : ℕ}
    (hbound : computation.IsQueryBoundP sourcePredicate n)
    (hstepTrue : ∀ query, sourcePredicate query →
      (impl query).IsQueryBoundP targetPredicate 1)
    (hstepFalse : ∀ query, ¬ sourcePredicate query →
      (impl query).IsQueryBoundP targetPredicate 0) :
    (simulateQ impl computation).IsQueryBoundP targetPredicate n := by
  induction computation using OracleComp.inductionOn generalizing n with
  | pure output => simp [simulateQ_pure]
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        monadLift_self]
      have hstep : (impl query).IsQueryBoundP targetPredicate
          (if sourcePredicate query then 1 else 0) := by
        by_cases hquery : sourcePredicate query
        · simpa [hquery] using hstepTrue query hquery
        · simpa [hquery] using hstepFalse query hquery
      have hsum : (if sourcePredicate query then 1 else 0) +
          (if sourcePredicate query then n - 1 else n) = n := by
        grind
      simpa [hsum] using OracleComp.isQueryBoundP_bind hstep
        (fun response _ => ih response (hbound.2 response))

theorem initializerPostRealImpl_uniform_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    {alpha : Type} {computation : OracleComp (InitializerPostSpec baseSpec) alpha}
    {q : ℕ} (hbound : computation.IsQueryBoundP IsInitializerUniformQuery q) :
    (simulateQ (initializerPostRealImpl source kem) computation).IsQueryBoundP
      IsMlKemUniformQuery q := by
  refine isQueryBoundP_simulateQ_of_step_noUniform hbound ?_ ?_
  · intro query hquery
    simpa [hquery] using initializerPostRealImpl_uniform_query_bound_step
      source kem query
  · intro query hquery
    simpa [hquery] using initializerPostRealImpl_uniform_query_bound_step
      source kem query

theorem initializerPostRealImpl_base_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    {alpha : Type} {computation : OracleComp (InitializerPostSpec baseSpec) alpha}
    {q : ℕ} (hbound : computation.IsQueryBoundP IsInitializerBaseQuery q) :
    (simulateQ (initializerPostRealImpl source kem) computation).IsQueryBoundP
      IsMlKemBaseQuery q := by
  refine isQueryBoundP_simulateQ_of_step_noUniform hbound ?_ ?_
  · intro query hquery
    simpa [hquery] using initializerPostRealImpl_base_query_bound_step
      source kem query
  · intro query hquery
    simpa [hquery] using initializerPostRealImpl_base_query_bound_step
      source kem query

theorem initializerPostRealImpl_decapsulation_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    {alpha : Type} {computation : OracleComp (InitializerPostSpec baseSpec) alpha}
    {q : ℕ}
    (hbound : computation.IsQueryBoundP
      IsInitializerLogicalDecapsulationQuery q) :
    (simulateQ (initializerPostRealImpl source kem) computation).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery q := by
  refine isQueryBoundP_simulateQ_of_step_noUniform hbound ?_ ?_
  · intro query hquery
    simpa [hquery] using
      initializerPostRealImpl_decapsulation_query_bound_step source kem query
  · intro query hquery
    simpa [hquery] using
      initializerPostRealImpl_decapsulation_query_bound_step source kem query

/-- The KEM reduction preserves all six pre/post logical source caps; KDF projection calls add no CCA query. -/
theorem toKemOneKeyAdversary_makesAtMostQueries
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    {qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym : ℕ}
    (hbounds : adversary.MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym) :
    (toKemOneKeyAdversary source kem adversary).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost := by
  constructor
  · exact hbounds.1
  · intro transcript kStar
    let known := adversary.knownCoordinates transcript.context
      transcript.publicKey transcript.ciphertext
    let publicContext := adversary.publicContext transcript.context
      transcript.publicKey transcript.ciphertext
    have hpost := hbounds.2
      ⟨transcript.publicKey, transcript.ciphertext, publicContext⟩ known
      (productionHiddenRoot source known kStar)
    exact ⟨initializerPostRealImpl_uniform_query_bound source kem hpost.1,
      initializerPostRealImpl_base_query_bound source kem hpost.2.1,
      initializerPostRealImpl_decapsulation_query_bound source kem hpost.2.2.1⟩

/-- The transformed post handler still blocks the exact challenge ciphertext without any primitive decapsulation. -/
theorem initializerPostToJointKdfViewImpl_challenge
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext) :
    initializerPostToJointKdfViewImpl baseImpl kem sk cStar
        (.inl (.inr cStar)) =
      pure none := by
  simp [initializerPostToJointKdfViewImpl,
    indCCA_postChallengeImpl_challenge]

/-- Every unequal post-challenge ciphertext is forwarded exactly once through the fixed ambient interpreter. -/
theorem initializerPostToJointKdfViewImpl_nonchallenge
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar ciphertext : MlKem768Ciphertext)
    (hne : ciphertext ≠ cStar) :
    initializerPostToJointKdfViewImpl baseImpl kem sk cStar
        (.inl (.inr ciphertext)) =
      simulateQ (ambientToJointKdfViewImpl baseImpl)
        (kem.decaps sk ciphertext) := by
  simp [initializerPostToJointKdfViewImpl,
    indCCA_postChallengeImpl_nonchallenge, hne]

/-! ## Primitive-facing reduction accounting -/

/-- A locally lifted probabilistic prefix emits no complete-stream query. -/
theorem liftProbComp_no_fixedHkdf_stream_query
    {alpha : Type} (computation : ProbComp alpha) :
    (OracleComp.liftComp computation
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512StreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfSha512StreamQuery)
    (hpq := by intro query; simp [IsFixedHkdfSha512StreamQuery,
      SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false computation 0)

/-- A locally lifted probabilistic prefix emits no root-domain stream query. -/
theorem liftProbComp_no_fixedHkdf_root_query
    {alpha : Type} (computation : ProbComp alpha) :
    (OracleComp.liftComp computation
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfRootStreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfRootStreamQuery)
    (hpq := by intro query; simp [IsFixedHkdfRootStreamQuery,
      SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false computation 0)

/-- A locally lifted probabilistic prefix emits no symmetric-domain stream query. -/
theorem liftProbComp_no_fixedHkdf_symmetric_query
    {alpha : Type} (computation : ProbComp alpha) :
    (OracleComp.liftComp computation
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSymmetricStreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfSymmetricStreamQuery)
    (hpq := by intro query; simp [IsFixedHkdfSymmetricStreamQuery,
      SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false computation 0)

/-- A locally lifted probabilistic prefix emits no untyped stream address. -/
theorem liftProbComp_no_fixedHkdf_untyped_stream_query
    {alpha : Type} (computation : ProbComp alpha) :
    (OracleComp.liftComp computation
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512UntypedStreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfSha512UntypedStreamQuery)
    (hpq := by intro query; simp [IsFixedHkdfSha512UntypedStreamQuery,
      SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false computation 0)

/-- Prefix uniform syntax plus source-post/ambient syntax plus the one 32-byte replacement sample. -/
theorem initializerKdfReductionMain_uniform_query_bound
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerKdfReductionMain baseImpl kem adversary bounds).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery (qPrefix + qPost + 32) := by
  unfold initializerKdfReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := qPrefix) (m := qPost + 32)
    bounds.prefixUniform ?_).mono (by omega)
  intro sampled _
  exact hiddenRootReductionMain_uniform_query_bound
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    (adversary.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext)
    (adversary.publicContext sampled.state sampled.publicKey
      sampled.ciphertext)

/-- The sampled prefix adds no root call; the honest hidden-root lookup adds exactly one to `qRoot`. -/
theorem initializerKdfReductionMain_root_query_bound
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerKdfReductionMain baseImpl kem adversary bounds).IsQueryBoundP
      IsFixedHkdfRootStreamQuery (qRoot + 1) := by
  unfold initializerKdfReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qRoot + 1)
    (liftProbComp_no_fixedHkdf_root_query
      (initializerKdfPrefixProb baseImpl kem adversary)) ?_).mono (by omega)
  intro sampled _
  exact hiddenRootReductionMain_root_query_bound
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    (adversary.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext)
    (adversary.publicContext sampled.state sampled.publicKey
      sampled.ciphertext)

/-- The sampled prefix and honest lookup add no symmetric-domain request. -/
theorem initializerKdfReductionMain_symmetric_query_bound
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerKdfReductionMain baseImpl kem adversary bounds).IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery qSym := by
  unfold initializerKdfReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qSym)
    (liftProbComp_no_fixedHkdf_symmetric_query
      (initializerKdfPrefixProb baseImpl kem adversary)) ?_).mono (by omega)
  intro sampled _
  exact hiddenRootReductionMain_symmetric_query_bound
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    (adversary.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext)
    (adversary.publicContext sampled.state sampled.publicKey
      sampled.ciphertext)

/-- Total complete-stream accounting is `qRoot + qSym + 1`; the sampled KEM prefix adds none. -/
theorem initializerKdfReductionMain_stream_query_bound
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerKdfReductionMain baseImpl kem adversary bounds).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery (qRoot + qSym + 1) := by
  unfold initializerKdfReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qRoot + qSym + 1)
    (liftProbComp_no_fixedHkdf_stream_query
      (initializerKdfPrefixProb baseImpl kem adversary)) ?_).mono (by omega)
  intro sampled _
  exact hiddenRootReductionMain_stream_query_bound
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    (adversary.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext)
    (adversary.publicContext sampled.state sampled.publicKey
      sampled.ciphertext)

/-- The complete initializer KDF reduction emits only canonical `INFO_PQ` and `INFO_R` addresses. -/
theorem initializerKdfReductionMain_no_untyped_stream_queries
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerKdfReductionMain baseImpl kem adversary bounds).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  unfold initializerKdfReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (liftProbComp_no_fixedHkdf_untyped_stream_query
      (initializerKdfPrefixProb baseImpl kem adversary)) ?_).mono (by omega)
  intro sampled _
  exact hiddenRootReductionMain_no_untyped_stream_queries
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    (adversary.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext)
    (adversary.publicContext sampled.state sampled.publicKey
      sampled.ciphertext)

/-- Ambient KEM uniform/base work cannot issue a typed root projection. -/
theorem ambientToJointKdfViewImpl_no_root_queries
    (baseImpl : QueryImpl baseSpec ProbComp)
    {alpha : Type} (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (simulateQ (ambientToJointKdfViewImpl baseImpl) computation).IsQueryBoundP
      IsHiddenRootDomainQuery 0 := by
  have hfalse : computation.IsQueryBoundP (fun _ => False) 0 :=
    OracleComp.isQueryBoundP_false computation 0
  refine isQueryBoundP_simulateQ_of_step_noUniform hfalse ?_ ?_
  · intro query hquery
    exact hquery.elim
  · intro query _
    rcases query with uniformQuery | baseQuery
    · change (liftM (JointKdfViewAdversarySpec.query (.inl uniformQuery)) :
        OracleComp JointKdfViewAdversarySpec _).IsQueryBoundP
          IsHiddenRootDomainQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [IsHiddenRootDomainQuery]
    · exact OracleComp.IsQueryBoundP.liftComp_subSpec
        (spec := unifSpec) (superSpec := JointKdfViewAdversarySpec)
        (p := fun _ => False) (q := IsHiddenRootDomainQuery)
        (hpq := by intro randomQuery; simp [IsHiddenRootDomainQuery,
          SubSpec.onQuery])
        (OracleComp.isQueryBoundP_false (baseImpl baseQuery) 0)

/-- Ambient KEM uniform/base work cannot issue a typed symmetric projection. -/
theorem ambientToJointKdfViewImpl_no_symmetric_queries
    (baseImpl : QueryImpl baseSpec ProbComp)
    {alpha : Type} (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (simulateQ (ambientToJointKdfViewImpl baseImpl) computation).IsQueryBoundP
      IsHiddenRootSymmetricQuery 0 := by
  have hfalse : computation.IsQueryBoundP (fun _ => False) 0 :=
    OracleComp.isQueryBoundP_false computation 0
  refine isQueryBoundP_simulateQ_of_step_noUniform hfalse ?_ ?_
  · intro query hquery
    exact hquery.elim
  · intro query _
    rcases query with uniformQuery | baseQuery
    · change (liftM (JointKdfViewAdversarySpec.query (.inl uniformQuery)) :
        OracleComp JointKdfViewAdversarySpec _).IsQueryBoundP
          IsHiddenRootSymmetricQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [IsHiddenRootSymmetricQuery]
    · exact OracleComp.IsQueryBoundP.liftComp_subSpec
        (spec := unifSpec) (superSpec := JointKdfViewAdversarySpec)
        (p := fun _ => False) (q := IsHiddenRootSymmetricQuery)
        (hpq := by intro randomQuery; simp [IsHiddenRootSymmetricQuery,
          SubSpec.onQuery])
        (OracleComp.isQueryBoundP_false (baseImpl baseQuery) 0)

theorem initializerPostToJointKdfViewImpl_root_query_bound_step
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext)
    (query : (InitializerPostSpec baseSpec).Domain) :
    (initializerPostToJointKdfViewImpl baseImpl kem sk cStar query).IsQueryBoundP
      IsHiddenRootDomainQuery
      (if IsInitializerRootQuery query then 1 else 0) := by
  rcases query with ccaQuery | viewQuery
  · simp only [initializerPostToJointKdfViewImpl, IsInitializerRootQuery,
      if_false]
    exact ambientToJointKdfViewImpl_no_root_queries baseImpl
      (kem.IND_CCA_postChallengeImpl sk cStar ccaQuery)
  · simp only [initializerPostToJointKdfViewImpl, IsInitializerRootQuery]
    by_cases hroot : IsHiddenRootDomainQuery (.inr viewQuery)
    · rw [if_pos hroot]
      change (liftM (JointKdfViewAdversarySpec.query (.inr viewQuery)) :
        OracleComp JointKdfViewAdversarySpec _).IsQueryBoundP
          IsHiddenRootDomainQuery 1
      exact (OracleComp.isQueryBoundP_query_iff
        IsHiddenRootDomainQuery (.inr viewQuery) 1).2 (by simp [hroot])
    · rw [if_neg hroot]
      change (liftM (JointKdfViewAdversarySpec.query (.inr viewQuery)) :
        OracleComp JointKdfViewAdversarySpec _).IsQueryBoundP
          IsHiddenRootDomainQuery 0
      exact (OracleComp.isQueryBoundP_query_iff
        IsHiddenRootDomainQuery (.inr viewQuery) 0).2 (by simpa)

theorem initializerPostToJointKdfViewImpl_symmetric_query_bound_step
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext)
    (query : (InitializerPostSpec baseSpec).Domain) :
    (initializerPostToJointKdfViewImpl baseImpl kem sk cStar query).IsQueryBoundP
      IsHiddenRootSymmetricQuery
      (if IsInitializerSymmetricQuery query then 1 else 0) := by
  rcases query with ccaQuery | viewQuery
  · simp only [initializerPostToJointKdfViewImpl,
      IsInitializerSymmetricQuery, if_false]
    exact ambientToJointKdfViewImpl_no_symmetric_queries baseImpl
      (kem.IND_CCA_postChallengeImpl sk cStar ccaQuery)
  · simp only [initializerPostToJointKdfViewImpl,
      IsInitializerSymmetricQuery]
    by_cases hsym : IsHiddenRootSymmetricQuery (.inr viewQuery)
    · rw [if_pos hsym]
      change (liftM (JointKdfViewAdversarySpec.query (.inr viewQuery)) :
        OracleComp JointKdfViewAdversarySpec _).IsQueryBoundP
          IsHiddenRootSymmetricQuery 1
      exact (OracleComp.isQueryBoundP_query_iff
        IsHiddenRootSymmetricQuery (.inr viewQuery) 1).2 (by simp [hsym])
    · rw [if_neg hsym]
      change (liftM (JointKdfViewAdversarySpec.query (.inr viewQuery)) :
        OracleComp JointKdfViewAdversarySpec _).IsQueryBoundP
          IsHiddenRootSymmetricQuery 0
      exact (OracleComp.isQueryBoundP_query_iff
        IsHiddenRootSymmetricQuery (.inr viewQuery) 0).2 (by simpa)

/-- Challenge blocking and ambient KEM interpretation preserve the source root-domain cap exactly. -/
theorem initializerPostToJointKdfViewImpl_root_query_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext)
    {alpha : Type} {computation : OracleComp (InitializerPostSpec baseSpec) alpha}
    {qRoot : ℕ}
    (hbound : computation.IsQueryBoundP IsInitializerRootQuery qRoot) :
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
      computation).IsQueryBoundP IsHiddenRootDomainQuery qRoot := by
  refine isQueryBoundP_simulateQ_of_step_noUniform hbound ?_ ?_
  · intro query hquery
    simpa [hquery] using
      initializerPostToJointKdfViewImpl_root_query_bound_step
        baseImpl kem sk cStar query
  · intro query hquery
    simpa [hquery] using
      initializerPostToJointKdfViewImpl_root_query_bound_step
        baseImpl kem sk cStar query

/-- Challenge blocking and ambient KEM interpretation preserve the source symmetric-domain cap exactly. -/
theorem initializerPostToJointKdfViewImpl_symmetric_query_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext)
    {alpha : Type} {computation : OracleComp (InitializerPostSpec baseSpec) alpha}
    {qSym : ℕ}
    (hbound : computation.IsQueryBoundP IsInitializerSymmetricQuery qSym) :
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
      computation).IsQueryBoundP IsHiddenRootSymmetricQuery qSym := by
  refine isQueryBoundP_simulateQ_of_step_noUniform hbound ?_ ?_
  · intro query hquery
    simpa [hquery] using
      initializerPostToJointKdfViewImpl_symmetric_query_bound_step
        baseImpl kem sk cStar query
  · intro query hquery
    simpa [hquery] using
      initializerPostToJointKdfViewImpl_symmetric_query_bound_step
        baseImpl kem sk cStar query

/-- Records source caps and caller-supplied slack allowances for uniform syntax induced by the chosen KEM/base interpreter. The addends are direct proof obligations, not derived primitive-internal counts. -/
structure InitializerExplicitReductionBounds
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ) where
  sourceQueries : adversary.MakesAtMostQueries
    qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym
  ambientTotal : qKemPrefix + qKemPost ≤ qKemAmbient
  prefixUniform :
    (OracleComp.liftComp (initializerKdfPrefixProb baseImpl kem adversary)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512UniformQuery (qKemPrefix + qUPre)
  postUniform : ∀ (sampled : InitializerKdfPrefix kem adversary)
      (known : KnownPqxdhRootCoordinates) (publicContext : adversary.Context)
      (root : HiddenRootCoordinate),
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (adversary.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
      IsJointKdfViewUniformQuery (qKemPost + qUPost)

/-- Derive the stated typed KDF-domain upper bounds from the source bounds; only the uniform ambient split remains an explicit interpretation budget. -/
def InitializerExplicitReductionBounds.toKdfBounds
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    {source : FixedHkdfSha512NoSaltSource}
    {baseImpl : QueryImpl baseSpec ProbComp}
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    {adversary : InitializerAdversary kem}
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    InitializerKdfReductionBounds baseImpl kem adversary
      (qKemPrefix + qUPre) (qKemPost + qUPost) qRoot qSym where
  prefixUniform := bounds.prefixUniform
  postUniform := bounds.postUniform
  postRoot sampled known publicContext root :=
    initializerPostToJointKdfViewImpl_root_query_bound baseImpl kem
      sampled.secretKey sampled.ciphertext
      (bounds.sourceQueries.2
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root).2.2.2.1
  postSymmetric sampled known publicContext root :=
    initializerPostToJointKdfViewImpl_symmetric_query_bound baseImpl kem
      sampled.secretKey sampled.ciphertext
      (bounds.sourceQueries.2
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root).2.2.2.2

/-- The one sampled-prefix fixed-HKDF distinguisher with its exact public uniform and stream caps. -/
noncomputable def initializerKdfReduction
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    FixedHkdfSha512JointStreamAdversary
      (qKemAmbient + qUPre + qUPost + 32) (qRoot + qSym + 1) where
  main := initializerKdfReductionMain baseImpl kem adversary bounds.toKdfBounds
  uniformQueryBound :=
    (initializerKdfReductionMain_uniform_query_bound baseImpl kem adversary
      bounds.toKdfBounds).mono (by
        have hambient := bounds.ambientTotal
        omega)
  streamQueryBound := initializerKdfReductionMain_stream_query_bound
    baseImpl kem adversary bounds.toKdfBounds

/-- The primitive-facing uniform cap is the supplied ambient slack plus both source-client caps plus the owned 32-byte replacement sample. -/
theorem initializerKdfReduction_uniform_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerKdfReduction source baseImpl kem adversary bounds).main.IsQueryBoundP
      IsFixedHkdfSha512UniformQuery
        (qKemAmbient + qUPre + qUPost + 32) :=
  (initializerKdfReduction source baseImpl kem adversary bounds).uniformQueryBound

/-- The primitive-facing complete-stream cap is `qRoot + qSym + 1`. -/
theorem initializerKdfReduction_stream_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerKdfReduction source baseImpl kem adversary bounds).main.IsQueryBoundP
      IsFixedHkdfSha512StreamQuery (qRoot + qSym + 1) :=
  (initializerKdfReduction source baseImpl kem adversary bounds).streamQueryBound

/-- The complete fixed-HKDF challenger-facing cap is the sum of its separate uniform and complete-stream caps. -/
theorem initializerKdfReduction_totalQueryBound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerKdfReduction source baseImpl kem adversary bounds).main.IsTotalQueryBound
      ((qKemAmbient + qUPre + qUPost + 32) + (qRoot + qSym + 1)) :=
  (initializerKdfReduction source baseImpl kem adversary bounds).totalQueryBound

/-- The packaged reduction retains the exact `qRoot + 1` root-domain cap. -/
theorem initializerKdfReduction_root_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerKdfReduction source baseImpl kem adversary bounds).main.IsQueryBoundP
      IsFixedHkdfRootStreamQuery (qRoot + 1) :=
  initializerKdfReductionMain_root_query_bound baseImpl kem adversary
    bounds.toKdfBounds

/-- The packaged reduction retains the exact `qSym` symmetric-domain cap. -/
theorem initializerKdfReduction_symmetric_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerKdfReduction source baseImpl kem adversary bounds).main.IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery qSym :=
  initializerKdfReductionMain_symmetric_query_bound baseImpl kem adversary
    bounds.toKdfBounds

/-- The packaged reduction uses no untyped stream address. -/
theorem initializerKdfReduction_no_untyped_stream_queries
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerKdfReduction source baseImpl kem adversary bounds).main.IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 :=
  initializerKdfReductionMain_no_untyped_stream_queries baseImpl kem adversary
    bounds.toKdfBounds

/-! ## Exact hybrids and composed advantage -/

/-- The source real game uses the encapsulated secret as the fifth production root coordinate; the branch-normalization ghost sample is never exposed. -/
noncomputable def initializerRealGame
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl)
    (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
      (toKemOneKeyAdversary source kem adversary) true)

/-- The source real game and terminal independent-root game define the one-session initializer advantage. -/
noncomputable def initializerSecrecyAdvantage
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) : ℝ :=
  (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
    (initializerIndependentRootGame baseImpl kem adversary bounds.toKdfBounds)

/-- The concrete ambient runtime evaluates pure computations exactly. -/
theorem runtimeOfImpl_evalDist_pure
    (impl : QueryImpl (unifSpec + baseSpec) ProbComp)
    {alpha : Type} (output : alpha) :
    (runtimeOfImpl impl).evalDist
        (pure output : OracleComp (unifSpec + baseSpec) alpha) =
      pure output := by
  simp

/-- The concrete ambient runtime distributes exactly over sequential composition. -/
theorem runtimeOfImpl_evalDist_bind
    (impl : QueryImpl (unifSpec + baseSpec) ProbComp)
    {alpha beta : Type}
    (computation : OracleComp (unifSpec + baseSpec) alpha)
    (continuation : alpha → OracleComp (unifSpec + baseSpec) beta) :
    (runtimeOfImpl impl).evalDist (computation >>= continuation) =
      (runtimeOfImpl impl).evalDist computation >>= fun output =>
        (runtimeOfImpl impl).evalDist (continuation output) := by
  simp [runtimeOfImpl_evalDist, simulateQ_bind]

/-- The concrete ambient runtime observes its explicitly lifted probabilistic samples exactly. -/
theorem runtimeOfImpl_evalDist_liftProbComp
    (baseImpl : QueryImpl baseSpec ProbComp)
    {alpha : Type} (computation : ProbComp alpha) :
    (runtimeOfImpl (kemAmbientImpl baseImpl)).evalDist
        ((runtimeOfImpl (kemAmbientImpl baseImpl)).liftProbComp computation) =
      𝒟[computation] := by
  rw [runtimeOfImpl_liftProbComp, runtimeOfImpl_evalDist,
    simulateQ_kemAmbient_liftProbComp]

/-- The fixed ProbComp interpreter is total on every Boolean computation. -/
theorem runtimeOfImpl_noFail_bool
    (impl : QueryImpl (unifSpec + baseSpec) ProbComp)
    (computation : OracleComp (unifSpec + baseSpec) Bool) :
    Pr[= true | (runtimeOfImpl impl).evalDist computation] +
      Pr[= false | (runtimeOfImpl impl).evalDist computation] = 1 := by
  change Pr[= true | simulateQ impl computation] +
    Pr[= false | simulateQ impl computation] = 1
  exact probOutput_true_add_false_of_neverFail

/-- The fixed true branch is exactly the evaluation distribution of the source real game. -/
theorem initializerKemBranch_true_eq_real
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    initializerKemBranch source kem
        (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary true =
      𝒟[initializerRealGame source baseImpl kem adversary] := by
  rfl

/-- The fixed false branch is exactly the evaluation distribution of the uniform-KEM KDF hybrid. -/
theorem initializerKemBranch_false_eq_uniformKemGame
    {qPrefix qPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    initializerKemBranch source kem
        (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary false =
      𝒟[initializerUniformKemGame source baseImpl kem adversary bounds] := by
  rw [initializerKemBranch_false_eq_uniformKemCore,
    initializerUniformKemGame_eq_core]

/-- Replacing the honest KEM secret by the single uniform coordinate costs exactly one generic IND-CCA advantage. -/
theorem initializerReal_uniformKem_advantage_eq_indCCA
    {qPrefix qPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
        (initializerUniformKemGame source baseImpl kem adversary bounds) =
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (toKemOneKeyAdversary source kem adversary).toINDCCA := by
  have hcca := oneKey_indCCAAdvantage_eq_branchDist kem
    (runtimeOfImpl (kemAmbientImpl baseImpl))
    (toKemOneKeyAdversary source kem adversary)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl baseImpl))
  change kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (toKemOneKeyAdversary source kem adversary).toINDCCA =
    SPMF.boolDistAdvantage
      (initializerKemBranch source kem
        (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary true)
      (initializerKemBranch source kem
        (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary false) at hcca
  rw [initializerKemBranch_true_eq_real,
    initializerKemBranch_false_eq_uniformKemGame source baseImpl kem
      adversary bounds] at hcca
  change SPMF.boolDistAdvantage
      𝒟[initializerRealGame source baseImpl kem adversary]
      𝒟[initializerUniformKemGame source baseImpl kem adversary bounds] = _
  exact hcca.symm

/-- Sampling the public KEM prefix before the hidden-root game preserves the pointwise `qRoot / 2^256` bound. -/
theorem tvDist_initializerSharedRoot_independentRoot_le
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    tvDist (initializerSharedRootGame baseImpl kem adversary bounds)
        (initializerIndependentRootGame baseImpl kem adversary bounds) ≤
      ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  unfold initializerSharedRootGame initializerIndependentRootGame
  apply tvDist_bind_left_le_const'
  intro sampled
  exact tvDist_hiddenRootSharedRandomGame_independentGame_le
    (sampledHiddenRootAdversary baseImpl kem adversary bounds sampled)
    (adversary.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext)
    (adversary.publicContext sampled.state sampled.publicKey
      sampled.ciphertext)

/-- Boolean distinguishing after the sampled prefix is bounded by the same hidden-root guess term. -/
theorem initializerSharedRoot_independentRoot_advantage_le
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem adversary
      qPrefix qPost qRoot qSym) :
    (initializerSharedRootGame baseImpl kem adversary bounds).boolDistAdvantage
        (initializerIndependentRootGame baseImpl kem adversary bounds) ≤
      ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  have houtput := abs_probOutput_toReal_sub_le_tvDist
    (initializerSharedRootGame baseImpl kem adversary bounds)
    (initializerIndependentRootGame baseImpl kem adversary bounds)
  exact (show
    (initializerSharedRootGame baseImpl kem adversary bounds).boolDistAdvantage
        (initializerIndependentRootGame baseImpl kem adversary bounds) ≤
      tvDist (initializerSharedRootGame baseImpl kem adversary bounds)
        (initializerIndependentRootGame baseImpl kem adversary bounds) by
      simpa [ProbComp.boolDistAdvantage] using houtput).trans
    (tvDist_initializerSharedRoot_independentRoot_le baseImpl kem adversary
      bounds)

/-- The uniform-KEM production-to-shared-root hop is exactly one fixed-HKDF joint-stream advantage of the sampled-prefix reduction. -/
theorem initializerUniformKem_sharedRoot_advantage_eq_fixedHkdf
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializerUniformKemGame source baseImpl kem adversary
        bounds.toKdfBounds).boolDistAdvantage
      (initializerSharedRootGame baseImpl kem adversary bounds.toKdfBounds) =
    fixedHkdfSha512JointStreamAdvantage source
      (initializerKdfReduction source baseImpl kem adversary bounds) := by
  unfold fixedHkdfSha512JointStreamAdvantage
    fixedHkdfSha512JointStreamRealExp
    fixedHkdfSha512JointStreamRandomExp initializerKdfReduction
  rw [initializerKdfReduction_real_eq_uniformKem,
    initializerKdfReduction_random_eq_sharedRoot]

/-- The KEM reduction inherits the source's exact pre/post uniform, base, and logical-decapsulation caps. -/
theorem initializerKemReduction_makesAtMostQueries
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (toKemOneKeyAdversary source kem adversary).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost :=
  toKemOneKeyAdversary_makesAtMostQueries source kem adversary
    bounds.sourceQueries

/-- At most `qDPost` post-challenge calls are primitive-forwardable; an exact `cStar` attempt remains logical but is blocked. -/
theorem initializerKemReduction_post_unblockedDecapsulationQueryBound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym)
    (transcript : MlKemChallengeTranscript
      (toKemOneKeyAdversary source kem adversary).Context)
    (kStar : MlKemSharedSecret) :
    ((toKemOneKeyAdversary source kem adversary).postChallenge
      transcript kStar).IsQueryBoundP
        (IsMlKemUnblockedDecapsulationQuery transcript.ciphertext) qDPost :=
  OneKeyAdversary.post_unblockedDecapsulationQueryBound
    (toKemOneKeyAdversary source kem adversary)
    (initializerKemReduction_makesAtMostQueries source baseImpl kem
      adversary bounds) transcript kStar

/-- One-session KEM-to-independent-root initializer composition.

The true-to-false hop charges one ML-KEM IND-CCA advantage, the production-to-shared-stream hop charges one fixed HKDF-SHA-512/no-salt joint-stream advantage, and the shared-to-independent-root hop charges exactly `qRoot / 2^256`. There is no factor two, field guess, or duplicated bad-event term.
-/
theorem initializerSecrecyAdvantage_le
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem)
    (bounds : InitializerExplicitReductionBounds source baseImpl kem adversary
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    initializerSecrecyAdvantage source baseImpl kem adversary bounds ≤
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
          (toKemOneKeyAdversary source kem adversary).toINDCCA +
        fixedHkdfSha512JointStreamAdvantage source
          (initializerKdfReduction source baseImpl kem adversary bounds) +
        ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  have hkem := initializerReal_uniformKem_advantage_eq_indCCA
    source baseImpl kem adversary bounds.toKdfBounds
  have hkdf := initializerUniformKem_sharedRoot_advantage_eq_fixedHkdf
    source baseImpl kem adversary bounds
  have hguess := initializerSharedRoot_independentRoot_advantage_le
    baseImpl kem adversary bounds.toKdfBounds
  unfold initializerSecrecyAdvantage
  calc
    (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
        (initializerIndependentRootGame baseImpl kem adversary
          bounds.toKdfBounds) ≤
      (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
          (initializerUniformKemGame source baseImpl kem adversary
            bounds.toKdfBounds) +
        (initializerUniformKemGame source baseImpl kem adversary
          bounds.toKdfBounds).boolDistAdvantage
          (initializerIndependentRootGame baseImpl kem adversary
            bounds.toKdfBounds) :=
      ProbComp.boolDistAdvantage_triangle _ _ _
    _ ≤ (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
          (initializerUniformKemGame source baseImpl kem adversary
            bounds.toKdfBounds) +
        ((initializerUniformKemGame source baseImpl kem adversary
          bounds.toKdfBounds).boolDistAdvantage
            (initializerSharedRootGame baseImpl kem adversary
              bounds.toKdfBounds) +
          (initializerSharedRootGame baseImpl kem adversary
            bounds.toKdfBounds).boolDistAdvantage
            (initializerIndependentRootGame baseImpl kem adversary
              bounds.toKdfBounds)) := by
      gcongr
      exact ProbComp.boolDistAdvantage_triangle _ _ _
    _ ≤ kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
          (toKemOneKeyAdversary source kem adversary).toINDCCA +
        fixedHkdfSha512JointStreamAdvantage source
          (initializerKdfReduction source baseImpl kem adversary bounds) +
        ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
      rw [hkem, hkdf]
      linarith

/--
info: 'BeaconcryptCore.Computational.PqxdhInitializerSecrecy.initializerSecrecyAdvantage_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms initializerSecrecyAdvantage_le

/--
info: 'BeaconcryptCore.Computational.PqxdhInitializerSecrecy.initializerKdfReduction_no_untyped_stream_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms initializerKdfReduction_no_untyped_stream_queries

/--
info: 'BeaconcryptCore.Computational.PqxdhInitializerSecrecy.initializerPostToJointKdfViewImpl_challenge' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms initializerPostToJointKdfViewImpl_challenge

end BeaconcryptCore.Computational.PqxdhInitializerSecrecy
