import BeaconcryptCore.Computational.PqxdhEd25519EufCma
import BeaconcryptCore.Computational.PqxdhKemIndCca

/-!
# Stateful Phase-1 retained writer and forgery reduction

This module defines the privately correlated, source-ordered Phase-1 prefix for an Ed25519 field-origin reduction. Local ML-KEM prechallenge interpretation preserves the complete retained tail: the incoming private prekey state, the generated private one-time state, the prekey/one-time/PQ signing order, the adaptive selected candidate, and selector continuation state. The exact signing writer equality retains every message and its actual returned signature together with that full protocol result.

Ed25519, ML-KEM-768, HKDF-SHA-512, X25519, ChaCha20-Poly1305, and BLAKE2b-512 implementations are treated as perfect implementations of their stated primitive contracts; this module proves no primitive internals. The structural writer and routing equalities require no cryptographic security premise. Generator-order interchange, protocol correlations across later phases, source/ideal semantic correspondence, and initialized-chain/KDF composition remain separate protocol proof obligations, rather than primitive assumptions.
-/

open OracleSpec OracleComp ENNReal MeasureTheory

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma

open PqxdhEd25519EufCma PqxdhKemIndCca

abbrev TargetKemPublicKey := PqxdhKemIndCca.MlKem768PublicKey
abbrev Phase1SigningSpec := Pqxdh.Bytes →ₒ Ed25519Signature

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK : Type}

/-- Honest prekey generation retains its correlated private result outside the public transcript. -/
structure PrivatePrekey (Private : Type) where
  publicKey : X25519PublicKey
  privateState : Private

/-- Honest one-time-key generation retains its correlated private result outside the public transcript. -/
structure PrivateOneTime (Private : Type) where
  publicKey : X25519PublicKey
  privateState : Private

/-- Source-shaped honest material setup. Its callbacks receive no identity secret key or locally generated KEM secret key, and public context depends only on public inputs. -/
structure StatefulPhase1Setup (baseSpec : OracleSpec iota) where
  PrivatePre : Type
  PrivateOne : Type
  Context : Type
  prekey : Ed25519PublicKey → OracleComp (unifSpec + baseSpec)
    (PrivatePrekey PrivatePre)
  oneTime : Ed25519PublicKey → PrivatePrekey PrivatePre → TargetKemPublicKey →
    OracleComp (unifSpec + baseSpec) (PrivateOneTime PrivateOne)
  publicContext : Ed25519PublicKey → X25519PublicKey → TargetKemPublicKey →
    X25519PublicKey → Context

/-- A selector receives only the public signed bundle; its continuation state stays distinct from public context. -/
structure StatefulPhase1Selector
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (Context : Type) where
  State : Type
  main : Phase1PublicTranscript Context →
    OracleComp kem.IND_CCA_oracleSpec (Phase1Candidate × State)

/-- The selector at the concrete CCA surface, avoiding opaque abbreviation casts in later routing equalities. -/
def StatefulPhase1Selector.mainConcrete
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    {Context : Type} (selector : StatefulPhase1Selector kem Context)
    (transcript : Phase1PublicTranscript Context) :
    OracleComp ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret))
      (Phase1Candidate × selector.State) :=
  selector.main transcript

/-- The selected KEM public key is installed by construction, never by an external honest-selection equality. -/
def setupMaterial (setup : StatefulPhase1Setup baseSpec)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) (after : PrivateOneTime setup.PrivateOne) :
    Phase1Material setup.Context where
  prekey := before.publicKey
  oneTime := after.publicKey
  pqKey := target
  context := setup.publicContext identity before.publicKey target after.publicKey

@[simp] theorem setupMaterial_pqKey (setup : StatefulPhase1Setup baseSpec)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) (after : PrivateOneTime setup.PrivateOne) :
    (setupMaterial setup identity before target after).pqKey = target := by
  rfl

/-- Directly embed the CCA surface as the left side of the signing-extended surface. -/
def phase1CcaLiftImpl : QueryImpl
    ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret))
    (OracleComp (((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) +
        Phase1SigningSpec)) :=
  fun query => liftM (((((unifSpec + baseSpec) +
    (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) +
      Phase1SigningSpec).query (.inl query)))

def phase1CcaLift {alpha : Type}
    (computation : OracleComp ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) alpha) :
    OracleComp (((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) +
        Phase1SigningSpec) alpha :=
  simulateQ phase1CcaLiftImpl computation

/-- A signing-interface call at the explicit right summand of the CCA-plus-signing surface. -/
def phase1SigningQuery (message : Pqxdh.Bytes) :
    OracleComp (((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) +
        Phase1SigningSpec) Ed25519Signature :=
  liftM (((((unifSpec + baseSpec) +
    (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) +
      Phase1SigningSpec).query (.inr message)))

/-- The same signing call after the local CCA interpreter has removed the decapsulation layer. -/
def phase1ForwardSigningQuery (message : Pqxdh.Bytes) :
    OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      Ed25519Signature :=
  liftM ((((unifSpec + baseSpec) + Phase1SigningSpec).query (.inr message)))

/-- The locally generated `sk` is not passed to setup or selector callbacks and is not returned as a dedicated result field; it stays closed over by the local CCA interpreter. -/
structure StatefulPhase1Result
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) where
  identity : Ed25519PublicKey
  target : TargetKemPublicKey
  before : PrivatePrekey setup.PrivatePre
  after : PrivateOneTime setup.PrivateOne
  preSignature : Ed25519Signature
  oneSignature : Ed25519Signature
  pqSignature : Ed25519Signature
  candidate : Phase1Candidate
  continuation : selector.State

def StatefulPhase1Result.material
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) : Phase1Material setup.Context :=
  setupMaterial setup result.identity result.before result.target result.after

def StatefulPhase1Result.transcript
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) : Phase1PublicTranscript setup.Context :=
  honestPhase1Transcript result.identity result.material result.preSignature
    result.oneSignature result.pqSignature

/-- Forget only private setup and continuation state for the existing pointwise field-origin classifier. -/
def StatefulPhase1Result.toShared
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) : Phase1SharedResult setup.Context :=
  ⟨result.identity, ⟨result.material, result.transcript, result.candidate⟩⟩

/-- One-time generation followed by exactly prekey/one-time/PQ signing and one stateful public selector. -/
def statefulPhase1Tail
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) :
    OracleComp (((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) + Phase1SigningSpec)
      (StatefulPhase1Result kem setup selector) := do
  let after ← phase1CcaLift (OracleComp.liftComp
    (setup.oneTime identity before target)
      ((unifSpec + baseSpec) + (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)))
  let material := setupMaterial setup identity before target after
  let preSignature ← phase1SigningQuery (prekeyMessage material.prekey)
  let oneSignature ← phase1SigningQuery (oneTimeMessage material.oneTime)
  let pqSignature ← phase1SigningQuery (pqMessage material.pqKey)
  let transcript := honestPhase1Transcript identity material preSignature oneSignature pqSignature
  let selected ← phase1CcaLift (selector.mainConcrete kem transcript)
  return ⟨identity, target, before, after, preSignature, oneSignature, pqSignature,
    selected.1, selected.2⟩

/-- The concrete local prechallenge interpreter at the exact exposed CCA surface. -/
def localKemPreChallengeImpl
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK) :
    QueryImpl ((unifSpec + baseSpec) +
        (MlKem768Ciphertext →ₒ Option MlKemSharedSecret))
      (OracleComp (unifSpec + baseSpec)) :=
  kem.IND_CCA_preChallengeImpl sk

/-- The stopped EUF reduction owns the locally generated KEM key and interprets all prechallenge decapsulation calls, while forwarding signature queries. -/
def localKemPhase1Impl
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK) :
    QueryImpl (((unifSpec + baseSpec) +
        (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) + Phase1SigningSpec)
      (OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)) :=
  (localKemPreChallengeImpl kem sk).liftTarget
      (OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)) +
    (fun message : Pqxdh.Bytes => (liftM (Phase1SigningSpec.query message) :
      OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec) Ed25519Signature))

/-- Exact source-order stopped prefix: prekey generation, one KEM key generation, then the public signing/selection tail. Identity generation is performed by the enclosing signature experiment. -/
def statefulPhase1Client
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) :
    OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      (StatefulPhase1Result kem setup selector) := do
  let before ← OracleComp.liftComp (setup.prekey identity)
    ((unifSpec + baseSpec) + Phase1SigningSpec)
  let (target, sk) ← OracleComp.liftComp kem.keygen
    ((unifSpec + baseSpec) + Phase1SigningSpec)
  simulateQ (localKemPhase1Impl kem sk)
    (statefulPhase1Tail kem setup selector identity before target)

/-- Direct locally interpreted tail used to expose the exact same joint distribution, including private state and adaptive selector output. -/
def localStatefulPhase1Tail
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) (sk : KemSK) :
    OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      (StatefulPhase1Result kem setup selector) := do
  let after ← (liftM
    (simulateQ (localKemPreChallengeImpl kem sk) (OracleComp.liftComp
      (setup.oneTime identity before target)
      ((unifSpec + baseSpec) +
        (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)))) :
    OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      (PrivateOneTime setup.PrivateOne))
  let material := setupMaterial setup identity before target after
  let preSignature ← phase1ForwardSigningQuery (prekeyMessage material.prekey)
  let oneSignature ← phase1ForwardSigningQuery (oneTimeMessage material.oneTime)
  let pqSignature ← phase1ForwardSigningQuery (pqMessage material.pqKey)
  let transcript := honestPhase1Transcript identity material preSignature oneSignature pqSignature
  let selected ← (liftM
    (simulateQ (localKemPreChallengeImpl kem sk)
      (selector.mainConcrete kem transcript)) :
    OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      (Phase1Candidate × selector.State))
  return ⟨identity, target, before, after, preSignature, oneSignature, pqSignature,
    selected.1, selected.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem simulateQ_localKemPhase1Impl_liftCCA
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK)
    {alpha : Type} (computation : OracleComp
      ((unifSpec + baseSpec) +
        (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) alpha) :
    simulateQ (localKemPhase1Impl kem sk)
        (phase1CcaLift computation) =
      (liftM (simulateQ (localKemPreChallengeImpl kem sk) computation) :
        OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec) alpha) := by
  unfold phase1CcaLift
  rw [← QueryImpl.simulateQ_compose]
  rw [show (localKemPhase1Impl kem sk ∘ₛ phase1CcaLiftImpl) =
      (localKemPreChallengeImpl kem sk).liftTarget
        (OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)) by
    funext query
    unfold QueryImpl.compose phase1CcaLiftImpl
    rw [simulateQ_spec_query]
    rfl]
  rw [simulateQ_liftTarget]

set_option backward.isDefEq.respectTransparency false in
theorem simulateQ_localKemPhase1Impl_sign
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK)
    (message : Pqxdh.Bytes) :
    simulateQ (localKemPhase1Impl kem sk)
        (phase1SigningQuery message) =
      phase1ForwardSigningQuery message := by
  unfold localKemPhase1Impl
  unfold phase1SigningQuery phase1ForwardSigningQuery
  rw [simulateQ_spec_query]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem simulateQ_statefulPhase1Tail_localKem
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) (sk : KemSK) :
    simulateQ (localKemPhase1Impl kem sk)
        (statefulPhase1Tail kem setup selector identity before target) =
      localStatefulPhase1Tail kem setup selector identity before target sk := by
  unfold statefulPhase1Tail localStatefulPhase1Tail
  simp only [simulateQ_bind, simulateQ_pure]
  rw [simulateQ_localKemPhase1Impl_liftCCA]
  simp_rw [simulateQ_localKemPhase1Impl_sign]
  simp_rw [simulateQ_localKemPhase1Impl_liftCCA]

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.simulateQ_localKemPhase1Impl_liftCCA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms simulateQ_localKemPhase1Impl_liftCCA

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.simulateQ_localKemPhase1Impl_sign' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms simulateQ_localKemPhase1Impl_sign

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.simulateQ_statefulPhase1Tail_localKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms simulateQ_statefulPhase1Tail_localKem

/-- The complete signing log, including the actual three returned signatures in source order. -/
def StatefulPhase1Result.signingLog
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) : QueryLog Phase1SigningSpec :=
  [⟨prekeyMessage result.material.prekey, result.preSignature⟩,
    ⟨oneTimeMessage result.material.oneTime, result.oneSignature⟩,
    ⟨pqMessage result.material.pqKey, result.pqSignature⟩]

set_option backward.isDefEq.respectTransparency false in
theorem phase1SigningImpl_run_forwardSign {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (pk : Ed25519PublicKey) (sk : SecretKey) (message : Pqxdh.Bytes) :
    (simulateQ (phase1SigningImpl sigAlg pk sk)
      (phase1ForwardSigningQuery message)).run =
      (sigAlg.sign pk sk message >>= fun signature =>
        pure (signature, ([⟨message, signature⟩] : QueryLog Phase1SigningSpec))) := by
  simp [phase1ForwardSigningQuery, phase1SigningImpl, SignatureAlg.signingOracle]

set_option backward.isDefEq.respectTransparency false in
theorem phase1Base_cca_query_liftComp (query : (unifSpec + baseSpec).Domain) :
    OracleComp.liftComp (liftM ((unifSpec + baseSpec).query query) :
      OracleComp (unifSpec + baseSpec) ((unifSpec + baseSpec).Range query))
      ((unifSpec + baseSpec) + (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) =
    liftM ((((unifSpec + baseSpec) + (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)).query (.inl query))) := by
  cases query <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem localKemPreChallengeImpl_base {alpha : Type}
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK)
    (computation : OracleComp (unifSpec + baseSpec) alpha) :
    simulateQ (localKemPreChallengeImpl kem sk)
      (OracleComp.liftComp computation ((unifSpec + baseSpec) +
        (MlKem768Ciphertext →ₒ Option MlKemSharedSecret))) = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query continuation ih =>
    simp only [OracleComp.liftComp_bind, simulateQ_bind, phase1Base_cca_query_liftComp, ih]
    simp [localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl]
    rfl

/-- Direct source-order signing execution retaining every private and public tail result. -/
def statefulPhase1TailReference {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (identitySk : SecretKey)
    (before : PrivatePrekey setup.PrivatePre) (target : TargetKemPublicKey)
    (kemSk : KemSK) : OracleComp (unifSpec + baseSpec)
      (StatefulPhase1Result kem setup selector) := do
  let after ← setup.oneTime identity before target
  let material := setupMaterial setup identity before target after
  let preSignature ← sigAlg.sign identity identitySk (prekeyMessage material.prekey)
  let oneSignature ← sigAlg.sign identity identitySk (oneTimeMessage material.oneTime)
  let pqSignature ← sigAlg.sign identity identitySk (pqMessage material.pqKey)
  let transcript := honestPhase1Transcript identity material preSignature oneSignature pqSignature
  let selected ← simulateQ (localKemPreChallengeImpl kem kemSk)
    (selector.mainConcrete kem transcript)
  return ⟨identity, target, before, after, preSignature, oneSignature, pqSignature,
    selected.1, selected.2⟩

/-- Stopped source prefix preserving the correlated prekey and KEM generation order. -/
def statefulPhase1ClientReference {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (identitySk : SecretKey) :
    OracleComp (unifSpec + baseSpec) (StatefulPhase1Result kem setup selector) := do
  let before ← setup.prekey identity
  let (target, kemSk) ← kem.keygen
  statefulPhase1TailReference sigAlg kem setup selector identity identitySk before target kemSk

/-- The same-target accepted field-substitution event on the complete retained result. -/
def StatefulPhase1Result.badBit
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (result : StatefulPhase1Result kem setup selector) : Bool :=
  phase1FieldSubstitutionBit verifyFn result.identity result.material result.candidate

/-- Select one changed typed field in the existing server verification order, without guessing a field. -/
def StatefulPhase1Result.forgery
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) : Pqxdh.Bytes × Ed25519Signature :=
  selectPhase1Forgery result.material result.transcript result.candidate

/-- A successful substitution selects a valid message absent from all three actual signing requests. -/
theorem StatefulPhase1Result.badBit_selects_fresh_valid
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (result : StatefulPhase1Result kem setup selector)
    (bad : result.badBit verifyFn = true) :
    verifyFn result.identity result.forgery.1 result.forgery.2 = true ∧
      result.forgery.1 ∉ result.signingLog.map (fun entry => entry.1) := by
  simpa [StatefulPhase1Result.forgery, StatefulPhase1Result.signingLog,
    honestPhase1Messages] using
    phase1FieldSubstitution_selects_fresh_valid verifyFn result.identity result.material
      result.transcript result.candidate bad

/-- The reduction runs the retained source prefix and outputs the one selected field forgery. -/
def statefulPhase1ToEUFCMA {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    SignatureAlg.UnforgeableAdversary sigAlg where
  main identity := StatefulPhase1Result.forgery <$>
    statefulPhase1Client kem setup selector identity

/-- Identity generation encloses the complete source-order retained reference. -/
def statefulPhase1JointReference {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    OracleComp (unifSpec + baseSpec) (StatefulPhase1Result kem setup selector) := do
  let (identity, identitySk) ← sigAlg.keygen
  statefulPhase1ClientReference sigAlg kem setup selector identity identitySk

/-- The actual signature experiment writer retains the full protocol result beside its log. -/
def statefulPhase1WriterJoint {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    OracleComp (unifSpec + baseSpec)
      (StatefulPhase1Result kem setup selector × QueryLog Phase1SigningSpec) := do
  let (identity, identitySk) ← sigAlg.keygen
  (simulateQ (phase1SigningImpl sigAlg identity identitySk)
    (statefulPhase1Client kem setup selector identity)).run

/-- Weak EUF checks freshness of the message, without requiring a new signature for an old message. -/
def StatefulPhase1Result.eufBit
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (result : StatefulPhase1Result kem setup selector) : Bool :=
  decide (result.forgery.1 ∉ result.signingLog.map (fun entry => entry.1)) &&
    verifyFn result.identity result.forgery.1 result.forgery.2

theorem StatefulPhase1Result.badBit_implies_eufBit
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (result : StatefulPhase1Result kem setup selector)
    (bad : result.badBit verifyFn = true) : result.eufBit verifyFn = true := by
  obtain ⟨valid, fresh⟩ := result.badBit_selects_fresh_valid verifyFn bad
  simp [StatefulPhase1Result.eufBit, fresh, valid]

set_option backward.isDefEq.respectTransparency false in
theorem phase1Base_query_lift (query : (unifSpec + baseSpec).Domain) :
    (liftM (liftM ((unifSpec + baseSpec).query query) :
      OracleComp (unifSpec + baseSpec) ((unifSpec + baseSpec).Range query)) :
      OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      ((unifSpec + baseSpec).Range query)) =
    liftM ((((unifSpec + baseSpec) + Phase1SigningSpec).query (.inl query))) := by
  cases query <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem phase1SigningImpl_run_concreteLift {SecretKey alpha : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (pk : Ed25519PublicKey) (sk : SecretKey)
    (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (simulateQ (phase1SigningImpl sigAlg pk sk)
      (liftM computation : OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
        alpha)).run =
      (fun output => (output, ([] : QueryLog Phase1SigningSpec))) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query continuation ih =>
    simp only [liftM_bind, simulateQ_bind, WriterT.run_bind, phase1Base_query_lift]
    simp only [ih]
    simp [phase1SigningImpl, HasQuery.toQueryImpl_apply]

set_option backward.isDefEq.respectTransparency false in
theorem localStatefulPhase1Tail_writer_exact {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (identitySk : SecretKey)
    (before : PrivatePrekey setup.PrivatePre) (target : TargetKemPublicKey)
    (kemSk : KemSK) :
    (simulateQ (phase1SigningImpl sigAlg identity identitySk)
      (localStatefulPhase1Tail kem setup selector identity before target kemSk)).run =
      (fun result => (result, result.signingLog)) <$>
        statefulPhase1TailReference sigAlg kem setup selector identity identitySk
          before target kemSk := by
  simp [localStatefulPhase1Tail, statefulPhase1TailReference,
    phase1SigningImpl_run_concreteLift, phase1SigningImpl_run_forwardSign,
    localKemPreChallengeImpl_base,
    StatefulPhase1Result.signingLog, StatefulPhase1Result.material]
  rfl

noncomputable def statefulPhase1EufBody {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    OracleComp (unifSpec + baseSpec) Bool := by
  letI : DecidableEq Pqxdh.Bytes := Classical.decEq Pqxdh.Bytes
  exact do
    let (identity, identitySk) ← sigAlg.keygen
    let (result, log) ← (simulateQ (phase1SigningImpl sigAlg identity identitySk)
      (statefulPhase1Client kem setup selector identity)).run
    let verified ← sigAlg.verify identity result.forgery.1 result.forgery.2
    return !log.wasQueried result.forgery.1 && verified

set_option backward.isDefEq.respectTransparency false in
theorem unforgeableExp_statefulPhase1ToEUFCMA {SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    runtime.evalDist (SignatureAlg.unforgeableExperiment (statefulPhase1ToEUFCMA sigAlg kem setup selector)) =
      runtime.evalDist (statefulPhase1EufBody sigAlg kem setup selector) := by
  simp [SignatureAlg.unforgeableExperiment, statefulPhase1EufBody, statefulPhase1ToEUFCMA,
    phase1SigningImpl, SignatureAlg.runWithSigningOracle, map_eq_bind_pure_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem phase1Base_query_liftComp (query : (unifSpec + baseSpec).Domain) :
    OracleComp.liftComp (liftM ((unifSpec + baseSpec).query query) :
      OracleComp (unifSpec + baseSpec) ((unifSpec + baseSpec).Range query))
      ((unifSpec + baseSpec) + Phase1SigningSpec) =
    liftM ((((unifSpec + baseSpec) + Phase1SigningSpec).query (.inl query))) := by
  cases query <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem phase1SigningImpl_run_concreteLiftComp {SecretKey alpha : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (pk : Ed25519PublicKey) (sk : SecretKey)
    (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (simulateQ (phase1SigningImpl sigAlg pk sk)
      (OracleComp.liftComp computation ((unifSpec + baseSpec) + Phase1SigningSpec))).run =
      (fun output => (output, ([] : QueryLog Phase1SigningSpec))) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query continuation ih =>
    simp only [OracleComp.liftComp_bind, simulateQ_bind, WriterT.run_bind, phase1Base_query_liftComp]
    simp only [ih]
    simp [phase1SigningImpl, HasQuery.toQueryImpl_apply]

set_option backward.isDefEq.respectTransparency false in
theorem statefulPhase1Client_writer_exact {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (identitySk : SecretKey) :
    (simulateQ (phase1SigningImpl sigAlg identity identitySk)
      (statefulPhase1Client kem setup selector identity)).run =
      (fun result => (result, result.signingLog)) <$>
        statefulPhase1ClientReference sigAlg kem setup selector identity identitySk := by
  simp [statefulPhase1Client, statefulPhase1ClientReference,
    simulateQ_statefulPhase1Tail_localKem, localStatefulPhase1Tail_writer_exact,
    phase1SigningImpl_run_concreteLiftComp]

/-- Identity generation, the full retained result, and every message/signature log entry agree jointly. -/
theorem statefulPhase1WriterJoint_exact {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    statefulPhase1WriterJoint sigAlg kem setup selector =
      (fun result => (result, result.signingLog)) <$>
        statefulPhase1JointReference sigAlg kem setup selector := by
  simp [statefulPhase1WriterJoint, statefulPhase1JointReference,
    statefulPhase1Client_writer_exact]

@[simp] theorem StatefulPhase1Result.signingLog_length
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) : result.signingLog.length = 3 := by
  rfl

@[simp] theorem StatefulPhase1Result.signingLog_messages
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (result : StatefulPhase1Result kem setup selector) :
    result.signingLog.map (fun entry => entry.1) = honestPhase1Messages result.material := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem statefulPhase1EufBody_eq_reference {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn) :
    statefulPhase1EufBody sigAlg kem setup selector =
      StatefulPhase1Result.eufBit verifyFn <$>
        statefulPhase1JointReference sigAlg kem setup selector := by
  unfold statefulPhase1EufBody statefulPhase1JointReference
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  rintro ⟨identity, identitySk⟩
  simp_rw [deterministic identity]
  rw [statefulPhase1Client_writer_exact]
  simp only [bind_map_left, pure_bind, QueryLog.wasQueried_eq_decide_mem_map_fst]
  simp [statefulPhase1ClientReference, statefulPhase1TailReference,
    StatefulPhase1Result.eufBit]

theorem unforgeableExp_statefulPhase1ToEUFCMA_eq_reference {SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn) :
    runtime.evalDist (SignatureAlg.unforgeableExperiment (statefulPhase1ToEUFCMA sigAlg kem setup selector)) =
      runtime.evalDist
        (statefulPhase1JointReference sigAlg kem setup selector >>= fun result =>
          pure (StatefulPhase1Result.eufBit verifyFn result)) := by
  rw [unforgeableExp_statefulPhase1ToEUFCMA, statefulPhase1EufBody_eq_reference
    sigAlg kem setup selector verifyFn deterministic, map_eq_bind_pure_comp]
  rfl

/-- Probability of accepted same-identity field substitution in the stopped source-order experiment. -/
noncomputable def StatefulPhase1FieldSubstitutionAdvantage {SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) : ℝ≥0∞ :=
  runtime.evalDist
    (statefulPhase1JointReference sigAlg kem setup selector >>= fun result =>
      pure (StatefulPhase1Result.badBit verifyFn result)) {true}

/-- One deterministic field selection gives a coefficient-one weak-EUF-CMA reduction. -/
theorem statefulPhase1FieldSubstitutionAdvantage_le_eufCma {SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn) :
    StatefulPhase1FieldSubstitutionAdvantage runtime sigAlg kem setup selector verifyFn ≤
      SignatureAlg.unforgeableAdvantage runtime (statefulPhase1ToEUFCMA sigAlg kem setup selector) := by
  let : MeasurableSpace (StatefulPhase1Result kem setup selector) := ⊤
  let : DiscreteMeasurableSpace (StatefulPhase1Result kem setup selector) :=
    ⟨fun _ => by simp⟩
  unfold StatefulPhase1FieldSubstitutionAdvantage SignatureAlg.unforgeableAdvantage
  rw [unforgeableExp_statefulPhase1ToEUFCMA_eq_reference runtime sigAlg kem setup
    selector verifyFn deterministic,
    runtime.evalDist_bind_pure _ (StatefulPhase1Result.badBit verifyFn)
      Measurable.of_discrete,
    runtime.evalDist_bind_pure _ (StatefulPhase1Result.eufBit verifyFn)
      Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton true),
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
  apply measure_mono
  intro result hresult
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hresult ⊢
  exact result.badBit_implies_eufBit verifyFn hresult

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.localStatefulPhase1Tail_writer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms localStatefulPhase1Tail_writer_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1Client_writer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1Client_writer_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1WriterJoint_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1WriterJoint_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.StatefulPhase1Result.badBit_selects_fresh_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StatefulPhase1Result.badBit_selects_fresh_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1FieldSubstitutionAdvantage_le_eufCma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1FieldSubstitutionAdvantage_le_eufCma

end BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma
