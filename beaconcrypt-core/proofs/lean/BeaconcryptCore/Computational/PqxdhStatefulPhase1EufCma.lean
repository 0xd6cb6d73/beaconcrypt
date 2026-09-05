import BeaconcryptCore.Computational.PqxdhEd25519EufCma
import BeaconcryptCore.Computational.PqxdhKemIndCca

/-!
# Stateful Phase-1 authentication prefix

This module defines the privately correlated, source-ordered Phase-1 prefix needed to compose the existing Ed25519 field-origin reduction with the initialized-chain secrecy game. The `publicContext` callback is passed only the identity, prekey, target ML-KEM public key, and one-time public key and receives none of the generated private results or the ML-KEM secret key; private setup and selector continuation state remain in the retained result, and the ML-KEM secret key remains exclusively inside the local CCA interpreter.

The checked routing lemma shows that lifting an arbitrary full prechallenge CCA computation through the signing layer and interpreting it with the locally owned ML-KEM key preserves the complete CCA computation under an untouched signing layer. It does not yet prove the joint writer/EUF equality or the final authentication-plus-chain bound.

Ed25519, ML-KEM-768, HKDF-SHA-512, X25519, ChaCha20-Poly1305, and BLAKE2b-512 correctness, security, implementation realization, generator independence, binding, and related-use properties are permanent external assumptions. This module proves no primitive internals and does not present those properties as future proof obligations.
-/

open OracleSpec OracleComp ENNReal

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

/-- Source-shaped honest material setup. The context callback receives only public argument values and none of the generated private results or the KEM secret key. -/
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

/-- The retained joint client result contains no KEM secret key. -/
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
    OracleComp (kem.IND_CCA_oracleSpec + Phase1SigningSpec)
      (StatefulPhase1Result kem setup selector) := do
  let after ← OracleComp.liftComp
    (OracleComp.liftComp (setup.oneTime identity before target)
      ((unifSpec + baseSpec) + (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)))
    (((unifSpec + baseSpec) + (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) +
      Phase1SigningSpec)
  let material := setupMaterial setup identity before target after
  let preSignature ← liftM (Phase1SigningSpec.query (prekeyMessage material.prekey))
  let oneSignature ← liftM (Phase1SigningSpec.query (oneTimeMessage material.oneTime))
  let pqSignature ← liftM (Phase1SigningSpec.query (pqMessage material.pqKey))
  let transcript := honestPhase1Transcript identity material preSignature oneSignature pqSignature
  let selected ← OracleComp.liftComp (selector.main transcript)
    (kem.IND_CCA_oracleSpec + Phase1SigningSpec)
  return ⟨identity, target, before, after, preSignature, oneSignature, pqSignature,
    selected.1, selected.2⟩

/-- The stopped EUF reduction owns the locally generated KEM key and interprets all prechallenge decapsulation calls while forwarding signature queries. -/
def localKemPhase1Impl
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK) :
    QueryImpl (kem.IND_CCA_oracleSpec + Phase1SigningSpec)
      (OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)) :=
  (kem.IND_CCA_preChallengeImpl sk).liftTarget
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

/-- Direct locally interpreted tail used to expose the same retained result shape, including private state and adaptive selector output. -/
def localStatefulPhase1Tail
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) (sk : KemSK) :
    OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
      (StatefulPhase1Result kem setup selector) := do
  let after ← OracleComp.liftComp (setup.oneTime identity before target)
    ((unifSpec + baseSpec) + Phase1SigningSpec)
  let material := setupMaterial setup identity before target after
  let preSignature ← liftM (Phase1SigningSpec.query (prekeyMessage material.prekey))
  let oneSignature ← liftM (Phase1SigningSpec.query (oneTimeMessage material.oneTime))
  let pqSignature ← liftM (Phase1SigningSpec.query (pqMessage material.pqKey))
  let transcript := honestPhase1Transcript identity material preSignature oneSignature pqSignature
  let selected ← OracleComp.liftComp
    (simulateQ (kem.IND_CCA_preChallengeImpl sk) (selector.main transcript))
    ((unifSpec + baseSpec) + Phase1SigningSpec)
  return ⟨identity, target, before, after, preSignature, oneSignature, pqSignature,
    selected.1, selected.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting a lifted full prechallenge CCA computation with the private local KEM key preserves that entire computation under the signing layer. -/
theorem simulateQ_localKemPhase1Impl_liftCCA
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (sk : KemSK)
    {alpha : Type} (computation : OracleComp kem.IND_CCA_oracleSpec alpha) :
    simulateQ (localKemPhase1Impl kem sk)
        (OracleComp.liftComp computation
          (kem.IND_CCA_oracleSpec + Phase1SigningSpec)) =
      (liftM (simulateQ (kem.IND_CCA_preChallengeImpl sk) computation) :
        OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec) alpha) := by
  refine (QueryImpl.simulateQ_add_liftComp_left
    ((kem.IND_CCA_preChallengeImpl sk).liftTarget
      (OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)))
    ((fun message : Pqxdh.Bytes =>
      (liftM (Phase1SigningSpec.query message) :
        OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)
          Ed25519Signature)) :
      QueryImpl Phase1SigningSpec
        (OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec)))
    computation).trans ?_
  rw [simulateQ_liftTarget]

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.simulateQ_localKemPhase1Impl_liftCCA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms simulateQ_localKemPhase1Impl_liftCCA

end BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma
