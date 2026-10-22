import BeaconcryptCore.Computational.PqxdhStatefulPhase1QueryBounds
import BeaconcryptCore.Computational.PqxdhSecretInputInitializer

/-!
# Stateful Phase-1 admission and the full-continuation authentication hop

Admission distinguishes unchanged honest fields, changed fields under the honest identity, accepted attacker-owned identities, and rejection. Only the changed same-identity case is the EUF bad event. Complete private prekey/one-time state, signatures, candidate, and selector continuation remain arguments of the continued game. The authentication reduction stops before the continuation, so it does not need the target identity's converted-DH secret.

The complete-continuation generator interchange theorem concerns evaluated distributions after an arbitrary joint continuation. It follows from commutation of two independent probabilistic computations after the fixed stateless ambient interpreter; equality of marginal key distributions is not an assumption.
-/

open OracleSpec OracleComp ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhStatefulPhase1Authentication

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhStatefulPhase1EufCma
open PqxdhInitializerSecrecy PqxdhSecretInputKdf

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK : Type}

/-- Exact four-way source admission, without an honest-selected-key premise. -/
inductive Admission where
  | rejected
  | attackerOwned (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
  | unchanged
  | changed (keys : Phase1KeyTuple)

noncomputable def admission
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (result : StatefulPhase1Result kem setup selector) : Admission :=
  match acceptPhase1Candidate verifyFn result.candidate with
  | none => .rejected
  | some (identity, keys) =>
    if identity = result.identity then
      if keys = result.material.keyTuple then .unchanged else .changed keys
    else .attackerOwned identity keys

/-- A selected honest key is derived from the unchanged admission branch. -/
theorem admission_unchanged_iff
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (result : StatefulPhase1Result kem setup selector) :
    admission verifyFn result = .unchanged ↔
      acceptPhase1Candidate verifyFn result.candidate =
        some (result.identity, result.material.keyTuple) := by
  cases accepted : acceptPhase1Candidate verifyFn result.candidate with
  | none => simp [admission, accepted]
  | some value =>
    rcases value with ⟨identity, keys⟩
    simp only [admission, accepted, Option.some.injEq, Prod.mk.injEq]
    split_ifs <;> simp_all

/-- Rejection and attacker-owned candidates keep their complete original continuation. -/
noncomputable def authenticateContinuation
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (next onChanged : StatefulPhase1Result kem setup selector → ProbComp Bool)
    (result : StatefulPhase1Result kem setup selector) : ProbComp Bool :=
  if result.badBit verifyFn then onChanged result else next result

/-- Authentication changes a complete continued game only on the single stopped field-substitution event. -/
theorem continuationAdvantage_le_bad
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (sample : ProbComp (StatefulPhase1Result kem setup selector))
    (next onChanged : StatefulPhase1Result kem setup selector → ProbComp Bool) :
    (sample >>= next).boolDistance
        (sample >>= authenticateContinuation verifyFn next onChanged) ≤
      Pr{let result ← sample}[result.badBit verifyFn = true].toReal := by
  rw [ProbComp.boolDistance]
  have bound := discreteDistance_bind_left_event_le sample next
    (authenticateContinuation verifyFn next onChanged)
    (fun result => result.badBit verifyFn = true)
    (fun result good => by simp [authenticateContinuation, good])
  refine le_trans ?_ bound
  simpa only [prEvent_eq_evalDist_singleton] using
    abs_prEvent_toReal_sub_le_discreteDistance (sample >>= next)
      (sample >>= authenticateContinuation verifyFn next onChanged)

/-- A complete continuation after the source-ordered prefix costs one weak-EUF-CMA term; it need not be simulated by the forgery reduction. -/
theorem continuationAdvantage_le_eufCma {SecretKey : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (next onChanged : StatefulPhase1Result kem setup selector → ProbComp Bool) :
    ((simulateQ (kemAmbientImpl baseImpl)
      (statefulPhase1JointReference sigAlg kem setup selector)) >>= next).boolDistance
      ((simulateQ (kemAmbientImpl baseImpl)
        (statefulPhase1JointReference sigAlg kem setup selector)) >>=
          authenticateContinuation verifyFn next onChanged) ≤
      (SignatureAlg.unforgeableAdvantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (statefulPhase1ToEUFCMA sigAlg kem setup selector)).toReal := by
  have euf := statefulPhase1FieldSubstitutionAdvantage_le_eufCma
    (runtimeOfImpl (kemAmbientImpl baseImpl)) sigAlg kem setup selector verifyFn deterministic
  refine (continuationAdvantage_le_bad verifyFn _ next onChanged).trans ?_
  apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
  have advantage : StatefulPhase1FieldSubstitutionAdvantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      sigAlg kem setup selector verifyFn =
      Pr{let result ← (simulateQ (kemAmbientImpl baseImpl)
        (statefulPhase1JointReference sigAlg kem setup selector))}[result.badBit verifyFn = true] := by
    unfold StatefulPhase1FieldSubstitutionAdvantage
    rw [runtimeOfImpl_evalDist, simulateQ_bind, prEvent_eq_evalDist_decide]
    simp only [simulateQ_pure, Bool.decide_eq_true]
  rw [advantage] at euf
  simpa only [SignatureAlg.unforgeableAdvantage] using euf

/-- Independent source prefix before KEM generation, retaining the identity secret and private prekey state. -/
noncomputable def identityPrekeySample {SecretKey : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (setup : StatefulPhase1Setup baseSpec) :
    ProbComp (Ed25519PublicKey × SecretKey × PrivatePrekey setup.PrivatePre) := do
  let (identity, identitySk) ← simulateQ (kemAmbientImpl baseImpl) sigAlg.keygen
  let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)
  return (identity, identitySk, before)

/-- Moving independent KEM generation preserves the evaluated distribution of every complete joint continuation. -/
theorem generators_commute_complete_continuation {SecretKey Output : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (next : (Ed25519PublicKey × SecretKey × PrivatePrekey setup.PrivatePre) →
      (TargetKemPublicKey × KemSK) → ProbComp Output) :
    EvalDistEq
      (do
        let retained ← identityPrekeySample baseImpl sigAlg setup
        let keypair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
        next retained keypair)
      (do
        let keypair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
        let retained ← identityPrekeySample baseImpl sigAlg setup
        next retained keypair) := by
  exact PqxdhSecretInputKdf.evalSPMF_sample_comm (identityPrekeySample baseImpl sigAlg setup)
    (simulateQ (kemAmbientImpl baseImpl) kem.keygen) next

/-- Internal source prefix retains the identity secret and leaves the KEM secret available only to its later interpreter. -/
noncomputable def privateSourcePrefix {SecretKey : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    ProbComp (SecretKey × StatefulPhase1Result kem setup selector × KemSK) := do
  let (identity, identitySk) ← simulateQ (kemAmbientImpl baseImpl) sigAlg.keygen
  let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)
  let (target, kemSk) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let result ← simulateQ (kemAmbientImpl baseImpl)
    (statefulPhase1TailReference sigAlg kem setup selector identity identitySk before target kemSk)
  return (identitySk, result, kemSk)

/-- Projecting away the two private interpreter secrets gives exactly the existing source-ordered EUF prefix. -/
theorem privateSourcePrefix_project {SecretKey : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) :
    (fun state : SecretKey × StatefulPhase1Result kem setup selector × KemSK => state.2.1) <$>
        privateSourcePrefix baseImpl sigAlg kem setup selector =
      simulateQ (kemAmbientImpl baseImpl)
        (statefulPhase1JointReference sigAlg kem setup selector) := by
  simp [privateSourcePrefix, statefulPhase1JointReference, statefulPhase1ClientReference]

/-- Private identity and KEM interpreter state do not alter the stopped bad-event probability. -/
theorem privateSourcePrefix_bad_probability {SecretKey : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    Pr{let state ← privateSourcePrefix baseImpl sigAlg kem setup selector}[
      state.2.1.badBit verifyFn = true] =
    StatefulPhase1FieldSubstitutionAdvantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      sigAlg kem setup selector verifyFn := by
  have advantage : StatefulPhase1FieldSubstitutionAdvantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      sigAlg kem setup selector verifyFn =
      Pr{let result ← (simulateQ (kemAmbientImpl baseImpl)
        (statefulPhase1JointReference sigAlg kem setup selector))}[result.badBit verifyFn = true] := by
    unfold StatefulPhase1FieldSubstitutionAdvantage
    rw [runtimeOfImpl_evalDist, simulateQ_bind, prEvent_eq_evalDist_decide]
    simp only [simulateQ_pure, Bool.decide_eq_true]
  have projected := congrArg
    (fun computation : ProbComp (StatefulPhase1Result kem setup selector) =>
      Pr{let result ← computation}[result.badBit verifyFn = true])
    (privateSourcePrefix_project baseImpl sigAlg kem setup selector)
  rw [prEvent_map] at projected
  rw [advantage]
  exact projected

/-- The stopped EUF charge remains coefficient one with every private identity/KEM value retained by the enclosing protocol interpreter. `next` describes the entire private interpreter for this probability bound; it is not a protocol or adversary callback, and this theorem supplies no CCA simulation of an arbitrary such function. A later CCA reduction must confine the KEM key to its oracle handler. -/
theorem privateContinuationAdvantage_le_eufCma {SecretKey : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (next onChanged : (SecretKey × StatefulPhase1Result kem setup selector × KemSK) →
      ProbComp Bool) :
    (privateSourcePrefix baseImpl sigAlg kem setup selector >>= next).boolDistance
      (privateSourcePrefix baseImpl sigAlg kem setup selector >>= fun state =>
        if state.2.1.badBit verifyFn then onChanged state else next state) ≤
      (SignatureAlg.unforgeableAdvantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (statefulPhase1ToEUFCMA sigAlg kem setup selector)).toReal := by
  have euf := statefulPhase1FieldSubstitutionAdvantage_le_eufCma
    (runtimeOfImpl (kemAmbientImpl baseImpl)) sigAlg kem setup selector verifyFn deterministic
  rw [ProbComp.boolDistance]
  have bound := discreteDistance_bind_left_event_le (privateSourcePrefix baseImpl sigAlg kem setup selector)
    next (fun state => if state.2.1.badBit verifyFn then onChanged state else next state)
    (fun state => state.2.1.badBit verifyFn = true)
    (fun state good => by simp [good])
  rw [ privateSourcePrefix_bad_probability] at bound
  refine le_trans ?_ (bound.trans (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) euf))
  simpa only [prEvent_eq_evalDist_singleton] using
    abs_prEvent_toReal_sub_le_discreteDistance
      (privateSourcePrefix baseImpl sigAlg kem setup selector >>= next)
      (privateSourcePrefix baseImpl sigAlg kem setup selector >>= fun state =>
        if state.2.1.badBit verifyFn then onChanged state else next state)

/-- The actual private Phase-1 prefix may take the challenger KEM key first without changing any complete continued distribution. -/
theorem privateSourcePrefix_kem_first {SecretKey Output : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (next : (SecretKey × StatefulPhase1Result kem setup selector × KemSK) → ProbComp Output) :
    EvalDistEq (privateSourcePrefix baseImpl sigAlg kem setup selector >>= next)
      (do
        let (target, kemSk) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
        let retained ← identityPrekeySample baseImpl sigAlg setup
        let result ← simulateQ (kemAmbientImpl baseImpl)
          (statefulPhase1TailReference sigAlg kem setup selector
            retained.1 retained.2.1 retained.2.2 target kemSk)
        next (retained.2.1, result, kemSk)) := by
  simpa [privateSourcePrefix, identityPrekeySample] using
    generators_commute_complete_continuation baseImpl sigAlg kem setup
      (fun retained keypair => do
        let result ← simulateQ (kemAmbientImpl baseImpl)
          (statefulPhase1TailReference sigAlg kem setup selector
            retained.1 retained.2.1 retained.2.2 keypair.1 keypair.2)
        next (retained.2.1, result, keypair.2))

/-- The source tail with a borrowed decapsulation oracle contains no KEM secret-key argument. -/
def borrowedPhase1Tail {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (identitySk : SecretKey)
    (before : PrivatePrekey setup.PrivatePre) (target : TargetKemPublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (StatefulPhase1Result kem setup selector) := do
  let after ← OracleComp.liftComp (setup.oneTime identity before target) (MlKemCCAOracleSpec baseSpec)
  let material := setupMaterial setup identity before target after
  let preSignature ← OracleComp.liftComp
    (sigAlg.sign identity identitySk (prekeyMessage material.prekey)) (MlKemCCAOracleSpec baseSpec)
  let oneSignature ← OracleComp.liftComp
    (sigAlg.sign identity identitySk (oneTimeMessage material.oneTime)) (MlKemCCAOracleSpec baseSpec)
  let pqSignature ← OracleComp.liftComp
    (sigAlg.sign identity identitySk (pqMessage material.pqKey)) (MlKemCCAOracleSpec baseSpec)
  let transcript := honestPhase1Transcript identity material preSignature oneSignature pqSignature
  let selected ← selector.mainConcrete kem transcript
  return ⟨identity, target, before, after, preSignature, oneSignature, pqSignature,
    selected.1, selected.2⟩

/-- Local interpretation of the borrowed oracle is the complete source tail, including all retained state and signing outputs. -/
theorem borrowedPhase1Tail_local_exact {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (identitySk : SecretKey)
    (before : PrivatePrekey setup.PrivatePre) (target : TargetKemPublicKey) (kemSk : KemSK) :
    simulateQ (localKemPreChallengeImpl kem kemSk)
      (borrowedPhase1Tail sigAlg kem setup selector identity identitySk before target) =
    statefulPhase1TailReference sigAlg kem setup selector identity identitySk before target kemSk := by
  simp [borrowedPhase1Tail, statefulPhase1TailReference, localKemPreChallengeImpl_base]

/-- The IND-CCA prefix generates and retains its own signing identity, then selects through the borrowed oracle. -/
def borrowedPhase1Prefix {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) (target : TargetKemPublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec)
      (SecretKey × StatefulPhase1Result kem setup selector) := do
  let (identity, identitySk) ← OracleComp.liftComp sigAlg.keygen (MlKemCCAOracleSpec baseSpec)
  let before ← OracleComp.liftComp (setup.prekey identity) (MlKemCCAOracleSpec baseSpec)
  let result ← borrowedPhase1Tail sigAlg kem setup selector identity identitySk before target
  return (identitySk, result)

/-- The borrowed prefix retains the actual generated identity secret after local KEM interpretation. -/
theorem borrowedPhase1Prefix_local_exact {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (target : TargetKemPublicKey) (kemSk : KemSK) :
    simulateQ (localKemPreChallengeImpl kem kemSk)
      (borrowedPhase1Prefix sigAlg kem setup selector target) =
    (do
      let (identity, identitySk) ← sigAlg.keygen
      let before ← setup.prekey identity
      let result ← statefulPhase1TailReference sigAlg kem setup selector
        identity identitySk before target kemSk
      return (identitySk, result)) := by
  simp [borrowedPhase1Prefix, localKemPreChallengeImpl_base, borrowedPhase1Tail_local_exact]

/-- The full source prefix and the borrowed-CCA prefix agree before every complete private continuation. -/
theorem privateSourcePrefix_borrowed_complete {SecretKey Output : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (next : (SecretKey × StatefulPhase1Result kem setup selector × KemSK) → ProbComp Output) :
    EvalDistEq (privateSourcePrefix baseImpl sigAlg kem setup selector >>= next)
      (do
        let (target, kemSk) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
        let retained ← simulateQ (kemAmbientImpl baseImpl)
          (simulateQ (localKemPreChallengeImpl kem kemSk)
            (borrowedPhase1Prefix sigAlg kem setup selector target))
        next (retained.1, retained.2, kemSk)) := by
  simpa [borrowedPhase1Prefix_local_exact, identityPrekeySample] using
    privateSourcePrefix_kem_first baseImpl sigAlg kem setup selector next

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1Authentication.privateContinuationAdvantage_le_eufCma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms privateContinuationAdvantage_le_eufCma

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1Authentication.privateSourcePrefix_borrowed_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms privateSourcePrefix_borrowed_complete

end BeaconcryptCore.Computational.PqxdhStatefulPhase1Authentication
