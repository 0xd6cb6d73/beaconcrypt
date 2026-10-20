import BeaconcryptCore.Computational.PqxdhPrivateSourceCoins

/-!
Actual typed source generation runs prekey, ML-KEM and one-time key in order, retaining complete private state. Full evaluated interchange retains arbitrary continuation state under the explicit fixed stateless ambient interpreter. The target secret is confined to the local evaluator and absent from the borrowed selector interface.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateKemSource
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Complete source generation retains both correlated DH private results and the target KEM key only in the private evaluator. -/
structure Generated (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) where
  before : PrivatePrekey setup.PrivatePre
  target : TargetKemPublicKey
  secret : KemSK
  after : PrivateOneTime setup.PrivateOne

/-- Production order is prekey, ML-KEM key pair, then one-time key; the entire resulting private state is returned. -/
def generate (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (identity : Ed25519PublicKey) : ProbComp (Generated setup KemSK) := do
  let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)
  let (target, secret) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let after ← simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)
  pure ⟨before, target, secret, after⟩

/-- The public bundle context uses only the existing public setup map and never receives the KEM secret. -/
def publicMaterial (setup : StatefulPhase1Setup baseSpec) (identity : Ed25519PublicKey)
    (generated : Generated setup KemSK) : Phase1Material setup.Context :=
  setupMaterial setup identity generated.before generated.target generated.after

/-- Actual generated target eligibility follows from the retained joint sample, not selected-candidate honesty. -/
theorem generate_key_support (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (identity : Ed25519PublicKey) (generated : Generated setup KemSK)
    (supported : generated ∈ support (generate baseImpl kem setup identity)) :
    (generated.target, generated.secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen) := by
  simp only [generate, mem_support_bind_iff] at supported
  obtain ⟨before, _, pair, keySupport, after, _, finished⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
  exact keySupport

/-- The source's complete private generator uses the private channel and leaves the actual public transcript unchanged. -/
theorem source_generation_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (identity : Ed25519PublicKey) (state : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (localCoins (generate baseImpl kem setup identity))).run state =
      (fun generated => (generated, state)) <$> generate baseImpl kem setup identity :=
  private_local_complete attachedVerify primitives count _ state

/-- Joint selector requests expose public identity operations and the exact ordinary CCA interface, with no KEM secret argument. -/
abbrev SelectorSpec (baseSpec : OracleSpec ι) := SourceSpec + MlKemCCAOracleSpec baseSpec

/-- A public selector receives only the original signed bundle and public context; its adaptive state remains private to its continuation. -/
structure Selector (baseSpec : OracleSpec ι) (Context : Type) where
  State : Type
  main : Phase1PublicTranscript Context → OracleComp (SelectorSpec baseSpec) (Phase1Candidate × State)

/-- Complete ordinary prechallenge evaluation. Primitive/ambient coins remain private protocol work. -/
def evalKem (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    {Result : Type} (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result) : ProbComp Result :=
  simulateQ (kemAmbientImpl baseImpl) (simulateQ (localKemPreChallengeImpl kem secret) client)

/-- The local selector interpreter confines the generated KEM secret to actual permitted decapsulation. -/
def localSelector (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    QueryImpl (SelectorSpec baseSpec) (OracleComp PrivateSourceSpec)
  | .inl query => publicSource (SourceSpec.query query)
  | .inr query => localCoins (evalKem baseImpl kem secret (MlKemCCAOracleSpec baseSpec |>.query query))

/-- Local probabilistic work is routed to the explicit CCA uniform channel. -/
def ccaCoins {Result : Type} (client : ProbComp Result) : OracleComp (MlKemCCAOracleSpec baseSpec) Result :=
  simulateQ (fun query => (MlKemCCAOracleSpec baseSpec |>.query (.inl (.inl query)) :
    OracleComp (MlKemCCAOracleSpec baseSpec) _)) client

/-- The CCA reduction has its own generated identities but receives no target KEM secret. -/
def borrowedSelector
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) :
    QueryImpl (SelectorSpec baseSpec) (StateT (BareState count) (OracleComp (MlKemCCAOracleSpec baseSpec))) :=
  fun query state => match query with
  | .inl request => ccaCoins ((bareImpl attachedVerify primitives count request).run state)
  | .inr request => do
      let answer ← MlKemCCAOracleSpec baseSpec |>.query request
      pure (answer, state)

/-- The fixed ordinary interpreter forwards exactly the explicitly lifted local coins. -/
theorem evalKem_coins (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    {Result : Type} (client : ProbComp Result) :
    evalKem baseImpl kem secret (ccaCoins client) = client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [ccaCoins, simulateQ_bind, simulateQ_spec_query, evalKem]
      change ((unifSpec.query query : ProbComp _) >>= fun answer =>
        evalKem baseImpl kem secret (ccaCoins (next answer))) = _
      simp only [ih]


/-- Ordinary interpretation preserves complete sequencing, not only output marginals. -/
theorem evalKem_bind {A B : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (first : OracleComp (MlKemCCAOracleSpec baseSpec) A)
    (next : A → OracleComp (MlKemCCAOracleSpec baseSpec) B) :
    evalKem baseImpl kem secret (first >>= next) =
      (evalKem baseImpl kem secret first >>= fun value => evalKem baseImpl kem secret (next value)) := by
  simp only [evalKem, simulateQ_bind]

/-- Each public identity or CCA request has the same actual reply and full source state in the local and borrowed interpretations. -/
theorem localSelector_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (query : (SelectorSpec baseSpec).Domain) (state : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count) (localSelector baseImpl kem secret query)).run state =
      evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives count query).run state) := by
  cases query with
  | inl query =>
      change (simulateQ (privateImpl attachedVerify primitives count) (publicSource (SourceSpec.query query))).run state =
        evalKem baseImpl kem secret (ccaCoins ((bareImpl attachedVerify primitives count query).run state))
      rw [private_public_complete, simulateQ_spec_query, evalKem_coins]
  | inr query =>
      change (simulateQ (privateImpl attachedVerify primitives count)
        (localCoins (evalKem baseImpl kem secret (MlKemCCAOracleSpec baseSpec |>.query query)))).run state =
        evalKem baseImpl kem secret (((MlKemCCAOracleSpec baseSpec).query query : OracleComp (MlKemCCAOracleSpec baseSpec) _) >>= fun answer => pure (answer, state))
      rw [private_local_complete, evalKem_bind]
      simp only [evalKem, simulateQ_pure, bind_pure_comp]

/-- Full adaptive oracle simulation retains the entire private identity state and unchanged selector output; the target KEM secret appears only in its CCA interpreter. -/
theorem localSelector_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (SelectorSpec baseSpec) Result) (state : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (simulateQ (localSelector baseImpl kem secret) client)).run state =
      evalKem baseImpl kem secret ((simulateQ (borrowedSelector attachedVerify primitives count) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalKem_bind]
      rw [localSelector_step]
      simp only [ih]

/-- Independent identity/prekey generation is retained jointly before the KEM draw. -/
def identityPreSample (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) : ProbComp (IdentitySeed × PrivatePrekey setup.PrivatePre) := do
  let seed ← sampleSeed
  let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey (primitives.publicKeys seed).ed25519)
  pure (seed, before)

/-- Moving the independent target key pair quantifies over the entire evaluated private continuation, including one-time generation and all later state. -/
theorem generators_complete_continuation {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (next : IdentitySeed → Generated setup KemSK → ProbComp Result) :
    𝒮[do let seed ← sampleSeed
         let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
         next seed generated] =
      𝒮[do let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
           let retained ← identityPreSample baseImpl primitives setup
           let after ← simulateQ (kemAmbientImpl baseImpl)
             (setup.oneTime (primitives.publicKeys retained.1).ed25519 retained.2 pair.1)
           next retained.1 ⟨retained.2, pair.1, pair.2, after⟩] := by
  have commute := PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy (identityPreSample baseImpl primitives setup)
    (simulateQ (kemAmbientImpl baseImpl) kem.keygen)
    (fun retained pair => do
      let after ← simulateQ (kemAmbientImpl baseImpl)
        (setup.oneTime (primitives.publicKeys retained.1).ed25519 retained.2 pair.1)
      next retained.1 ⟨retained.2, pair.1, pair.2, after⟩)
  simpa only [identityPreSample, generate, bind_assoc, pure_bind] using commute

/-- Explicit primitive/uniform forwarding retains the ordinary CCA ambient query classes. -/
def ccaAmbient {Result : Type} (client : OracleComp (unifSpec + baseSpec) Result) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Result :=
  simulateQ (fun query => ((MlKemCCAOracleSpec baseSpec).query (.inl query) :
    OracleComp (MlKemCCAOracleSpec baseSpec) _)) client

/-- Evaluating the borrowed ambient interface gives the same fixed full probabilistic computation. -/
theorem evalKem_ambient {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (unifSpec + baseSpec) Result) :
    evalKem baseImpl kem secret (ccaAmbient client) = simulateQ (kemAmbientImpl baseImpl) client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [ccaAmbient, simulateQ_bind, simulateQ_spec_query, evalKem]
      have baseQuery :
          simulateQ (kemAmbientImpl baseImpl) (localKemPreChallengeImpl kem secret (.inl query)) =
            kemAmbientImpl baseImpl query := by
        unfold localKemPreChallengeImpl KEMScheme.IND_CCA_preChallengeImpl QueryImpl.add
        simp only [HasQuery.toQueryImpl_apply, simulateQ_HasQuery_query]
      rw [baseQuery]
      change (kemAmbientImpl baseImpl query >>= fun answer =>
        evalKem baseImpl kem secret (ccaAmbient (next answer))) = _
      simp only [ih]

end BeaconcryptCore.Computational.PqxdhPrivateKemSource

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.generate_key_support' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.generate_key_support

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.source_generation_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.source_generation_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem_coins' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.localSelector_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.localSelector_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.localSelector_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.localSelector_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.generators_complete_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.generators_complete_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem_ambient' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem_ambient
