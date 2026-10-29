import BeaconcryptCore.Computational.PqxdhJointDhExtractFamily

/-! The native related-input fixed-Extract primitive additionally represents a selected Beacon prekey with an arbitrary admitted Server pin and ordinary fully supplied DH coordinates. Its real game computes the actual optional first and third DH values; its ideal game randomizes only full 192-byte inputs whose first DH equals the selected cross-DH value. This is an explicitly broader ordinary distinguishing advantage than the legacy related-input primitive. The legacy Family and Gap-DH decision interface remain unchanged. All tables retain literal input aliases, and public HMAC evaluations stay real. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.RegistrationNativeRelatedFamily
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

inductive Third where
  | known : DhOutput → Third
  | selected : PeerEncoding → Third
  | pinned : PeerEncoding → Third
  | supplied : DhOutput → DhOutput → Third
  deriving DecidableEq

structure Message where
  staticPeer : PeerEncoding
  third : Third
  second : DhOutput
  fourth : DhOutput
  kem : DhOutput
  deriving DecidableEq

/-- Only the selected form calls the challenge-held prekey. Server ephemerals have locally available third coordinates. -/
def thirdValue (joint : Primitives) (dh : DhInterface joint) (scalar : ScalarBytes) : Third → Option DhOutput
  | .known value => some value
  | .selected peer | .pinned peer => dh.dh scalar peer
  | .supplied _ third => some third

/-- Pinned Beacon roots use the selected prekey with the actual converted Server pin. Legacy requests keep their selected Server identity interpretation. -/
def firstValue (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) : Option DhOutput :=
  match message.third with
  | .pinned _ => dh.dh scalar message.staticPeer
  | .supplied first _ => some first
  | .known _ | .selected _ => joint.staticDh seed message.staticPeer

/-- Legacy requests enter the broader native language without changing any field or optional computation. -/
def Message.ofLegacy (message : PqxdhJointDhExtractFamily.Message) : Message :=
  ⟨message.staticPeer, match message.third with
    | .known value => .known value
    | .selected peer => .selected peer,
    message.second, message.fourth, message.kem⟩

def Message.toLegacy? (message : Message) : Option PqxdhJointDhExtractFamily.Message :=
  match message.third with
  | .known value => some ⟨message.staticPeer, .known value, message.second, message.fourth, message.kem⟩
  | .selected peer => some ⟨message.staticPeer, .selected peer, message.second, message.fourth, message.kem⟩
  | .pinned _ | .supplied _ _ => none

/-- Peer metadata is not part of the input; actual DH byte aliases must coalesce. -/
def address (message : Message) : PqxdhJointGapDh.TupleAddress :=
  ⟨message.staticPeer, message.staticPeer, message.second, message.fourth, message.kem⟩

/-- The challenger alone evaluates the unavailable static seed and, when requested, selected prekey scalar. Optional failures retain their actual order. -/
def input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) : Option Pqxdh.Bytes := do
  let first ← firstValue joint dh seed scalar message
  let third ← thirdValue joint dh scalar message.third
  pure (PqxdhJointGapDh.assemble (address message) first third)

/-- Protection is a property of the actual input bytes, never of the raw peer encoding or request constructor. -/
def Protected (target : Option DhOutput) (bytes : Pqxdh.Bytes) : Prop :=
  target.isSome = true ∧ PqxdhJointGapDh.readDh 32 bytes = target

instance (target : Option DhOutput) (bytes : Pqxdh.Bytes) : Decidable (Protected target bytes) :=
  inferInstanceAs (Decidable (target.isSome = true ∧ PqxdhJointGapDh.readDh 32 bytes = target))

inductive Request where
  | sign : Pqxdh.Bytes → Request
  | publicHmac : HmacBlock → Pqxdh.Bytes → Request
  | derive : Message → Request

abbrev PrimitiveSpec : OracleSpec Request
  | .sign _ => PqxdhEd25519EufCma.Ed25519Signature
  | .publicHmac _ _ => HmacBlock
  | .derive _ => Option HmacBlock

abbrev Spec := unifSpec + PrimitiveSpec

inductive Observation where
  | sign : Pqxdh.Bytes → PqxdhEd25519EufCma.Ed25519Signature → Observation
  | publicHmac : HmacBlock → Pqxdh.Bytes → HmacBlock → Observation
  | derive : Message → Option HmacBlock → Observation

abbrev History := List Observation

structure State where
  history : History
  cache : HmacOracle.QueryCache

def empty : State := ⟨[], ∅⟩

/-- Even repeat real evaluations compute the fixed primitive; the cache is retained analysis instrumentation. -/
def actualExtract (hmac : HmacSha512) : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp) :=
  fun bytes cache =>
    let prk := extract hmac bytes
    pure (prk, cache.cacheQuery bytes prk)

/-- Known and unrelated side inputs keep the fixed function. Protected full-input aliases share one random table. -/
noncomputable def protectedExtract (hmac : HmacSha512) (target : Option DhOutput) :
    QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp) := fun bytes =>
  if Protected target bytes then HmacOracle.randomOracle bytes else actualExtract hmac bytes

/-- Both modes have exactly the same public algorithm, same-seed signing, and optional input rejection. Only the private Extract reply service differs. -/
noncomputable def impl (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp)) :
    QueryImpl Spec (StateT State ProbComp) := fun query state =>
  match query with
  | .inl coin => do
      let value ← unifSpec.query coin
      pure (value, state)
  | .inr (.sign message) =>
      let signature := joint.sign seed message
      pure (signature, { state with history := state.history ++ [.sign message signature] })
  | .inr (.publicHmac key message) =>
      let block := hmac.eval key message
      pure (block, { state with history := state.history ++ [.publicHmac key message block] })
  | .inr (.derive message) =>
      match input joint dh seed scalar message with
      | none => pure (none, { state with history := state.history ++ [.derive message none] })
      | some bytes => do
          let result ← (extractImpl bytes).run state.cache
          pure (some result.1, ⟨state.history ++ [.derive message (some result.1)], result.2⟩)

noncomputable def realImpl (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) : QueryImpl Spec (StateT State ProbComp) :=
  impl hmac joint dh seed scalar (actualExtract hmac)

noncomputable def idealImpl (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) : QueryImpl Spec (StateT State ProbComp) :=
  impl hmac joint dh seed scalar
    (protectedExtract hmac (joint.staticDh seed (dh.publicKey scalar)))

/-- The endpoint samples the identity seed, then prekey scalar, followed by the full adaptive client. A source generator interchange is not asserted. -/
noncomputable def realGame (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp Spec Bool) : ProbComp Bool := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  (simulateQ (realImpl hmac joint dh seed scalar) (client (PqxdhJointGapDh.challenge joint dh seed scalar))).run' empty

noncomputable def idealGame (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp Spec Bool) : ProbComp Bool := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  (simulateQ (idealImpl hmac joint dh seed scalar) (client (PqxdhJointGapDh.challenge joint dh seed scalar))).run' empty

/-- This additional primitive/distribution obligation is an ordinary distinguishing advantage. Its smallness is not assumed or proved. -/
noncomputable def advantage (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp Spec Bool) : ℝ :=
  (realGame hmac joint dh client).boolDistance (idealGame hmac joint dh client)

/-- Actual byte assembly preserves both optional DH computations without an injectivity assumption. -/
theorem input_some_iff (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes) :
    input joint dh seed scalar message = some bytes ↔
      ∃ first third, firstValue joint dh seed scalar message = some first ∧
        thirdValue joint dh scalar message.third = some third ∧
        PqxdhJointGapDh.assemble (address message) first third = bytes := by
  simp [input, Option.bind_eq_some_iff]

/-- A supplied message denotes exactly one optional 192-byte source input. -/
theorem input_length (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) : bytes.length = 192 := by
  simp [input, Option.bind_eq_some_iff] at present
  obtain ⟨first, _, third, _, assembled⟩ := present
  rw [← assembled]
  exact PqxdhJointGapDh.assemble_length _ _ _

/-- Every successful input is protected exactly when its actual static-DH reply is the selected cross-DH value. A different peer encoding is not an exclusion. -/
theorem input_protected_iff (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (present : input joint dh seed scalar message = some bytes) :
    Protected (joint.staticDh seed (dh.publicKey scalar)) bytes ↔
      firstValue joint dh seed scalar message = joint.staticDh seed (dh.publicKey scalar) := by
  obtain ⟨first, third, firstReply, _, rfl⟩ := (input_some_iff joint dh seed scalar message bytes).mp present
  rw [firstReply]
  simp only [Protected, PqxdhJointGapDh.read_first]
  cases joint.staticDh seed (dh.publicKey scalar) <;> simp

/-- Public evaluations use the original fixed HMAC in every world, including zero-salt Extract guesses; they do not consult or program the private table. -/
theorem public_evaluation (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp))
    (key : HmacBlock) (bytes : Pqxdh.Bytes) (state : State) :
    (impl hmac joint dh seed scalar extractImpl (.inr (.publicHmac key bytes))).run state =
      pure (hmac.eval key bytes, { state with history := state.history ++ [.publicHmac key bytes (hmac.eval key bytes)] }) := by
  rfl

/-- The real service returns exactly fixed-zero-salt Extract at the native optional input and retains the full history and actual-input cache. -/
theorem real_derive (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (state : State) :
    (realImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      match input joint dh seed scalar message with
      | none => pure (none, { state with history := state.history ++ [.derive message none] })
      | some bytes =>
          let prk := extract hmac bytes
          pure (some prk, ⟨state.history ++ [.derive message (some prk)], state.cache.cacheQuery bytes prk⟩) := by
  cases actual : input joint dh seed scalar message <;> simp [realImpl, impl, actual, actualExtract, StateT.run]

/-- Optional invalid-DH rejection is identical in the real and ideal services and leaves the full table unchanged. -/
theorem rejected (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp))
    (message : Message) (state : State) (invalid : input joint dh seed scalar message = none) :
    (impl hmac joint dh seed scalar extractImpl (.inr (.derive message))).run state =
      pure (none, { state with history := state.history ++ [.derive message none] }) := by
  unfold impl
  change (match input joint dh seed scalar message with
    | none => pure (none, { state with history := state.history ++ [Observation.derive message none] })
    | some bytes => _) = _
  rw [invalid]

/-- An unrelated actual DH1 reply keeps the complete real service, even with a selected third coordinate. This covers attacker-computable side sessions without a public-Extract inconsistency. -/
theorem side_real (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (state : State)
    (separate : firstValue joint dh seed scalar message ≠ joint.staticDh seed (dh.publicKey scalar)) :
    (idealImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      (realImpl hmac joint dh seed scalar (.inr (.derive message))).run state := by
  cases actual : input joint dh seed scalar message with
  | none => simp [idealImpl, realImpl, impl, actual, StateT.run]
  | some bytes =>
      have off : ¬ Protected (joint.staticDh seed (dh.publicKey scalar)) bytes :=
        fun present => separate ((input_protected_iff joint dh seed scalar message bytes actual).mp present)
      simp [idealImpl, realImpl, impl, actual, protectedExtract, off, StateT.run]

set_option backward.isDefEq.respectTransparency false in
/-- Every protected input alias reuses the installed complete PRK; the entire cache remains unchanged. -/
theorem protected_hit (hmac : HmacSha512) (target : Option DhOutput)
    (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache) (prk : HmacBlock)
    (inside : Protected target bytes) (hit : cache bytes = some prk) :
    (protectedExtract hmac target bytes).run cache = pure (prk, cache) := by
  simp only [protectedExtract, ite_eq_left inside, randomOracle.apply_eq, StateT.run_bind,
    StateT.run_get, pure_bind, hit, StateT.run_pure]

set_option backward.isDefEq.respectTransparency false in
/-- A new protected full input installs one 64-byte block, shared by all later request aliases. -/
theorem protected_miss (hmac : HmacSha512) (target : Option DhOutput)
    (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache)
    (inside : Protected target bytes) (miss : cache bytes = none) :
    (protectedExtract hmac target bytes).run cache = (do
      let prk ← $ᵗ HmacBlock
      pure (prk, cache.cacheQuery bytes prk)) := by
  simp only [protectedExtract, ite_eq_left inside, randomOracle.apply_eq, StateT.run_bind,
    StateT.run_get, pure_bind, miss, StateT.run_modifyGet]
  change ((do let value ← $ᵗ HmacBlock; pure (value, cache)) >>= fun pair =>
    pure (pair.1, pair.2.cacheQuery bytes pair.1)) = _
  simp only [bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Cache reuse applies to any request with the same actual protected input, including different peer encodings and known/selected-third descriptions. Only its truthful request log differs. -/
theorem derive_hit (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (state : State)
    (bytes : Pqxdh.Bytes) (prk : HmacBlock)
    (present : input joint dh seed scalar message = some bytes)
    (inside : Protected (joint.staticDh seed (dh.publicKey scalar)) bytes)
    (hit : state.cache bytes = some prk) :
    (idealImpl hmac joint dh seed scalar (.inr (.derive message))).run state =
      pure (some prk, ⟨state.history ++ [.derive message (some prk)], state.cache⟩) := by
  simp only [idealImpl, StateT.run, impl, present]
  have cached := protected_hit hmac _ bytes state.cache prk inside hit
  simp only [StateT.run] at cached
  rw [cached]
  simp only [pure_bind]


/-- The additive language round-trips every old request exactly. -/
theorem Message.toLegacy_ofLegacy (message : PqxdhJointDhExtractFamily.Message) :
    (Message.ofLegacy message).toLegacy? = some message := by
  rcases message with ⟨peer, third, second, fourth, kem⟩
  cases third <;> rfl

/-- Old requests retain their actual optional input bytes, including every encoding and DH alias. -/
theorem input_ofLegacy (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message) :
    input joint dh seed scalar (Message.ofLegacy message) = PqxdhJointDhExtractFamily.input joint dh seed scalar message := by
  rcases message with ⟨peer, third, second, fourth, kem⟩
  cases third <;> rfl


def Observation.ofLegacy : PqxdhJointDhExtractFamily.Observation → Observation
  | .sign bytes signature => .sign bytes signature
  | .publicHmac key bytes block => .publicHmac key bytes block
  | .derive message reply => .derive (Message.ofLegacy message) reply

def State.ofLegacy (state : PqxdhJointDhExtractFamily.State) : State :=
  ⟨state.history.map Observation.ofLegacy, state.cache⟩

def legacy : QueryImpl PqxdhJointDhExtractFamily.Spec (OracleComp Spec)
  | .inl coin => Spec.query (.inl coin)
  | .inr (.sign bytes) => Spec.query (.inr (.sign bytes))
  | .inr (.publicHmac key bytes) => Spec.query (.inr (.publicHmac key bytes))
  | .inr (.derive message) => Spec.query (.inr (.derive (Message.ofLegacy message)))

/-- Both real and ideal Extract implementations embed the old request language with the complete history and literal cache preserved. -/
theorem impl_legacy (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl HmacOracle (StateT HmacOracle.QueryCache ProbComp))
    (query : PqxdhJointDhExtractFamily.Spec.Domain) (before : PqxdhJointDhExtractFamily.State) :
    (simulateQ (impl hmac joint dh seed scalar extractImpl) (legacy query)).run (State.ofLegacy before) =
      Prod.map id State.ofLegacy <$>
        (PqxdhJointDhExtractFamily.impl hmac joint dh seed scalar extractImpl query).run before := by
  cases query with
  | inl coin => simp only [legacy, simulateQ_spec_query, impl, PqxdhJointDhExtractFamily.impl,
      State.ofLegacy, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq]
  | inr query => cases query with
    | sign bytes => simp only [legacy, simulateQ_spec_query, impl, PqxdhJointDhExtractFamily.impl,
        State.ofLegacy, StateT.run, Prod.map, id_eq, map_pure, List.map_append, List.map_cons, List.map_nil, Observation.ofLegacy]
    | publicHmac key bytes => simp only [legacy, simulateQ_spec_query, impl, PqxdhJointDhExtractFamily.impl,
        State.ofLegacy, StateT.run, Prod.map, id_eq, map_pure, List.map_append, List.map_cons, List.map_nil, Observation.ofLegacy]
    | derive message =>
        simp only [legacy, simulateQ_spec_query, StateT.run]
        cases actual : PqxdhJointDhExtractFamily.input joint dh seed scalar message <;>
          simp only [impl, PqxdhJointDhExtractFamily.impl, State.ofLegacy, StateT.run, input_ofLegacy, actual, Prod.map, id_eq, map_pure, bind_pure_comp, Functor.map_map,
            List.map_append, List.map_cons, List.map_nil, Observation.ofLegacy]

end BeaconcryptCore.Computational.RegistrationNativeRelatedFamily

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_some_iff

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_protected_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_protected_iff

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.public_evaluation' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.public_evaluation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.real_derive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.real_derive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.rejected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.side_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.side_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.protected_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.protected_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.protected_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.protected_miss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.derive_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.derive_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.Message.toLegacy_ofLegacy' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.Message.toLegacy_ofLegacy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_ofLegacy' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.input_ofLegacy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.impl_legacy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedFamily.impl_legacy
