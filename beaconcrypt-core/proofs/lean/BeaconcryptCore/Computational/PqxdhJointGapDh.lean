import BeaconcryptCore.Computational.PqxdhJointIdentity

/-!
This module defines a specialized joint native Gap-DH recovery experiment. Two independently uniform 32-byte strings feed the actual Ed25519 seed/public/signing interface and an X25519 scalar/public interface. The first seed also determines the converted static X25519 operation. The adversary gets correlated public keys, signatures, and two anchored decision services: each answers whether a supplied 32-byte candidate equals the actual optional DH at one challenge-held secret and a chosen peer encoding. Neither service returns raw DH. Invalid inputs retain the primitive's optional behavior. The only winning condition is recovery of the actual nonzero cross-DH; neither None nor all-zero output wins. No protocol authentication, hash pseudorandomness or small-advantage premise is built into the winning predicate.

This is an explicit joint-use, native-byte formulation of a Gap-DH-style recovery endpoint, not a proved equivalence to textbook prime-order GapDH. In particular, it does not posit a global bytes-only DDH relation or public-key injectivity across X25519 cofactor/twist representations. All accepted peer encodings remain queryable, and functional aliases preserve actual replies. The signing capability and exact joint seed distribution must be retained in any eventual primitive hardness contract.

An executable scan reduces occurrence of the target among a fixed candidate vector to this recovery game without a guessing factor; every repeated/failed decision and the full prior history are retained. A separate two-coordinate matcher recognizes the unchanged 192-byte FF32/DH1/DH2/DH3/DH4/SS input using at most two decision requests. DH1 and DH3 are evaluated at challenge-held secrets; DH2, DH4 and SS are explicit supplied values. The original candidate's complete byte shape and all known coordinates are checked. Full stateful continuations preserve both decision observations, even when either test fails. This is input recognition, not a simulation of all derived-output queries or all protocol roles.

The complete challenger pays 64 seed/scalar byte draws plus the adversary's uniform calls. Candidate scanning adds at most its fixed vector length in decision calls and no uniform/signing calls. Matching adds at most two decisions and no uniform/signing calls. Decision-oracle calls are logical reduction resources; deterministic DH, signing, comparisons, byte parsing and history/list work are not free. The optional byte-model source instantiation derives functional agreement from existing source laws; it does not prove native generation/error/ABI correspondence. Shared hash simulation, concrete Extract security, target selection, compromise/ownership policies, correlated root/KEM routing and native global protocol composition remain separate obligations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointGapDh
open PqxdhJointIdentity PqxdhEd25519EufCma

abbrev ScalarBytes := List.Vector UInt8 32

/-- Actual scalar generation/public map and optional primitive DH; no decision oracle or security law is assumed here. -/
structure DhInterface (joint : Primitives) where
  publicKey : ScalarBytes → PeerEncoding
  dh : ScalarBytes → PeerEncoding → Option DhOutput
  agreement : ∀ seed scalar,
    joint.staticDh seed (publicKey scalar) = dh scalar (joint.publicKeys seed).convertedX25519

structure PublicChallenge where
  identity : PublicIdentity
  prekey : PeerEncoding
  deriving DecidableEq

inductive Request where
  | sign (message : Pqxdh.Bytes)
  | decideDh (usePrekey : Bool) (peer : PeerEncoding) (candidate : DhOutput)

def ServiceSpec : OracleSpec Request
  | .sign _ => Ed25519Signature
  | .decideDh _ _ _ => Bool

attribute [reducible] ServiceSpec

abbrev AdversarySpec := unifSpec + ServiceSpec

inductive Observation where
  | sign (message : Pqxdh.Bytes) (signature : Ed25519Signature)
  | decideDh (usePrekey : Bool) (peer : PeerEncoding) (candidate : DhOutput) (answer : Bool)
  deriving DecidableEq

abbrev History := List Observation

def reply (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    (request : ServiceSpec.Domain) → ServiceSpec.Range request
  | .sign message => joint.sign seed message
  | .decideDh usePrekey peer candidate =>
      decide ((if usePrekey then dh.dh scalar peer else joint.staticDh seed peer) = some candidate)

def observation : (request : ServiceSpec.Domain) → ServiceSpec.Range request → Observation
  | .sign message, signature => .sign message signature
  | .decideDh left right candidate, answer => .decideDh left right candidate answer

def serviceImpl (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl AdversarySpec (StateT History ProbComp) := fun query history =>
  match query with
  | .inl coin => do
      let answer ← unifSpec.query coin
      pure (answer, history)
  | .inr request =>
      let answer := reply joint dh seed scalar request
      pure (answer, history ++ [observation request answer])

theorem service_step (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (request : ServiceSpec.Domain) (history : History) :
    (serviceImpl joint dh seed scalar (.inr request)).run history =
      pure (reply joint dh seed scalar request,
        history ++ [observation request (reply joint dh seed scalar request)]) := by
  rfl

def sampleScalar : ProbComp ScalarBytes := $ᵗ ScalarBytes

def challenge (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) : PublicChallenge :=
  ⟨joint.publicKeys seed, dh.publicKey scalar⟩

def run {Result : Type} (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (adversary : PublicChallenge → OracleComp AdversarySpec Result) : ProbComp (Result × History) :=
  (simulateQ (serviceImpl joint dh seed scalar) (adversary (challenge joint dh seed scalar))).run []

/-- Ordinary computational-DH success: a nonzero candidate is the actual optional DH result. No protocol event is tested. -/
def zeroDh : DhOutput := List.Vector.replicate 32 0

def wins (target guess : Option DhOutput) : Bool :=
  match guess with
  | none => false
  | some value => decide (value ≠ zeroDh ∧ target = some value)

def game (joint : Primitives) (dh : DhInterface joint)
    (adversary : PublicChallenge → OracleComp AdversarySpec (Option DhOutput)) : ProbComp Bool := do
  let seed ← sampleSeed
  let scalar ← sampleScalar
  let (guess, _) ← run joint dh seed scalar adversary
  pure (wins (joint.staticDh seed (dh.publicKey scalar)) guess)

noncomputable def advantage (joint : Primitives) (dh : DhInterface joint)
    (adversary : PublicChallenge → OracleComp AdversarySpec (Option DhOutput)) : ℝ≥0∞ :=
  Pr{let x ← game joint dh adversary}[x = true]

/-- Public executable selection uses the ordinary decision service, never either private scalar. -/
def scan (publicValue : PublicChallenge) : List DhOutput → OracleComp AdversarySpec (Option DhOutput)
  | [] => pure none
  | candidate :: rest => do
      let accepted ← (liftM (AdversarySpec.query
        (.inr (.decideDh false publicValue.prekey candidate))) : OracleComp AdversarySpec Bool)
      if accepted then pure (some candidate) else scan publicValue rest

def scanResult (target : Option DhOutput) (candidates : List DhOutput) : Option DhOutput :=
  candidates.find? (fun candidate => decide (target = some candidate))

/-- Exact chronological decision trace; neither a failed decision nor a repeated candidate is omitted. -/
def scanOutcome (publicValue : PublicChallenge) (target : Option DhOutput) :
    List DhOutput → History → Option DhOutput × History
  | [], history => (none, history)
  | candidate :: rest, history =>
      let accepted := decide (target = some candidate)
      let nextHistory := history ++ [.decideDh false publicValue.prekey candidate accepted]
      if accepted then (some candidate, nextHistory) else scanOutcome publicValue target rest nextHistory

theorem scan_full (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidates : List DhOutput) (history : History) :
    (simulateQ (serviceImpl joint dh seed scalar)
      (scan (challenge joint dh seed scalar) candidates)).run history =
      pure (scanOutcome (challenge joint dh seed scalar)
        (joint.staticDh seed (dh.publicKey scalar)) candidates history) := by
  induction candidates generalizing history with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [scan, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        challenge]
      change (simulateQ (serviceImpl joint dh seed scalar)
        (if decide (joint.staticDh seed (dh.publicKey scalar) = some candidate) then
          pure (some candidate) else scan (challenge joint dh seed scalar) rest)).run _ = _
      by_cases found : joint.staticDh seed (dh.publicKey scalar) = some candidate
      · simp [found, scanOutcome, observation, reply]
      · simpa [found, scanOutcome, challenge, observation, reply] using ih _

/-- Executable first-match scan returns exactly the first candidate equal to the real DH output. -/
theorem scan_complete (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidates : List DhOutput) (history : History) :
    (Prod.fst <$> (simulateQ (serviceImpl joint dh seed scalar)
      (scan (challenge joint dh seed scalar) candidates)).run history) =
      pure (scanResult (joint.staticDh seed (dh.publicKey scalar)) candidates) := by
  induction candidates generalizing history with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [scan, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        challenge]
      change (Prod.fst <$> (simulateQ (serviceImpl joint dh seed scalar)
        (if decide (joint.staticDh seed (dh.publicKey scalar) = some candidate) then
          pure (some candidate) else scan (challenge joint dh seed scalar) rest)).run _) = _
      by_cases found : joint.staticDh seed (dh.publicKey scalar) = some candidate
      · simp [found, scanResult]
      · simpa only [found, decide_false, Bool.false_eq_true, ite_false, scanResult,
          List.find?_cons] using ih _

theorem wins_none (target : Option DhOutput) : wins target none = false := by
  rfl

theorem wins_zero (target : Option DhOutput) : wins target (some zeroDh) = false := by
  simp [wins]

theorem failed_target (guess : Option DhOutput) : wins none guess = false := by
  cases guess <;> simp [wins]

theorem target_agreement (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    joint.staticDh seed (dh.publicKey scalar) = dh.dh scalar (joint.publicKeys seed).convertedX25519 :=
  dh.agreement seed scalar

theorem scanResult_wins (target : Option DhOutput) (candidates : List DhOutput) :
    wins target (scanResult target candidates) =
      decide (∃ value, target = some value ∧ value ≠ zeroDh ∧ value ∈ candidates) := by
  cases target with
  | none => simp [failed_target]
  | some value =>
    induction candidates with
    | nil => simp [scanResult, wins]
    | cons candidate rest ih =>
      by_cases same : value = candidate
      · subst candidate
        simp [scanResult, wins]
      · simpa [scanResult, List.find?_cons, same, wins] using ih


def IsUniform (query : AdversarySpec.Domain) : Prop := query.isLeft = true

def IsSigning : AdversarySpec.Domain → Prop
  | .inr (.sign _) => True
  | _ => False

def IsDecision : AdversarySpec.Domain → Prop
  | .inr (.decideDh _ _ _) => True
  | _ => False

instance : DecidablePred IsUniform := fun query => inferInstanceAs (Decidable (query.isLeft = true))
instance : DecidablePred IsSigning := fun query => by cases query with
  | inl _ => exact isFalse (by simp [IsSigning])
  | inr request => cases request <;> unfold IsSigning <;> infer_instance
instance : DecidablePred IsDecision := fun query => by cases query with
  | inl _ => exact isFalse (by simp [IsDecision])
  | inr request => cases request <;> unfold IsDecision <;> infer_instance

theorem service_uniform_step (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : AdversarySpec.Domain) (history : History) :
    ((serviceImpl joint dh seed scalar query).run history).IsQueryBoundP (fun _ => True)
      (if IsUniform query then 1 else 0) := by
  cases query with
  | inl coin =>
    change OracleComp.IsQueryBoundP
      ((fun answer => (answer, history)) <$> (unifSpec.query coin : ProbComp _)) (fun _ => True) 1
    simp only [OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by simp)
  | inr request =>
    cases request <;> change (pure _ : ProbComp _).IsQueryBoundP (fun _ => True) 0 <;> trivial

theorem run_uniform (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Result : Type}
    (client : OracleComp AdversarySpec Result) (qUniform : Nat)
    (bounded : client.IsQueryBoundP IsUniform qUniform) (history : History) :
    ((simulateQ (serviceImpl joint dh seed scalar) client).run history).IsTotalQueryBound qUniform :=
  (OracleComp.isQueryBoundP_true_iff _ _).mp
    (bounded.simulateQ_run_StateT_of_step (service_uniform_step joint dh seed scalar) history)

theorem sampleScalar_uniform : sampleScalar.IsTotalQueryBound 32 :=
  CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

theorem game_uniform (joint : Primitives) (dh : DhInterface joint)
    (adversary : PublicChallenge → OracleComp AdversarySpec (Option DhOutput))
    (qUniform : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP IsUniform qUniform) :
    (game joint dh adversary).IsTotalQueryBound (64 + qUniform) := by
  have budget : 64 + qUniform = 32 + (32 + qUniform) := by omega
  rw [budget]
  unfold game
  apply OracleComp.isTotalQueryBound_bind sampleSeed_uniform_bound
  intro seed
  apply OracleComp.isTotalQueryBound_bind sampleScalar_uniform
  intro scalar
  simpa only [run, bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    run_uniform joint dh seed scalar (adversary (challenge joint dh seed scalar)) qUniform (bounded _) []

/-- Public description of a two-coordinate DH input. Values in the other three coordinates are explicitly supplied, not silently computable secret values. -/
structure TupleAddress where
  staticPeer : PeerEncoding
  prekeyPeer : PeerEncoding
  second : DhOutput
  fourth : DhOutput
  kem : DhOutput
  deriving DecidableEq

def assemble (address : TupleAddress) (first third : DhOutput) : Pqxdh.Bytes :=
  List.replicate 32 255 ++ first.toList ++ address.second.toList ++ third.toList ++
    address.fourth.toList ++ address.kem.toList

def readDh (offset : Nat) (input : Pqxdh.Bytes) : Option DhOutput :=
  let bytes := (input.drop offset).take 32
  if width : bytes.length = 32 then some ⟨bytes, width⟩ else none

theorem assemble_length (address : TupleAddress) (first third : DhOutput) :
    (assemble address first third).length = 192 := by
  simp [assemble]

theorem read_first (address : TupleAddress) (first third : DhOutput) :
    readDh 32 (assemble address first third) = some first := by
  simp [readDh, assemble, List.append_assoc, List.drop_append]

theorem read_third (address : TupleAddress) (first third : DhOutput) :
    readDh 96 (assemble address first third) = some third := by
  simp [readDh, assemble, List.append_assoc, List.drop_append]

theorem assemble_eq_iff (address : TupleAddress) (first third otherFirst otherThird : DhOutput) :
    assemble address first third = assemble address otherFirst otherThird ↔
      first = otherFirst ∧ third = otherThird := by
  constructor
  · intro same
    constructor
    · exact Option.some.inj (by simpa only [read_first] using congrArg (readDh 32) same)
    · exact Option.some.inj (by simpa only [read_third] using congrArg (readDh 96) same)
  · rintro ⟨rfl, rfl⟩
    rfl

def sourceInput (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (address : TupleAddress) : Option Pqxdh.Bytes := do
  let first ← joint.staticDh seed address.staticPeer
  let third ← dh.dh scalar address.prekeyPeer
  pure (assemble address first third)

theorem sourceInput_some_iff (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (address : TupleAddress) (input : Pqxdh.Bytes) :
    sourceInput joint dh seed scalar address = some input ↔
      ∃ first third, joint.staticDh seed address.staticPeer = some first ∧
        dh.dh scalar address.prekeyPeer = some third ∧ assemble address first third = input := by
  simp [sourceInput, Option.bind_eq_some_iff]

def candidateCoordinates (address : TupleAddress) (input : Pqxdh.Bytes) : Option (DhOutput × DhOutput) := do
  let first ← readDh 32 input
  let third ← readDh 96 input
  if input = assemble address first third then pure (first, third) else none

theorem candidateCoordinates_some_iff (address : TupleAddress) (input : Pqxdh.Bytes)
    (first third : DhOutput) :
    candidateCoordinates address input = some (first, third) ↔ input = assemble address first third := by
  constructor
  · intro accepted
    simp [candidateCoordinates, Option.bind_eq_some_iff] at accepted
    aesop
  · intro same
    rw [same]
    simp [candidateCoordinates, read_first, read_third]

theorem sourceInput_assembled_iff (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (address : TupleAddress) (first third : DhOutput) :
    sourceInput joint dh seed scalar address = some (assemble address first third) ↔
      joint.staticDh seed address.staticPeer = some first ∧ dh.dh scalar address.prekeyPeer = some third := by
  rw [sourceInput_some_iff]
  simp only [assemble_eq_iff]
  aesop

def testInputResult (firstReply thirdReply : Option DhOutput)
    (address : TupleAddress) (input : Pqxdh.Bytes) : Bool :=
  match candidateCoordinates address input with
  | none => false
  | some (first, third) => decide (firstReply = some first ∧ thirdReply = some third)

theorem testInputResult_exact (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (address : TupleAddress) (input : Pqxdh.Bytes) :
    testInputResult (joint.staticDh seed address.staticPeer) (dh.dh scalar address.prekeyPeer) address input =
      decide (sourceInput joint dh seed scalar address = some input) := by
  cases parsed : candidateCoordinates address input with
  | none =>
    have rejected : sourceInput joint dh seed scalar address ≠ some input := by
      intro accepted
      obtain ⟨first, third, _, _, assembled⟩ := (sourceInput_some_iff joint dh seed scalar address input).mp accepted
      have existsParsed := (candidateCoordinates_some_iff address input first third).mpr assembled.symm
      rw [parsed] at existsParsed
      contradiction
    simp [testInputResult, parsed, rejected]
  | some pair =>
    rcases pair with ⟨first, third⟩
    have same := (candidateCoordinates_some_iff address input first third).mp parsed
    simp only [testInputResult, parsed]
    simp only [same, sourceInput_assembled_iff]

def testInput (address : TupleAddress) (input : Pqxdh.Bytes) : OracleComp AdversarySpec Bool :=
  match candidateCoordinates address input with
  | none => pure false
  | some (first, third) => do
      let firstAccepted ← (liftM (AdversarySpec.query
        (.inr (.decideDh false address.staticPeer first))) : OracleComp AdversarySpec Bool)
      let thirdAccepted ← (liftM (AdversarySpec.query
        (.inr (.decideDh true address.prekeyPeer third))) : OracleComp AdversarySpec Bool)
      pure (firstAccepted && thirdAccepted)

def testOutcome (firstReply thirdReply : Option DhOutput) (address : TupleAddress)
    (input : Pqxdh.Bytes) (history : History) : Bool × History :=
  match candidateCoordinates address input with
  | none => (false, history)
  | some (first, third) =>
      let firstAccepted := decide (firstReply = some first)
      let thirdAccepted := decide (thirdReply = some third)
      (firstAccepted && thirdAccepted, history ++
        [.decideDh false address.staticPeer first firstAccepted,
         .decideDh true address.prekeyPeer third thirdAccepted])

theorem testInput_full (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (address : TupleAddress)
    (input : Pqxdh.Bytes) (history : History) :
    (simulateQ (serviceImpl joint dh seed scalar) (testInput address input)).run history =
      pure (testOutcome (joint.staticDh seed address.staticPeer) (dh.dh scalar address.prekeyPeer)
        address input history) := by
  cases parsed : candidateCoordinates address input with
  | none => simp [testInput, testOutcome, parsed]
  | some pair =>
    rcases pair with ⟨first, third⟩
    simp only [testInput, parsed, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change (pure (_, (history ++ [_]) ++ [_]) : ProbComp _) = _
    simp [testOutcome, parsed, observation, reply, List.append_assoc]

/-- All possible decision replies are counted, independently of their actual distribution. -/
theorem scan_query_bound (publicValue : PublicChallenge) (candidates : List DhOutput) :
    (scan publicValue candidates).IsTotalQueryBound candidates.length := by
  induction candidates with
  | nil => trivial
  | cons candidate rest ih =>
    change ((liftM (AdversarySpec.query
      (.inr (.decideDh false publicValue.prekey candidate))) : OracleComp AdversarySpec Bool) >>=
        fun accepted => if accepted then pure (some candidate) else scan publicValue rest).IsTotalQueryBound
      (candidate :: rest).length
    simp only [List.length_cons]
    rw [OracleComp.isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun answer => ?_⟩
    by_cases accepted : answer = true
    · simp only [accepted, ite_true]
      trivial
    · simpa only [accepted, Bool.false_eq_true, ite_false, Nat.add_sub_cancel] using ih

theorem scan_excludes (publicValue : PublicChallenge) (candidates : List DhOutput)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ side peer candidate, ¬predicate (.inr (.decideDh side peer candidate))) :
    (scan publicValue candidates).IsQueryBoundP predicate 0 := by
  induction candidates with
  | nil => trivial
  | cons candidate rest ih =>
    change ((liftM (AdversarySpec.query
      (.inr (.decideDh false publicValue.prekey candidate))) : OracleComp AdversarySpec Bool) >>=
        fun accepted => if accepted then pure (some candidate) else scan publicValue rest).IsQueryBoundP
      predicate 0
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    have requestExcluded := excluded false publicValue.prekey candidate
    refine ⟨Or.inl requestExcluded, fun answer => ?_⟩
    simp only [requestExcluded, ite_false]
    by_cases accepted : answer = true
    · simp only [accepted, ite_true]
      trivial
    · simpa only [accepted, Bool.false_eq_true, ite_false] using ih

theorem testInput_query_bound (address : TupleAddress) (input : Pqxdh.Bytes) :
    (testInput address input).IsTotalQueryBound 2 := by
  cases parsed : candidateCoordinates address input with
  | none =>
    simp only [testInput, parsed]
    trivial
  | some pair =>
    rcases pair with ⟨first, third⟩
    simp only [testInput, parsed]
    rw [OracleComp.isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun _ => (OracleComp.isTotalQueryBound_query_bind_iff).2
      ⟨by omega, fun _ => trivial⟩⟩

theorem testInput_excludes (address : TupleAddress) (input : Pqxdh.Bytes)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ side peer candidate, ¬predicate (.inr (.decideDh side peer candidate))) :
    (testInput address input).IsQueryBoundP predicate 0 := by
  cases parsed : candidateCoordinates address input with
  | none =>
    simp only [testInput, parsed]
    trivial
  | some pair =>
    rcases pair with ⟨first, third⟩
    simp only [testInput, parsed]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    have firstExcluded := excluded false address.staticPeer first
    refine ⟨Or.inl firstExcluded, fun firstAccepted => ?_⟩
    simp only [firstExcluded, ite_false]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    have thirdExcluded := excluded true address.prekeyPeer third
    exact ⟨Or.inl thirdExcluded, fun _ => by simp [thirdExcluded]⟩

theorem testOutcome_value (firstReply thirdReply : Option DhOutput) (address : TupleAddress)
    (input : Pqxdh.Bytes) (history : History) :
    (testOutcome firstReply thirdReply address input history).1 =
      testInputResult firstReply thirdReply address input := by
  cases parsed : candidateCoordinates address input with
  | none => simp [testOutcome, testInputResult, parsed]
  | some pair => cases pair; simp [testOutcome, testInputResult, parsed]

theorem testInput_continuation (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (address : TupleAddress)
    (input : Pqxdh.Bytes) (history : History) {Result : Type}
    (next : Bool → History → ProbComp Result) :
    ((simulateQ (serviceImpl joint dh seed scalar) (testInput address input)).run history >>=
      fun output => next output.1 output.2) =
      next (decide (sourceInput joint dh seed scalar address = some input))
        (testOutcome (joint.staticDh seed address.staticPeer) (dh.dh scalar address.prekeyPeer)
          address input history).2 := by
  rw [testInput_full]
  change next (testOutcome _ _ _ _ _).1 (testOutcome _ _ _ _ _).2 = _
  rw [testOutcome_value, testInputResult_exact]

def extractor {count : Nat}
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count))
    (publicValue : PublicChallenge) : OracleComp AdversarySpec (Option DhOutput) := do
  let candidates ← client publicValue
  scan publicValue candidates.toList

def candidateGame {count : Nat} (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count)) : ProbComp Bool := do
  let seed ← sampleSeed
  let scalar ← sampleScalar
  let (candidates, _) ← run joint dh seed scalar client
  pure (decide (∃ value, joint.staticDh seed (dh.publicKey scalar) = some value ∧
    value ≠ zeroDh ∧ value ∈ candidates.toList))

theorem scan_final (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidates : List DhOutput) (history : History) :
    ((simulateQ (serviceImpl joint dh seed scalar)
      (scan (challenge joint dh seed scalar) candidates)).run history >>=
        fun output => pure (wins (joint.staticDh seed (dh.publicKey scalar)) output.1)) =
      pure (decide (∃ value, joint.staticDh seed (dh.publicKey scalar) = some value ∧
        value ≠ zeroDh ∧ value ∈ candidates)) := by
  have projected := congrArg (fun computation : ProbComp (Option DhOutput) =>
    wins (joint.staticDh seed (dh.publicKey scalar)) <$> computation)
    (scan_complete joint dh seed scalar candidates history)
  simpa only [monad_norm, Function.comp_def, pure_bind, scanResult_wins]
    using projected

theorem extraction_game {count : Nat} (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count)) :
    game joint dh (extractor client) = candidateGame joint dh client := by
  simp only [game, candidateGame, run, extractor, simulateQ_bind, StateT.run_bind,
    bind_assoc, scan_final]

theorem candidate_success_eq_advantage {count : Nat} (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count)) :
    Pr{let x ← candidateGame joint dh client}[x = true] = advantage joint dh (extractor client) := by
  rw [advantage, extraction_game]

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.PqxdhJointGapDh.candidate_success_eq_advantage_vcvioLegacy :
    ∀ {count : ℕ} (joint : BeaconcryptCore.Computational.PqxdhJointIdentity.Primitives) (dh : BeaconcryptCore.Computational.PqxdhJointGapDh.DhInterface joint) (client : BeaconcryptCore.Computational.PqxdhJointGapDh.PublicChallenge → OracleComp BeaconcryptCore.Computational.PqxdhJointGapDh.AdversarySpec (List.Vector BeaconcryptCore.Computational.PqxdhJointIdentity.DhOutput count)), Pr[= Bool.true | BeaconcryptCore.Computational.PqxdhJointGapDh.candidateGame joint dh client] = BeaconcryptCore.Computational.PqxdhJointGapDh.advantage joint dh (BeaconcryptCore.Computational.PqxdhJointGapDh.extractor client) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhJointGapDh.candidate_success_eq_advantage

theorem extractor_class_bound {count : Nat}
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count))
    (publicValue : PublicChallenge) (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (budget : Nat) (bounded : (client publicValue).IsQueryBoundP predicate budget) :
    (extractor client publicValue).IsQueryBoundP predicate (budget + count) := by
  apply OracleComp.isQueryBoundP_bind bounded
  intro candidates _
  have width : candidates.toList.length = count := candidates.2
  simpa only [width] using
    (scan_query_bound publicValue candidates.toList).isQueryBoundP (p := predicate)

theorem extractor_excludes {count : Nat}
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count))
    (publicValue : PublicChallenge) (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ side peer candidate, ¬predicate (.inr (.decideDh side peer candidate)))
    (budget : Nat) (bounded : (client publicValue).IsQueryBoundP predicate budget) :
    (extractor client publicValue).IsQueryBoundP predicate budget := by
  simpa only [extractor, Nat.add_zero] using OracleComp.isQueryBoundP_bind bounded
    (fun candidates _ => scan_excludes publicValue candidates.toList predicate excluded)

theorem extractor_uniform {count : Nat}
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count))
    (publicValue : PublicChallenge) (budget : Nat)
    (bounded : (client publicValue).IsQueryBoundP IsUniform budget) :
    (extractor client publicValue).IsQueryBoundP IsUniform budget :=
  extractor_excludes client publicValue IsUniform (by intros; simp [IsUniform]) budget bounded

theorem extractor_signing {count : Nat}
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count))
    (publicValue : PublicChallenge) (budget : Nat)
    (bounded : (client publicValue).IsQueryBoundP IsSigning budget) :
    (extractor client publicValue).IsQueryBoundP IsSigning budget :=
  extractor_excludes client publicValue IsSigning (by intros; simp [IsSigning]) budget bounded

theorem extractor_game_uniform {count : Nat} (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp AdversarySpec (List.Vector DhOutput count))
    (budget : Nat) (bounded : ∀ publicValue, (client publicValue).IsQueryBoundP IsUniform budget) :
    (game joint dh (extractor client)).IsTotalQueryBound (64 + budget) :=
  game_uniform joint dh (extractor client) budget
    (fun publicValue => extractor_uniform client publicValue budget (bounded publicValue))

theorem static_alias_decision (joint : Primitives) (dh : DhInterface joint)
    (aliases : PeerEquivalence joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (left right : PeerEncoding) (candidate : DhOutput) (same : aliases.same left right) :
    reply joint dh seed scalar (.decideDh false left candidate) =
      reply joint dh seed scalar (.decideDh false right candidate) := by
  simp only [reply, Bool.false_eq_true, ite_false, aliases.replies seed left right same]

def sourceScalarDh (c : Pqxdh.Crypto) (scalar : ScalarBytes) (peer : PeerEncoding) : Option DhOutput :=
  let output : DhOutput := ⟨c.x25519 scalar.toList peer.toList, c.x25519_length _ _⟩
  if output.toList = Pqxdh.zero32 then none else some output

def sourceInterface (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed) :
    DhInterface joint where
  publicKey scalar := ⟨c.xpub scalar.toList, c.xpub_length _⟩
  dh := sourceScalarDh c
  agreement := by
    intro seed scalar
    change joint.staticDh seed
      (show PeerEncoding from ⟨c.xpub scalar.toList, c.xpub_length _⟩) =
        sourceScalarDh c scalar (joint.publicKeys seed).convertedX25519
    rw [wiring.staticDh]
    simp only [sourceDhReply, sourceScalarDh, wiring.xPublic, List.Vector.toList_mk]
    have same := c.dh_comm (c.xsk (secretOfSeed seed).toList) scalar.toList
    simp only [same]

theorem assemble_source (address : TupleAddress) (first third : DhOutput) :
    assemble address first third = Pqxdh.pqxdhIKM first.toList address.second.toList
      third.toList address.fourth.toList address.kem.toList := by
  rfl

/-- The two unknown coordinates are precisely the source beacon's prekey/static and prekey/ephemeral calls; other validated primitive outputs remain explicit inputs. -/
theorem source_target_input (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (ephemeral : PeerEncoding)
    (second fourth kem : DhOutput) :
    sourceInput joint (sourceInterface c joint secretOfSeed wiring) seed scalar
      ⟨(sourceInterface c joint secretOfSeed wiring).publicKey scalar, ephemeral, second, fourth, kem⟩ =
      (do let first ← sourceScalarDh c scalar (joint.publicKeys seed).convertedX25519
          let third ← sourceScalarDh c scalar ephemeral
          pure (Pqxdh.pqxdhIKM first.toList second.toList third.toList fourth.toList kem.toList)) := by
  unfold sourceInput
  rw [(sourceInterface c joint secretOfSeed wiring).agreement]
  rfl

end BeaconcryptCore.Computational.PqxdhJointGapDh

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.service_step' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.service_step

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.scan_full' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.scan_full

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.scan_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.scan_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.wins_none' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.wins_none

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.wins_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.wins_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.failed_target' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.failed_target

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.target_agreement' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.target_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.scanResult_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.scanResult_wins

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.service_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.service_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.run_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.run_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.sampleScalar_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.sampleScalar_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.game_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.game_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.assemble_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.assemble_length

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.read_first' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.read_first

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.read_third' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.read_third

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.assemble_eq_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.assemble_eq_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.sourceInput_some_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.sourceInput_some_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.candidateCoordinates_some_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.candidateCoordinates_some_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.sourceInput_assembled_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.sourceInput_assembled_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.testInputResult_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.testInputResult_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_full' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_full

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.scan_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.scan_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.scan_excludes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.scan_excludes

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_query_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_excludes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_excludes

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.testOutcome_value' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.testOutcome_value

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_continuation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.testInput_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.scan_final' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.scan_final

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.extraction_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.extraction_game

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.candidate_success_eq_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.candidate_success_eq_advantage

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_excludes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_excludes

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_signing

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.extractor_game_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.static_alias_decision' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.static_alias_decision

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.assemble_source' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.assemble_source

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.source_target_input' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.source_target_input

/--
info: 'BeaconcryptCore.Computational.PqxdhJointGapDh.sourceInterface' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointGapDh.sourceInterface
