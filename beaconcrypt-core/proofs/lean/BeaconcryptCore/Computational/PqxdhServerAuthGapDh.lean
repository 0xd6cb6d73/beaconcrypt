import BeaconcryptCore.Computational.PqxdhServerAuthExperiment
import BeaconcryptCore.Computational.PqxdhServerAuthAssumptions

/-!
# Server-authentication Extract-query reduction

This module proves stage B6 of the approved server-authentication experiment. In the restricted zero-salt, 192-byte Extract random-oracle model, an adversary query at the target Beacon's actual root input yields the nonzero cross DH value to a concrete scanning reduction. The bound has coefficient one and uses the existing twist-inclusive, two-secret decision game `PqxdhJointGapDh.game`; the X25519 class law is its only extra functional premise beyond the experiment's setup.

The executable symbolic table receives neither challenge secret. Exact concretization preserves the complete original body, optional replies, family history, table aliases and source query order. Public HMAC outside the Extract slice, including root Expand, stays real. Source rejections and all adaptive continuations remain in the same experiment.

Resource bounds count zero challenge signing requests, at most `2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1) + qH` decision requests for the complete extractor, and `u + 64*(qH+Q+1)` uniform requests. Here `u` is an explicit bound on every uniform request of the concrete source body; it includes primitive/base simulation, honest generation and adversary work. The ordinary Gap-DH game additionally samples its own 64 bytes. No source sampling is declared free.

This establishes the BadB term, not the later per-entry KDF/CTX hops or the complete server-authentication theorem. It neither introduces a serialization contract nor analyzes primitive implementations, snapshots or persistence.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthGapDh
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge zeroDh readDh sourceInterface
  sourceScalarDh)
open PqxdhJointDhExtractFamily (Message Third)
open PqxdhJointDhExtractRoot (RootSpec RootRequest)
open PqxdhServerAuthExperiment (Setup Codec Checks Adversary)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ## The symbolic table -/

/-- A key of the symbolic Extract table: concrete 192 bytes of a public table query, or the message of a root derivation whose bytes the reduction cannot compute. -/
inductive SymKey where
  | concrete (bytes : Pqxdh.Bytes)
  | message (message : Message)

/-- State of the symbolic family: the same family history as the Extract random-oracle family, and the ordered table of keys with their sampled blocks. -/
structure SymState where
  history : PqxdhJointDhExtractFamily.History
  table : List (SymKey × HmacBlock)

/-- The empty symbolic state. -/
def SymState.empty : SymState := ⟨[], []⟩

/-- The fixed reference scalar with which the reduction compares X25519 peers under the class law. -/
def referenceScalar : ScalarBytes := List.Vector.replicate 32 0

/-- A decision request to the Gap-DH services. -/
def decision (usePrekey : Bool) (peer : PeerEncoding) (candidate : DhOutput) : OracleComp PqxdhJointGapDh.AdversarySpec Bool :=
  (liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.decideDh usePrekey peer candidate))) : OracleComp PqxdhJointGapDh.AdversarySpec Bool)

/-- The public coordinates of a Server-shaped root input, whose only unknown coordinate is DH1. -/
structure ServerAddress where
  staticPeer : PeerEncoding
  second : DhOutput
  third : DhOutput
  fourth : DhOutput
  kem : DhOutput
  deriving DecidableEq

/-- The 192-byte root input of a Server-shaped address with first coordinate `first`. -/
def serverBytes (address : ServerAddress) (first : DhOutput) : Pqxdh.Bytes :=
  PqxdhJointGapDh.assemble ⟨address.staticPeer, address.staticPeer, address.second, address.fourth, address.kem⟩
    first address.third

/-- The DH1 coordinate of a candidate, present exactly when the candidate has the address's shape. -/
def serverCoordinate (address : ServerAddress) (candidate : Pqxdh.Bytes) : Option DhOutput := do
  let first ← readDh 32 candidate
  if candidate = serverBytes address first then pure first else none

/-- One-coordinate matcher: one decision on the Server static DH decides whether the candidate is the address's actual root input. -/
def testServer (address : ServerAddress) (candidate : Pqxdh.Bytes) : OracleComp PqxdhJointGapDh.AdversarySpec Bool :=
  match serverCoordinate address candidate with
  | none => pure false
  | some first => decision false address.staticPeer first

/-- Whether concrete bytes are the actual root input of a message: one decision for a known third coordinate, two for a selected one. -/
def concreteTest (message : Message) (candidate : Pqxdh.Bytes) : OracleComp PqxdhJointGapDh.AdversarySpec Bool :=
  match message.third with
  | .known third => testServer ⟨message.staticPeer, message.second, third, message.fourth, message.kem⟩ candidate
  | .selected peer =>
      PqxdhJointGapDh.testInput ⟨message.staticPeer, peer, message.second, message.fourth, message.kem⟩ candidate

/-- Whether two third coordinates have the same actual value: known values are compared, a known value and a selected peer take one decision, and two selected peers are compared under the reference scalar. -/
def thirdSame (c : Pqxdh.Crypto) : Third → Third → OracleComp PqxdhJointGapDh.AdversarySpec Bool
  | .known left, .known right => pure (decide (left = right))
  | .known value, .selected peer => decision true peer value
  | .selected peer, .known value => decision true peer value
  | .selected left, .selected right =>
      pure (decide (sourceScalarDh c referenceScalar left = sourceScalarDh c referenceScalar right))

/-- Whether two messages have the same actual root input, given that the second one has an input: the public coordinates are compared, DH1 under the reference scalar, and the third coordinates by `thirdSame`. -/
def messageSame (c : Pqxdh.Crypto) (left right : Message) : OracleComp PqxdhJointGapDh.AdversarySpec Bool :=
  if left.second = right.second ∧ left.fourth = right.fourth ∧ left.kem = right.kem ∧
      sourceScalarDh c referenceScalar left.staticPeer = sourceScalarDh c referenceScalar right.staticPeer then
    thirdSame c left.third right.third
  else pure false

/-- Whether a table entry's key has the actual bytes of a queried key. -/
def symSame (c : Pqxdh.Crypto) : SymKey → SymKey → OracleComp PqxdhJointGapDh.AdversarySpec Bool
  | .concrete query, .concrete entry => pure (decide (entry = query))
  | .concrete query, .message entry => concreteTest entry query
  | .message query, .concrete entry => concreteTest query entry
  | .message query, .message entry => messageSame c entry query

/-- The block of the first table entry whose key has the queried key's actual bytes. -/
def symLookup (c : Pqxdh.Crypto) (query : SymKey) : List (SymKey × HmacBlock) → OracleComp PqxdhJointGapDh.AdversarySpec (Option HmacBlock)
  | [] => pure none
  | entry :: rest => do
      let hit ← symSame c query entry.1
      if hit then pure (some entry.2) else symLookup c query rest

/-- Uniform coins of a probabilistic computation, as coin queries of the Gap-DH interface. -/
def symCoins {α : Type} (work : ProbComp α) : OracleComp PqxdhJointGapDh.AdversarySpec α :=
  simulateQ (fun query => (liftM (PqxdhJointGapDh.AdversarySpec.query (.inl query)) : OracleComp PqxdhJointGapDh.AdversarySpec _)) work

/-- One table read: a matching entry is returned unchanged; otherwise a uniform block is sampled and appended under the queried key. -/
def symRead (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock)) :
    OracleComp PqxdhJointGapDh.AdversarySpec (HmacBlock × List (SymKey × HmacBlock)) := do
  let found ← symLookup c query table
  match found with
  | some block => pure (block, table)
  | none => do
      let block ← symCoins ($ᵗ HmacBlock)
      pure (block, table ++ [(query, block)])

/-- Public rejection test of a derivation: the Server static DH and, for a selected third coordinate, the prekey DH are accepted by the public domains. -/
def symAccepts (setup : Setup baseSpec KemSK) (message : Message) : Bool :=
  setup.serverDomain.accepts message.staticPeer &&
    match message.third with
    | .known _ => true
    | .selected peer => setup.beaconDomain.accepts peer

/-- The symbolic Extract family, which holds neither the Server seed nor the Beacon's prekey scalar. Coins and signing requests are forwarded to the Gap-DH interface; a public HMAC query outside the table domain is the real function; a table query and an accepted derivation read the symbolic table; a rejected derivation is logged. -/
noncomputable def symImpl (setup : Setup baseSpec KemSK) :
    QueryImpl PqxdhJointDhExtractFamily.Spec (StateT SymState (OracleComp PqxdhJointGapDh.AdversarySpec)) := fun query state =>
  match query with
  | .inl coin => do
      let value ← (liftM (PqxdhJointGapDh.AdversarySpec.query (.inl coin)) : OracleComp PqxdhJointGapDh.AdversarySpec _)
      pure (value, state)
  | .inr (.sign message) => do
      let signature ← (liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.sign message))) : OracleComp PqxdhJointGapDh.AdversarySpec _)
      pure (signature, { state with history := state.history ++ [.sign message signature] })
  | .inr (.publicHmac key message) =>
      if key = zeroSalt ∧ message.length = 192 then do
        let read ← symRead setup.source.crypto (.concrete message) state.table
        pure (read.1, ⟨state.history ++ [.publicHmac key message read.1], read.2⟩)
      else
        let block := setup.hmac.eval key message
        pure (block, { state with history := state.history ++ [.publicHmac key message block] })
  | .inr (.derive message) =>
      if symAccepts setup message then do
        let read ← symRead setup.source.crypto (.message message) state.table
        pure (some read.1, ⟨state.history ++ [.derive message (some read.1)], read.2⟩)
      else pure (none, { state with history := state.history ++ [.derive message none] })

/-- The scanning client: it runs the experiment body with no revealed seed under the symbolic family and outputs the padded DH1 coordinates of the table queries in the family history. -/
noncomputable def scanClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat) (publicValue : PublicChallenge) :
    OracleComp PqxdhJointGapDh.AdversarySpec (List.Vector DhOutput qH) := do
  let result ← (simulateQ (symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction)
    (PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue)).run SymState.empty
  pure (PqxdhServerAuthExperiment.padded qH (PqxdhServerAuthExperiment.romCandidates result.2.history))

/-! ## Concretization -/

/-- The Gap-DH services answered directly with the two secrets, without a history. -/
def answer (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl PqxdhJointGapDh.AdversarySpec ProbComp
  | .inl coin => (unifSpec.query coin : ProbComp _)
  | .inr request => pure (PqxdhJointGapDh.reply joint dh seed scalar request)

/-- The actual bytes of a symbolic key, computed with the two secrets. -/
def keyInput (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) : SymKey → Option Pqxdh.Bytes
  | .concrete bytes => some bytes
  | .message message => PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message

/-- The cache a symbolic table denotes: each input maps to the block of the first entry whose key has those bytes. -/
def symCache (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (table : List (SymKey × HmacBlock)) : HmacOracle.QueryCache := fun bytes =>
  (table.find? (fun entry => decide (keyInput setup seed scalar entry.1 = some bytes))).map Prod.snd

/-- The family state a symbolic state denotes: the same history and the concretized table. -/
def concretize (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (state : SymState) :
    PqxdhJointDhExtractFamily.State :=
  ⟨state.history, symCache setup seed scalar state.table⟩

/-! ## Semantics of the symbolic family -/

/-- The output of a run against the Gap-DH services does not depend on their decision history: it is the run against the stateless answers. -/
theorem service_fst (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (oa : OracleComp PqxdhJointGapDh.AdversarySpec α) (history : PqxdhJointGapDh.History) :
    Prod.fst <$> (simulateQ (PqxdhJointGapDh.serviceImpl joint dh seed scalar) oa).run history =
      simulateQ (answer joint dh seed scalar) oa := by
  induction oa using OracleComp.inductionOn generalizing history with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rcases query with coin | request
      · change ((do let answer ← (unifSpec.query coin : ProbComp _); pure (answer, history)) >>= _) = _
        simp only [bind_assoc, pure_bind, ih]
        rfl
      · rw [PqxdhJointGapDh.service_step]
        simp only [pure_bind, ih]
        rfl

/-- Coins lifted to the Gap-DH interface run the computation itself under the stateless answers. -/
theorem answer_coins (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (work : ProbComp α) :
    simulateQ (answer joint dh seed scalar) (symCoins work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp [symCoins]
  | query_bind query next ih =>
      simp only [symCoins, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      simp only [ih]
      rfl

/-- A decision request is answered with the truth. -/
theorem answer_decision (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (usePrekey : Bool) (peer : PeerEncoding) (candidate : DhOutput) :
    simulateQ (answer joint dh seed scalar) (decision usePrekey peer candidate) =
      pure (decide ((if usePrekey then dh.dh scalar peer else joint.staticDh seed peer) = some candidate)) := by
  simp only [decision, simulateQ_spec_query]
  rfl

/-- The second coordinate of an assembled root input. -/
theorem read_second (address : PqxdhJointGapDh.TupleAddress) (first third : DhOutput) :
    readDh 64 (PqxdhJointGapDh.assemble address first third) = some address.second := by
  have split : PqxdhJointGapDh.assemble address first third =
      (List.replicate 32 255 ++ first.toList) ++
        (address.second.toList ++ (third.toList ++ address.fourth.toList ++ address.kem.toList)) := by
    simp [PqxdhJointGapDh.assemble, List.append_assoc]
  rw [readDh, split, List.drop_left' (by simp), List.take_left' (by simp)]
  simp

/-- The fourth coordinate of an assembled root input. -/
theorem read_fourth (address : PqxdhJointGapDh.TupleAddress) (first third : DhOutput) :
    readDh 128 (PqxdhJointGapDh.assemble address first third) = some address.fourth := by
  have split : PqxdhJointGapDh.assemble address first third =
      (List.replicate 32 255 ++ first.toList ++ address.second.toList ++ third.toList) ++
        (address.fourth.toList ++ address.kem.toList) := by
    simp [PqxdhJointGapDh.assemble, List.append_assoc]
  rw [readDh, split, List.drop_left' (by simp), List.take_left' (by simp)]
  simp

/-- The KEM coordinate of an assembled root input. -/
theorem read_kem (address : PqxdhJointGapDh.TupleAddress) (first third : DhOutput) :
    readDh 160 (PqxdhJointGapDh.assemble address first third) = some address.kem := by
  have split : PqxdhJointGapDh.assemble address first third =
      (List.replicate 32 255 ++ first.toList ++ address.second.toList ++ third.toList ++ address.fourth.toList) ++
        address.kem.toList := by
    simp [PqxdhJointGapDh.assemble, List.append_assoc]
  rw [readDh, split, List.drop_left' (by simp), List.take_of_length_le (by simp)]
  simp

/-- Two assembled root inputs are equal only when all five coordinates are. -/
theorem assemble_inj (left right : PqxdhJointGapDh.TupleAddress) (first third first' third' : DhOutput)
    (same : PqxdhJointGapDh.assemble left first third = PqxdhJointGapDh.assemble right first' third') :
    first = first' ∧ third = third' ∧ left.second = right.second ∧ left.fourth = right.fourth ∧
      left.kem = right.kem := by
  have h1 := congrArg (readDh 32) same
  have h2 := congrArg (readDh 64) same
  have h3 := congrArg (readDh 96) same
  have h4 := congrArg (readDh 128) same
  have h5 := congrArg (readDh 160) same
  simp only [PqxdhJointGapDh.read_first, read_second, PqxdhJointGapDh.read_third, read_fourth, read_kem,
    Option.some.injEq] at h1 h2 h3 h4 h5
  exact ⟨h1, h3, h2, h4, h5⟩

/-- A candidate has a DH1 coordinate for a Server address exactly when it is the address's input with that coordinate. -/
theorem serverCoordinate_some_iff (address : ServerAddress) (candidate : Pqxdh.Bytes) (first : DhOutput) :
    serverCoordinate address candidate = some first ↔ candidate = serverBytes address first := by
  constructor
  · intro found
    simp only [serverCoordinate, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
    obtain ⟨read, _, rest⟩ := found
    split at rest
    · cases rest
      assumption
    · cases rest
  · intro same
    subst same
    simp [serverCoordinate, serverBytes, PqxdhJointGapDh.read_first]

/-- The one-coordinate matcher answers exactly whether the candidate is the address's actual root input. -/
theorem testServer_answer (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (address : ServerAddress) (candidate : Pqxdh.Bytes) :
    simulateQ (answer joint dh seed scalar) (testServer address candidate) =
      pure (decide ((joint.staticDh seed address.staticPeer).map (serverBytes address) = some candidate)) := by
  unfold testServer
  cases parsed : serverCoordinate address candidate with
  | none =>
      simp only [simulateQ_pure]
      congr 1
      symm
      rw [decide_eq_false_iff_not]
      intro found
      obtain ⟨first, _, rfl⟩ := Option.map_eq_some_iff.mp found
      rw [(serverCoordinate_some_iff address _ first).mpr rfl] at parsed
      cases parsed
  | some first =>
      have same := (serverCoordinate_some_iff address candidate first).mp parsed
      rw [answer_decision]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [decide_eq_decide, same]
      constructor
      · intro found
        rw [found]
        rfl
      · intro found
        cases actual : joint.staticDh seed address.staticPeer with
        | none =>
            rw [actual] at found
            cases found
        | some value =>
            rw [actual] at found
            have read := congrArg (readDh 32) (Option.some.inj found)
            simp only [serverBytes, PqxdhJointGapDh.read_first, Option.some.injEq] at read
            rw [read]

/-- A message with a known third coordinate has the input of its Server address. -/
theorem input_known (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (staticPeer : PeerEncoding) (value second fourth kem : DhOutput) :
    PqxdhJointDhExtractFamily.input joint dh seed scalar ⟨staticPeer, .known value, second, fourth, kem⟩ =
      (joint.staticDh seed staticPeer).map (serverBytes ⟨staticPeer, second, value, fourth, kem⟩) := by
  cases actual : joint.staticDh seed staticPeer <;>
    simp [PqxdhJointDhExtractFamily.input, PqxdhJointDhExtractFamily.thirdValue, actual, serverBytes,
      PqxdhJointDhExtractFamily.address]

/-- A message with a selected third coordinate has the input of the two-coordinate address. -/
theorem input_selected (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (staticPeer peer : PeerEncoding) (second fourth kem : DhOutput) :
    PqxdhJointDhExtractFamily.input joint dh seed scalar ⟨staticPeer, .selected peer, second, fourth, kem⟩ =
      PqxdhJointGapDh.sourceInput joint dh seed scalar ⟨staticPeer, peer, second, fourth, kem⟩ :=
  rfl

/-- Concrete bytes are tested against a message exactly for being its actual root input. -/
theorem concreteTest_answer (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (candidate : Pqxdh.Bytes) :
    simulateQ (answer joint dh seed scalar) (concreteTest message candidate) =
      pure (decide (PqxdhJointDhExtractFamily.input joint dh seed scalar message = some candidate)) := by
  rcases message with ⟨staticPeer, third, second, fourth, kem⟩
  cases third with
  | known value =>
      simp only [concreteTest]
      rw [testServer_answer, input_known]
  | selected peer =>
      simp only [concreteTest]
      rw [← service_fst joint dh seed scalar _ [], PqxdhJointGapDh.testInput_full, map_pure,
        PqxdhJointGapDh.testOutcome_value, PqxdhJointGapDh.testInputResult_exact, input_selected]

/-- Under the class law, `thirdSame` answers exactly whether the two third coordinates have the same actual value. -/
theorem thirdSame_answer (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (left right : Third) :
    simulateQ (answer setup.joint setup.dh seed scalar) (thirdSame setup.source.crypto left right) =
      pure (decide (PqxdhJointDhExtractFamily.thirdValue setup.joint setup.dh scalar left =
        PqxdhJointDhExtractFamily.thirdValue setup.joint setup.dh scalar right)) := by
  cases left with
  | known leftValue =>
      cases right with
      | known rightValue => simp [thirdSame, PqxdhJointDhExtractFamily.thirdValue]
      | selected peer =>
          simp only [thirdSame, answer_decision, ↓reduceIte, PqxdhJointDhExtractFamily.thirdValue]
          congr 1
          exact decide_eq_decide.mpr eq_comm
  | selected peer =>
      cases right with
      | known rightValue =>
          simp only [thirdSame, answer_decision, ↓reduceIte, PqxdhJointDhExtractFamily.thirdValue]
          rfl
      | selected rightPeer =>
          simp only [thirdSame, simulateQ_pure, PqxdhJointDhExtractFamily.thirdValue]
          congr 1
          exact decide_eq_decide.mpr (PqxdhServerAuthAssumptions.scalar_iff setup.source.crypto law referenceScalar
            scalar peer rightPeer).symm

/-- Under the class law, `messageSame` answers exactly whether the first message has the second message's actual root input. -/
theorem messageSame_answer (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (left right : Message) (bytes : Pqxdh.Bytes)
    (present : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar right = some bytes) :
    simulateQ (answer setup.joint setup.dh seed scalar) (messageSame setup.source.crypto left right) =
      pure (decide (PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar left = some bytes)) := by
  obtain ⟨first', third', firstRight, thirdRight, assembled⟩ :=
    (PqxdhJointDhExtractFamily.input_some_iff _ _ _ _ right bytes).mp present
  unfold messageSame
  split_ifs with coordinates
  · obtain ⟨second, fourth, kem, dh1⟩ := coordinates
    have staticSame : setup.joint.staticDh seed left.staticPeer = setup.joint.staticDh seed right.staticPeer :=
      (PqxdhServerAuthAssumptions.static_iff setup.source.crypto law setup.joint setup.secretOfSeed setup.wiring
        referenceScalar left.staticPeer right.staticPeer seed).mpr dh1
    rw [thirdSame_answer setup law]
    congr 1
    rw [decide_eq_decide, thirdRight]
    constructor
    · intro thirdLeft
      rw [PqxdhJointDhExtractFamily.input_some_iff]
      refine ⟨first', third', staticSame.trans firstRight, thirdLeft, ?_⟩
      rw [← assembled]
      simp only [PqxdhJointGapDh.assemble, PqxdhJointDhExtractFamily.address, second, fourth, kem]
    · intro inputLeft
      obtain ⟨first, third, _, thirdLeft, assembledLeft⟩ :=
        (PqxdhJointDhExtractFamily.input_some_iff _ _ _ _ left bytes).mp inputLeft
      have same := assemble_inj _ _ _ _ _ _ (assembledLeft.trans assembled.symm)
      rw [thirdLeft, same.2.1]
  · simp only [simulateQ_pure]
    congr 1
    symm
    rw [decide_eq_false_iff_not]
    intro inputLeft
    obtain ⟨first, third, firstLeft, _, assembledLeft⟩ :=
      (PqxdhJointDhExtractFamily.input_some_iff _ _ _ _ left bytes).mp inputLeft
    obtain ⟨sameFirst, _, sameSecond, sameFourth, sameKem⟩ :=
      assemble_inj _ _ _ _ _ _ (assembledLeft.trans assembled.symm)
    apply coordinates
    refine ⟨sameSecond, sameFourth, sameKem, ?_⟩
    exact (PqxdhServerAuthAssumptions.static_iff setup.source.crypto law setup.joint setup.secretOfSeed setup.wiring
      referenceScalar left.staticPeer right.staticPeer seed).mp (by rw [firstLeft, firstRight, sameFirst])

/-- Under the class law, `symSame` answers exactly whether a table key has the queried key's actual bytes. -/
theorem symSame_answer (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query entry : SymKey) (bytes : Pqxdh.Bytes) (present : keyInput setup seed scalar query = some bytes) :
    simulateQ (answer setup.joint setup.dh seed scalar) (symSame setup.source.crypto query entry) =
      pure (decide (keyInput setup seed scalar entry = some bytes)) := by
  cases query with
  | concrete query =>
      simp only [keyInput, Option.some.injEq] at present
      subst present
      cases entry with
      | concrete entry => simp [symSame, keyInput]
      | message entry =>
          simp only [symSame, keyInput]
          exact concreteTest_answer _ _ _ _ _ _
  | message query =>
      simp only [keyInput] at present
      cases entry with
      | concrete entry =>
          simp only [symSame, keyInput]
          rw [concreteTest_answer, present]
          congr 1
          exact decide_eq_decide.mpr eq_comm
      | message entry =>
          simp only [symSame, keyInput]
          exact messageSame_answer setup law seed scalar entry query bytes present

/-- Under the class law, the symbolic lookup returns the block of the concretized cache at the queried key's bytes. -/
theorem symLookup_answer (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : SymKey) (bytes : Pqxdh.Bytes) (present : keyInput setup seed scalar query = some bytes)
    (table : List (SymKey × HmacBlock)) :
    simulateQ (answer setup.joint setup.dh seed scalar) (symLookup setup.source.crypto query table) =
      pure (symCache setup seed scalar table bytes) := by
  induction table with
  | nil => simp [symLookup, symCache]
  | cons entry rest ih =>
      simp only [symLookup, simulateQ_bind, symSame_answer setup law seed scalar query entry.1 bytes present,
        pure_bind]
      by_cases hit : keyInput setup seed scalar entry.1 = some bytes
      · simp [hit, symCache]
      · simp only [hit, decide_false, Bool.false_eq_true, ↓reduceIte, ih]
        simp [symCache, hit]

/-- Appending a new entry under a key whose bytes the table misses records its block at those bytes. -/
theorem symCache_append (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (table : List (SymKey × HmacBlock)) (query : SymKey) (block : HmacBlock) (bytes : Pqxdh.Bytes)
    (present : keyInput setup seed scalar query = some bytes)
    (miss : symCache setup seed scalar table bytes = none) :
    symCache setup seed scalar (table ++ [(query, block)]) =
      (symCache setup seed scalar table).cacheQuery bytes block := by
  funext other
  have missFind : table.find? (fun entry => decide (keyInput setup seed scalar entry.1 = some bytes)) = none := by
    simpa [symCache] using miss
  by_cases same : other = bytes
  · subst same
    rw [QueryCache.cacheQuery_self]
    simp [symCache, List.find?_append, missFind, present]
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    have skip : keyInput setup seed scalar query ≠ some other := by
      rw [present]
      exact fun found => same (Option.some.inj found).symm
    simp [symCache, List.find?_append, skip]

/-- Under the class law, a symbolic table read is the lazy random-oracle read of the concretized cache, returned with the new table. -/
theorem symRead_answer (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : SymKey) (bytes : Pqxdh.Bytes) (present : keyInput setup seed scalar query = some bytes)
    (table : List (SymKey × HmacBlock)) :
    simulateQ (answer setup.joint setup.dh seed scalar) (symRead setup.source.crypto query table) =
      match symCache setup seed scalar table bytes with
      | some block => pure (block, table)
      | none => ($ᵗ HmacBlock) >>= fun block => pure (block, table ++ [(query, block)]) := by
  simp only [symRead, simulateQ_bind, symLookup_answer setup law seed scalar query bytes present, pure_bind]
  cases symCache setup seed scalar table bytes with
  | some block => simp
  | none => simp [answer_coins]

/-- The public rejection test agrees with the existence of the actual root input. -/
theorem symAccepts_iff (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) :
    symAccepts setup message = (PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message).isSome := by
  have server := setup.serverDomain.available seed message.staticPeer
  rcases message with ⟨staticPeer, third, second, fourth, kem⟩
  cases third with
  | known value =>
      simp only [symAccepts, Bool.and_true]
      rw [input_known, Option.isSome_map]
      exact server.symm
  | selected peer =>
      have beacon : (setup.dh.dh scalar peer).isSome = setup.beaconDomain.accepts peer :=
        setup.beaconDomain.available scalar peer
      simp only [symAccepts]
      rw [← server, ← beacon]
      simp only [PqxdhJointDhExtractFamily.input, PqxdhJointDhExtractFamily.thirdValue]
      cases setup.joint.staticDh seed staticPeer <;> cases setup.dh.dh scalar peer <;> rfl

/-- A symbolic table read, concretized, is the lazy random-oracle read of the concretized cache. -/
theorem symRead_concretize (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : SymKey) (bytes : Pqxdh.Bytes) (present : keyInput setup seed scalar query = some bytes)
    (table : List (SymKey × HmacBlock)) :
    (fun read : HmacBlock × List (SymKey × HmacBlock) => (read.1, symCache setup seed scalar read.2)) <$>
        simulateQ (answer setup.joint setup.dh seed scalar) (symRead setup.source.crypto query table) =
      (HmacOracle.randomOracle bytes).run (symCache setup seed scalar table) := by
  rw [symRead_answer setup law seed scalar query bytes present, randomOracle.run_eq]
  cases hit : symCache setup seed scalar table bytes with
  | some block => simp
  | none =>
      simp only [map_bind, map_pure]
      refine bind_congr fun block => ?_
      rw [symCache_append setup seed scalar table query block bytes present hit]

/-- Per-query simulation (step A2): under the class law, every query of the symbolic family, answered by the Gap-DH services and concretized, is the same query of the Extract random-oracle family at the concretized state. The equation holds at every symbolic state. -/
theorem sym_step (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : PqxdhJointDhExtractFamily.Spec.Domain) (state : SymState) :
    Prod.map id (concretize setup seed scalar) <$>
        simulateQ (answer setup.joint setup.dh seed scalar) ((symImpl setup query).run state) =
      (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar query).run
        (concretize setup seed scalar state) := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · change Prod.map id _ <$> simulateQ _ (do
        let value ← (liftM (PqxdhJointGapDh.AdversarySpec.query (.inl coin)) : OracleComp _ _)
        pure (value, state)) = _
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure]
    rfl
  · change Prod.map id _ <$> simulateQ _ (do
        let signature ← (liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.sign message))) : OracleComp _ _)
        pure (signature, { state with history := state.history ++
          [PqxdhJointDhExtractFamily.Observation.sign message signature] })) = _
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure]
    rfl
  · by_cases inside : key = zeroSalt ∧ message.length = 192
    · rw [PqxdhExtractRomFamily.rom_public_oracle _ _ _ _ _ key message inside]
      change Prod.map id _ <$> simulateQ _ (if key = zeroSalt ∧ message.length = 192 then _ else _) = _
      rw [ite_eq_left_of_eq_true _ _ (eq_true inside)]
      simp only [simulateQ_bind, simulateQ_pure]
      rw [show (concretize setup seed scalar state).cache = symCache setup seed scalar state.table from rfl,
        ← symRead_concretize setup law seed scalar (.concrete message) message rfl state.table]
      simp only [Functor.map_map, bind_pure_comp]
      rfl
    · rw [PqxdhExtractRomFamily.rom_public_real _ _ _ _ _ (PqxdhJointDhExtractFamily.actualExtract setup.hmac) key
        message inside, PqxdhJointDhExtractFamily.public_evaluation]
      change Prod.map id _ <$> simulateQ _ (if key = zeroSalt ∧ message.length = 192 then _ else _) = _
      rw [ite_eq_right_of_eq_false _ _ (eq_false inside)]
      simp only [simulateQ_pure, map_pure]
      rfl
  · cases present : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
    | none =>
        have rejected : symAccepts setup message = false := by
          rw [symAccepts_iff setup seed scalar, present]
          rfl
        rw [PqxdhExtractRomFamily.rom_rejected _ _ _ _ _ message _ present]
        change Prod.map id _ <$> simulateQ _ (if symAccepts setup message = true then _ else _) = _
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [rejected]; decide))]
        simp only [simulateQ_pure, map_pure]
        rfl
    | some bytes =>
        have accepted : symAccepts setup message = true := by
          rw [symAccepts_iff setup seed scalar, present]
          rfl
        rw [PqxdhExtractRomFamily.rom_derive_oracle _ _ _ _ _ message bytes present]
        change Prod.map id _ <$> simulateQ _ (if symAccepts setup message = true then _ else _) = _
        rw [ite_eq_left_of_eq_true _ _ (eq_true accepted)]
        simp only [simulateQ_bind, simulateQ_pure]
        rw [show (concretize setup seed scalar state).cache = symCache setup seed scalar state.table from rfl,
          ← symRead_concretize setup law seed scalar (.message message) bytes present state.table]
        simp only [Functor.map_map, bind_pure_comp]
        rfl

/-- Exact simulation (step A2): under the class law, running any root-valued program under the symbolic family and answering its Gap-DH requests with the two secrets gives, after concretization, exactly the run under the Extract random-oracle family, with the same output and the same family history. -/
theorem sym_complete (setup : Setup baseSpec KemSK)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (oa : OracleComp RootSpec α) (state : SymState) :
    Prod.map id (concretize setup seed scalar) <$> simulateQ (answer setup.joint setup.dh seed scalar)
        ((simulateQ (symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) oa).run state) =
      (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction) oa).run (concretize setup seed scalar state) := by
  rw [QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose, QueryImpl.simulateQ_mapStateTBase_run]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (concretize setup seed scalar)
    (fun query state => sym_step setup law seed scalar query state) _ state

/-- The empty symbolic state denotes the empty family state. -/
theorem concretize_empty (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) :
    concretize setup seed scalar SymState.empty = PqxdhJointDhExtractFamily.empty :=
  rfl

/-- Under the class law and the stateless Gap-DH answers, the scanning client outputs exactly the padded candidates of the family history of the real experiment body. -/
theorem scanClient_answer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat) (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    simulateQ (answer setup.joint setup.dh seed scalar)
        (scanClient setup codec checks adversary qH (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) =
      (fun result : PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State =>
          PqxdhServerAuthExperiment.padded qH (PqxdhServerAuthExperiment.romCandidates result.2.history)) <$>
        (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
          PqxdhJointDhExtractRoot.reduction)
          (PqxdhServerAuthExperiment.body setup codec checks adversary none
            (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run PqxdhJointDhExtractFamily.empty := by
  unfold scanClient
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  rw [bind_pure_comp, ← concretize_empty setup seed scalar, ← sym_complete setup law seed scalar, Functor.map_map]
  congr 1

/-- The Gap-DH candidate game of the scanning client is the experiment with the scan event read from its final family history. -/
theorem candidate_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat) (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) :
    PqxdhJointGapDh.candidateGame setup.joint setup.dh (scanClient setup codec checks adversary qH) =
      (fun result : IdentitySeed × ScalarBytes × PqxdhServerAuthExperiment.GameState KemSK ×
          PqxdhJointDhExtractFamily.State =>
        decide (∃ value, setup.joint.staticDh result.1 (setup.dh.publicKey result.2.1) = some value ∧
          value ≠ zeroDh ∧ value ∈ (PqxdhServerAuthExperiment.padded qH
            (PqxdhServerAuthExperiment.romCandidates result.2.2.2.history)).toList)) <$>
        PqxdhServerAuthExperiment.gameState setup codec checks false adversary := by
  unfold PqxdhJointGapDh.candidateGame PqxdhServerAuthExperiment.gameState
  simp only [map_bind, map_pure]
  refine bind_congr fun seed => bind_congr fun scalar => ?_
  have client := scanClient_answer setup codec checks adversary qH law seed scalar
  rw [← service_fst _ _ _ _ _ []] at client
  have split : (PqxdhJointGapDh.run setup.joint setup.dh seed scalar
      (scanClient setup codec checks adversary qH) >>= fun output =>
        pure (decide (∃ value, setup.joint.staticDh seed (setup.dh.publicKey scalar) = some value ∧
          value ≠ zeroDh ∧ value ∈ output.1.toList))) =
      (fun candidates : List.Vector DhOutput qH =>
        decide (∃ value, setup.joint.staticDh seed (setup.dh.publicKey scalar) = some value ∧
          value ≠ zeroDh ∧ value ∈ candidates.toList)) <$>
        (Prod.fst <$> PqxdhJointGapDh.run setup.joint setup.dh seed scalar
          (scanClient setup codec checks adversary qH)) := by
    simp only [Functor.map_map, bind_pure_comp]
  refine split.trans ?_
  rw [PqxdhJointGapDh.run, client, Functor.map_map, map_eq_bind_pure_comp]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

set_option linter.deprecated false in
/-- Step A2 and A3 of the hybrid chain: under the class law, the probability of the scan event in the experiment is the Gap-DH term of the scanning reduction. -/
theorem candHit_eq_gapDh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat) (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto) :
    Pr[fun result => PqxdhServerAuthExperiment.CandHit setup result.1 result.2.1 qH result.2.2.2.history |
        PqxdhServerAuthExperiment.gameState setup codec checks false adversary] =
      PqxdhServerAuthAssumptions.serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed
        setup.wiring (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH)) := by
  rw [← PqxdhServerAuthAssumptions.candidate_eq_serverGapDh]
  change _ = Pr[= true | PqxdhJointGapDh.candidateGame setup.joint setup.dh
    (scanClient setup codec checks adversary qH)]
  rw [candidate_game setup codec checks adversary qH law, probOutput_map]
  refine probEvent_ext fun result _ => ?_
  simp only [decide_eq_true_eq, PqxdhServerAuthExperiment.CandHit]

/-! ## Which family requests honest code makes -/

/-- Public requests of the root-valued family interface: signing and public HMAC. -/
def IsPublicRoot : RootSpec.Domain → Prop
  | .inr (.sign _) => True
  | .inr (.publicHmac _ _) => True
  | _ => False

/-- Public requests are decidable. -/
instance : DecidablePred IsPublicRoot := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr (.sign _) => isTrue trivial
  | .inr (.publicHmac _ _) => isTrue trivial
  | .inr (.derive _) => isFalse id

/-- Signing requests of the root-valued family interface. -/
def IsSignRoot : RootSpec.Domain → Prop
  | .inr (.sign _) => True
  | _ => False

/-- Signing requests are decidable. -/
instance : DecidablePred IsSignRoot := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr (.sign _) => isTrue trivial
  | .inr (.publicHmac _ _) => isFalse id
  | .inr (.derive _) => isFalse id

/-- Table requests of the root-valued family interface: public HMAC under the zero key on 192 bytes. -/
def IsTableRoot : RootSpec.Domain → Prop
  | .inr (.publicHmac key message) => key = zeroSalt ∧ message.length = 192
  | _ => False

/-- Table requests are decidable. -/
instance : DecidablePred IsTableRoot := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr (.sign _) => isFalse id
  | .inr (.publicHmac key message) => inferInstanceAs (Decidable (key = zeroSalt ∧ message.length = 192))
  | .inr (.derive _) => isFalse id

/-- A signing request is public. -/
theorem sign_public (query : RootSpec.Domain) (sign : IsSignRoot query) : IsPublicRoot query := by
  rcases query with coin | (message | ⟨key, message⟩ | message) <;> simp_all [IsSignRoot, IsPublicRoot]

/-- A table request is public. -/
theorem table_public (query : RootSpec.Domain) (table : IsTableRoot query) : IsPublicRoot query := by
  rcases query with coin | (message | ⟨key, message⟩ | message) <;> simp_all [IsTableRoot, IsPublicRoot]

/-- A game computation that makes no public family request, from any state. -/
def Quiet {α : Type} (work : PqxdhServerAuthExperiment.Game KemSK α) : Prop :=
  ∀ state, (work.run state).IsQueryBoundP IsPublicRoot 0

/-- A returned value is quiet. -/
theorem quiet_pure {α : Type} (value : α) : Quiet (pure value : PqxdhServerAuthExperiment.Game KemSK α) :=
  fun state => by simp

/-- Quiet computations compose. -/
theorem quiet_bind {α β : Type} {first : PqxdhServerAuthExperiment.Game KemSK α}
    {next : α → PqxdhServerAuthExperiment.Game KemSK β} (quietFirst : Quiet first) (quietNext : ∀ value, Quiet (next value)) :
    Quiet (first >>= next) := fun state => by
  rw [StateT.run_bind]
  simpa using isQueryBoundP_bind (quietFirst state) (fun pair _ => quietNext pair.1 pair.2)

/-- Reading the state is quiet. -/
theorem quiet_get : Quiet (get : PqxdhServerAuthExperiment.Game KemSK (PqxdhServerAuthExperiment.GameState KemSK)) :=
  fun state => by simp

/-- Writing the state is quiet. -/
theorem quiet_set (value : PqxdhServerAuthExperiment.GameState KemSK) :
    Quiet (set value : PqxdhServerAuthExperiment.Game KemSK PUnit) :=
  fun state => by simp

/-- Modifying the state is quiet. -/
theorem quiet_modify (change : PqxdhServerAuthExperiment.GameState KemSK → PqxdhServerAuthExperiment.GameState KemSK) :
    Quiet (modify change : PqxdhServerAuthExperiment.Game KemSK PUnit) :=
  fun state => by simp

/-- Family coins make no public request. -/
theorem familyCoins_quiet {α : Type} (work : ProbComp α) :
    (PqxdhServerAuthExperiment.familyCoins work).IsQueryBoundP IsPublicRoot 0 :=
  IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false work 0) (fun _ absurd => absurd.elim)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).mpr (fun found => absurd found id))

/-- Lifted coins are quiet. -/
theorem quiet_liftCoins {α : Type} (work : ProbComp α) :
    Quiet (PqxdhServerAuthExperiment.liftCoins (KemSK := KemSK) work) := fun state => by
  simp only [PqxdhServerAuthExperiment.liftCoins, StateT.run_lift]
  simpa using familyCoins_quiet work

/-- A forwarded request is quiet unless it is public. -/
theorem quiet_forward (query : RootSpec.Domain) (quiet : ¬ IsPublicRoot query) :
    Quiet (PqxdhServerAuthExperiment.forwardFamily (KemSK := KemSK) query) := fun state => by
  simp only [PqxdhServerAuthExperiment.forwardFamily, StateT.run_lift]
  exact (isQueryBoundP_bind ((isQueryBoundP_query_iff IsPublicRoot query 0).mpr (fun found => absurd found quiet))
    (fun _ _ => isQueryBoundP_pure IsPublicRoot _ 0)).mono (by omega)

/-- A forwarded request makes at most one public request, and none when it is not public. -/
theorem forward_bound (query : RootSpec.Domain) (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.forwardFamily (KemSK := KemSK) query).run state).IsQueryBoundP IsPublicRoot
      (if IsPublicRoot query then 1 else 0) := by
  simp only [PqxdhServerAuthExperiment.forwardFamily, StateT.run_lift]
  exact (isQueryBoundP_bind ((isQueryBoundP_query_iff IsPublicRoot query
    (if IsPublicRoot query then 1 else 0)).mpr (fun found => by simp [found]))
    (fun _ _ => isQueryBoundP_pure IsPublicRoot _ 0)).mono (by simp)

/-- Recording a touch is quiet. -/
theorem quiet_record (touch : PqxdhServerAuthExperiment.Touch) :
    Quiet (PqxdhServerAuthExperiment.recordTouch (KemSK := KemSK) touch) :=
  fun state => by simp [PqxdhServerAuthExperiment.record_run]

/-- Public requests of the Server's root-consumer interface. -/
def IsPublicClient : PqxdhServerRelatedRootConsumer.Spec.Domain → Prop
  | .inl query => IsPublicRoot query
  | .inr _ => False

/-- Public root-consumer requests are decidable. -/
instance : DecidablePred IsPublicClient := fun query =>
  match query with
  | .inl query => inferInstanceAs (Decidable (IsPublicRoot query))
  | .inr _ => isFalse id

/-- The Server's root consumer makes no public family request: its only family request is the root derivation. -/
theorem client_quiet (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) :
    (PqxdhServerRelatedRootConsumer.client binding input).IsQueryBoundP IsPublicClient 0 := by
  classical
  unfold PqxdhServerRelatedRootConsumer.client
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl id, fun _ => ?_⟩
  split
  · trivial
  · rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl id, fun root => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl id, fun _ => ?_⟩
    split
    · trivial
    · rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun _ => trivial⟩

/-- A step of a Server session's callbacks makes a public family request only when it forwards one. -/
theorem session_step (index : Nat) (query : PqxdhServerRelatedRootConsumer.Spec.Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.sessionImpl index query).run state).IsQueryBoundP IsPublicRoot
      (if IsPublicClient query then 1 else 0) := by
  rcases query with (coin | (message | ⟨key, message⟩ | message)) | aux
  · exact forward_bound _ state
  · exact forward_bound _ state
  · exact forward_bound _ state
  · exact quiet_bind (quiet_forward _ id) (fun reply => quiet_bind (quiet_record _) fun _ => quiet_pure _) state
  · cases aux
    · exact quiet_pure _ state
    · exact quiet_pure _ state
    · exact quiet_modify _ state

/-- A Server session's root consumer, run on the game, is quiet. -/
theorem quiet_session (index : Nat) (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) :
    Quiet (simulateQ (PqxdhServerAuthExperiment.sessionImpl (KemSK := KemSK) index)
      (PqxdhServerRelatedRootConsumer.client binding input)) := fun state =>
  IsQueryBoundP.simulateQ_run_StateT_of_step (client_quiet binding input)
    (fun query state => session_step index query state) state

/-- A Server accept is quiet. -/
theorem quiet_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) :
    Quiet (PqxdhServerAuthExperiment.acceptOracle setup codec checks publicValue raw) := by
  unfold PqxdhServerAuthExperiment.acceptOracle
  refine quiet_bind quiet_get fun state => ?_
  refine quiet_bind (quiet_liftCoins _) fun collected => ?_
  refine quiet_bind (quiet_set _) fun _ => ?_
  split
  · exact quiet_pure _
  · refine quiet_bind (quiet_session _ _ _) fun returned => ?_
    split
    · exact quiet_bind (quiet_modify _) fun _ => quiet_pure _
    · exact quiet_pure _

/-- A Server build is quiet. -/
theorem quiet_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) :
    Quiet (PqxdhServerAuthExperiment.buildOracle setup codec checks session payload) := by
  unfold PqxdhServerAuthExperiment.buildOracle
  refine quiet_bind quiet_get fun state => ?_
  split
  · exact quiet_pure _
  · exact quiet_bind (quiet_liftCoins _) fun result => quiet_bind (quiet_set _) fun _ => quiet_pure _

/-- Public requests of the Beacon's related-root tail interface. -/
def IsPublicTail : (PqxdhPhase2DhRootConsumer.Spec Response).Domain → Prop
  | .inl query => IsPublicRoot query
  | .inr _ => False

/-- Public tail requests are decidable. -/
instance : DecidablePred (IsPublicTail (Response := Response)) := fun query =>
  match query with
  | .inl query => inferInstanceAs (Decidable (IsPublicRoot query))
  | .inr _ => isFalse id

/-- Public requests of the Beacon's Phase 2 stage interface. -/
def IsPublicStage : (PqxdhPhase2DhStage.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain → Prop
  | .inl _ => False
  | .inr query => IsPublicTail query

/-- Public stage requests are decidable. -/
instance : DecidablePred (IsPublicStage (KemSK := KemSK) (Response := Response)) := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable (IsPublicTail query))

/-- The Beacon's related-root tail makes no public family request: its only family request is the root derivation. -/
theorem tail_quiet (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (PqxdhPhase2DhRootConsumer.tail publicValue decode pending).IsQueryBoundP IsPublicTail 0 := by
  unfold PqxdhPhase2DhRootConsumer.tail
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun value _ => ?_
  · refine IsQueryBoundP.simulateQ_of_step (p := IsPublicRoot) (n := 0) ?_ ?_ ?_
    · unfold PqxdhPhase2DhRootConsumer.root
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun found => found.elim
    · intro query _
      exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
    · intro query quiet
      exact (isQueryBoundP_query_iff _ _ _).mpr fun found => absurd found quiet
  · split
    · trivial
    · refine IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false _ 0)
        (fun _ absurd => absurd.elim) ?_
      intro query _
      exact (isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim

/-- The Beacon's Phase 2 stage makes no public family request. -/
theorem stage_quiet (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (raw : Pqxdh.Bytes) :
    (PqxdhPhase2DhStage.stage (X := Unit) (Response := Response) publicValue decode control identity oneTime kem
      raw).IsQueryBoundP IsPublicStage 0 := by
  unfold PqxdhPhase2DhStage.stage
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun pending _ => ?_
  · refine IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false _ 0)
      (fun _ absurd => absurd.elim) ?_
    intro query _
    exact (isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim
  · split
    · trivial
    · refine IsQueryBoundP.simulateQ_of_step (p := IsPublicTail) (tail_quiet _ _ _) ?_ ?_
      · intro query _
        exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
      · intro query quiet
        exact (isQueryBoundP_query_iff _ _ _).mpr fun found => absurd found quiet

/-- Work on the shared BLAKE2b cache is quiet. -/
theorem quiet_onCtx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    Quiet (PqxdhServerAuthExperiment.onCtx (KemSK := KemSK) work) := fun state => by
  change (PqxdhServerAuthExperiment.familyCoins (work.run ((), state.ctx)) >>= fun result =>
    pure (result.1, { state with ctx := result.2.2 })).IsQueryBoundP IsPublicRoot 0
  simpa using familyCoins_quiet (work.run ((), state.ctx))

/-- A step of the Beacon's stage callbacks makes a public family request only when it forwards one. -/
theorem stage_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (query : (PqxdhPhase2DhStage.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.stageImpl setup codec beaconSeed query).run state).IsQueryBoundP IsPublicRoot
      (if IsPublicStage query then 1 else 0) := by
  rcases query with query | (coin | (message | ⟨key, message⟩ | message)) | query
  · exact quiet_liftCoins _ state
  · exact forward_bound _ state
  · exact forward_bound _ state
  · exact forward_bound _ state
  · exact quiet_bind (quiet_record _) (fun _ => quiet_forward _ id) state
  · exact quiet_onCtx _ state

/-- The Beacon's stage, run on the game, is quiet. -/
theorem quiet_stage (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    Quiet (simulateQ (PqxdhServerAuthExperiment.stageImpl setup codec beaconSeed)
      (PqxdhPhase2DhStage.stage publicValue codec.frameRead control identity oneTime kem raw)) := fun state =>
  IsQueryBoundP.simulateQ_run_StateT_of_step (stage_quiet publicValue codec.frameRead control identity oneTime kem raw)
    (fun query state => stage_step setup codec beaconSeed query state) state

/-- The target Beacon's finish is quiet. -/
theorem quiet_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (publicValue : PublicChallenge)
    (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) :
    Quiet (PqxdhServerAuthExperiment.finishOracle setup codec publicValue beaconSeed raw) := by
  unfold PqxdhServerAuthExperiment.finishOracle
  refine quiet_bind quiet_get fun state => ?_
  split
  · exact quiet_bind (quiet_stage _ _ _ _ _ _ _ _ _) fun staged => quiet_bind quiet_get fun current =>
      quiet_bind (quiet_set _) fun _ => quiet_pure _
  · exact quiet_pure _

/-- A BLAKE2b query is quiet. -/
theorem quiet_hash (bytes : Pqxdh.Bytes) : Quiet (PqxdhServerAuthExperiment.hashOracle (KemSK := KemSK) bytes) :=
  fun state => by
    change (PqxdhServerAuthExperiment.familyCoins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx) >>=
      fun result => pure (result.1, { state with ctx := result.2 })).IsQueryBoundP IsPublicRoot 0
    simpa using familyCoins_quiet ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx)

/-- Honest code makes no public family request (`honest_no_rom_public`): every handler step other than the adversary's public HMAC query issues neither a signing request nor a public HMAC request, in particular no table request. -/
theorem honest_no_rom_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : PqxdhServerAuthExperiment.ServerAuthSpec.Domain)
    (notHmac : ∀ key message, query ≠ .inr (.hmac key message)) :
    Quiet (PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed query) := by
  rcases query with coin | query
  · exact quiet_forward _ id
  cases query with
  | accept raw => exact quiet_accept setup codec checks publicValue raw
  | build session payload => exact quiet_build setup codec checks session payload
  | finish raw => exact quiet_finish setup codec publicValue beaconSeed raw
  | hmac key message => exact absurd rfl (notHmac key message)
  | hash bytes => exact quiet_hash bytes
  | reveal keyId =>
      intro state
      change (pure _ : OracleComp RootSpec _).IsQueryBoundP IsPublicRoot 0
      trivial

/-! ## Adversary touches and table queries in the family history -/

/-- The adversary's table queries logged in a touch list, in order. -/
def adversaryTouches (touches : List PqxdhServerAuthExperiment.Touch) : List Pqxdh.Bytes :=
  touches.filterMap fun
    | .adversary bytes => some bytes
    | _ => none

/-- The table-domain messages of the public HMAC entries of a family history, in order. -/
def romMessages (history : PqxdhJointDhExtractFamily.History) : List Pqxdh.Bytes :=
  history.filterMap fun
    | .publicHmac key message _ => if key = zeroSalt ∧ message.length = 192 then some message else none
    | _ => none

/-- The table-domain message of a root-valued request, if it is a table request. -/
def tableMessage : RootSpec.Domain → List Pqxdh.Bytes
  | .inr (.publicHmac key message) => if key = zeroSalt ∧ message.length = 192 then [message] else []
  | _ => []

/-- The table-domain message of an adversary query, if it is a table query. -/
def romMessage : PqxdhServerAuthExperiment.ServerAuthSpec.Domain → List Pqxdh.Bytes
  | .inr (.hmac key message) => if key = zeroSalt ∧ message.length = 192 then [message] else []
  | _ => []

/-- A query that is not a public HMAC query has no table-domain message. -/
theorem romMessage_quiet (query : PqxdhServerAuthExperiment.ServerAuthSpec.Domain)
    (notHmac : ∀ key message, query ≠ .inr (.hmac key message)) : romMessage query = [] := by
  rcases query with coin | query
  · rfl
  · cases query with
    | hmac key message => exact absurd rfl (notHmac key message)
    | _ => rfl

/-- A request that is not a table request has no table-domain message. -/
theorem tableMessage_quiet (query : RootSpec.Domain) (quiet : ¬ IsTableRoot query) : tableMessage query = [] := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · rfl
  · rfl
  · exact ite_eq_right_of_eq_false _ _ (eq_false quiet)
  · rfl

/-- Each request of the Extract random-oracle family appends to the table-domain messages of the history exactly the table-domain message of the request: honest root derivations add none, because the root Expand input has 47 bytes. -/
theorem rom_step (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (query : RootSpec.Domain) (state : PqxdhJointDhExtractFamily.State)
    (result : RootSpec.Range query × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ
      PqxdhJointDhExtractRoot.reduction) query).run state)) :
    romMessages result.2.history = romMessages state.history ++ tableMessage query := by
  obtain ⟨forwardCoin, forwardSign, forwardPublic⟩ := PqxdhExtractRomFamily.rom_forward hmac joint dh seed scalar
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · rw [forwardCoin] at supported
    change result ∈ support (do
      let value ← (unifSpec.query coin : ProbComp _)
      pure (value, state)) at supported
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    simp [tableMessage]
  · rw [forwardSign] at supported
    change result ∈ support (pure _ : ProbComp _) at supported
    rw [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp [romMessages, tableMessage]
  · rw [forwardPublic] at supported
    by_cases inside : key = zeroSalt ∧ message.length = 192
    · rw [PqxdhExtractRomFamily.rom_public_oracle hmac joint dh seed scalar key message inside, support_map]
        at supported
      obtain ⟨step, _, rfl⟩ := supported
      simp [romMessages, tableMessage, inside]
    · rw [PqxdhExtractRomFamily.rom_public_real hmac joint dh seed scalar
        (PqxdhJointDhExtractFamily.actualExtract hmac) key message inside,
        PqxdhJointDhExtractFamily.public_evaluation, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      simp [romMessages, tableMessage, inside]
  · rw [PqxdhExtractRomFamily.rom_root] at supported
    split at supported
    · rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      simp [romMessages, tableMessage]
    · rw [support_map] at supported
      obtain ⟨step, _, rfl⟩ := supported
      have outside := PqxdhExtractRomFamily.rootExpand_outside step.1
      simp [romMessages, tableMessage, outside]

/-- A root-valued program without table requests leaves the table-domain messages of the family history unchanged under the Extract random-oracle family. -/
theorem rom_quiet (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) {α : Type} (oa : OracleComp RootSpec α) (bounded : oa.IsQueryBoundP IsTableRoot 0)
    (state : PqxdhJointDhExtractFamily.State) (result : α × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support ((simulateQ (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ
      PqxdhJointDhExtractRoot.reduction) oa).run state)) :
    romMessages result.2.history = romMessages state.history := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have quiet : ¬ IsTableRoot query := fun table => by simpa using bounded.1.resolve_left (not_not.mpr table)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      obtain ⟨middle, first, rest⟩ := (mem_support_bind_iff _ _ _).1 supported
      have nextBound : (next middle.1).IsQueryBoundP IsTableRoot 0 := by
        simpa [quiet] using bounded.2 middle.1
      rw [ih middle.1 nextBound middle.2 rest, rom_step hmac joint dh seed scalar query state middle first,
        tableMessage_quiet query quiet, List.append_nil]

/-- A Server accept logs no adversary touch. -/
theorem accept_touches (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (result : Option Nat × PqxdhServerAuthExperiment.GameState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthExperiment.acceptOracle setup codec checks publicValue raw).run
      state)) :
    adversaryTouches result.2.ghost.touches = adversaryTouches state.ghost.touches := by
  simp only [PqxdhServerAuthExperiment.acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨_, same⟩ := PqxdhServerAuthExperiment.liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, shape, _⟩ := PqxdhServerAuthExperiment.client_run state.sessions
        (PqxdhServerAuthExperiment.binding setup publicValue) input _ returned derived
      have touches : adversaryTouches returned.2.ghost.touches = adversaryTouches state.ghost.touches := by
        rw [eq]
        rcases shape with ⟨_, rfl⟩ | ⟨_, reply, rfl⟩ <;> simp [adversaryTouches]
      rcases returned with ⟨outcome, after⟩
      dsimp only at touches
      rcases outcome with (_ | token) | error | _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact touches
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        exact touches
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact touches
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact touches

/-- A Server build logs no touch. -/
theorem build_touches (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthExperiment.GameState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthExperiment.buildOracle setup codec checks session payload).run
      state)) :
    result.2.ghost.touches = state.ghost.touches := by
  simp only [PqxdhServerAuthExperiment.buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨_, same⟩ := PqxdhServerAuthExperiment.liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      rfl

/-- The Beacon's finish logs no adversary touch. -/
theorem finish_touches (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (publicValue : PublicChallenge)
    (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (result : Option Pqxdh.Bytes × PqxdhServerAuthExperiment.GameState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthExperiment.finishOracle setup codec publicValue beaconSeed
      raw).run state)) :
    adversaryTouches result.2.ghost.touches = adversaryTouches state.ghost.touches := by
  simp only [PqxdhServerAuthExperiment.finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [hphase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, stageRun, supported⟩ := supported
      obtain ⟨cache, extra, stagedEq, shape⟩ := PqxdhServerAuthExperiment.stage_run setup codec beaconSeed
        publicValue control state.beacon.beacon.identity oneTime kem raw state staged stageRun
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
      rw [PqxdhServerAuthExperiment.Ghost.accept_touches, stagedEq]
      rcases shape with ⟨rfl, _, _⟩ | ⟨pending, _, rfl⟩ <;> simp [adversaryTouches]
  | _ =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- Each handler step appends to the adversary touches exactly the table-domain message of the query: a public HMAC query in the table domain adds its message, and every other step adds none. -/
theorem adversary_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : PqxdhServerAuthExperiment.ServerAuthSpec.Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK)
    (result : PqxdhServerAuthExperiment.ServerAuthSpec.Range query × PqxdhServerAuthExperiment.GameState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed
      query).run state)) :
    adversaryTouches result.2.ghost.touches = adversaryTouches state.ghost.touches ++ romMessage query := by
  rcases query with coin | query
  · rw [PqxdhServerAuthExperiment.forward_support _ _ _ supported]
    simp [romMessage]
  cases query with
  | accept raw =>
      rw [accept_touches setup codec checks publicValue raw state result supported]
      simp [romMessage]
  | build session payload =>
      rw [build_touches setup codec checks session payload state result supported]
      simp [romMessage]
  | finish raw =>
      rw [finish_touches setup codec publicValue beaconSeed raw state result supported]
      simp [romMessage]
  | hmac key message =>
      change result ∈ support ((PqxdhServerAuthExperiment.hmacOracle key message).run state) at supported
      simp only [PqxdhServerAuthExperiment.hmacOracle] at supported
      split_ifs at supported with inside
      · obtain ⟨middle, first, rest⟩ := PqxdhServerAuthExperiment.run_bind_support _ _ _ _ supported
        rw [PqxdhServerAuthExperiment.record_run, support_pure, Set.mem_singleton_iff] at first
        subst first
        rw [PqxdhServerAuthExperiment.forward_support _ _ _ rest]
        simp [adversaryTouches, romMessage, inside]
      · rw [PqxdhServerAuthExperiment.forward_support _ _ _ supported]
        simp [romMessage, inside]
  | hash bytes =>
      obtain ⟨cache, eq⟩ := PqxdhServerAuthExperiment.hashOracle_step bytes state result supported
      rw [eq]
      simp [romMessage]
  | reveal keyId =>
      change result ∈ support (pure _ : OracleComp RootSpec _) at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      simp [romMessage]

/-- The combined handler of the experiment: the handler runs on the game state, and its family requests are answered by the Extract random-oracle family on the family state. -/
noncomputable def fusedImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl PqxdhServerAuthExperiment.ServerAuthSpec
      (StateT (PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State) ProbComp) :=
  ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
    PqxdhJointDhExtractRoot.reduction).mapStateTBase
      (PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed)).flattenStateT

/-- One combined step runs the handler step under the Extract random-oracle family. -/
theorem fused_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : PqxdhServerAuthExperiment.ServerAuthSpec.Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (fusedImpl setup codec checks publicValue beaconSeed seed scalar query).run state =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
          PqxdhJointDhExtractRoot.reduction)
          ((PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed query).run state.1)).run
            state.2 :=
  rfl

/-- The lockstep relation: the adversary touches of the ghost are the table-domain messages of the family history. -/
def Lockstep (state : PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State) : Prop :=
  adversaryTouches state.1.ghost.touches = romMessages state.2.history

/-- Every combined step keeps the lockstep relation: an adversary table query adds its message to both logs, and every other step adds to neither, because honest code makes no public family request. -/
theorem fused_lockstep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : PqxdhServerAuthExperiment.ServerAuthSpec.Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : PqxdhServerAuthExperiment.ServerAuthSpec.Range query ×
      (PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State))
    (supported : result ∈ support ((fusedImpl setup codec checks publicValue beaconSeed seed scalar query).run state))
    (lock : Lockstep state) : Lockstep result.2 := by
  rw [fused_run, support_map] at supported
  obtain ⟨z, zRun, rfl⟩ := supported
  have inner : z.1 ∈ support ((PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed
      query).run state.1) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh
      seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ zRun
  have touches := adversary_step setup codec checks publicValue beaconSeed query state.1 z.1 inner
  unfold Lockstep at lock ⊢
  dsimp only
  rw [touches, lock]
  by_cases hmacQuery : ∃ key message, query = .inr (.hmac key message)
  · obtain ⟨key, message, rfl⟩ := hmacQuery
    change z ∈ support ((simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
      PqxdhJointDhExtractRoot.reduction) ((PqxdhServerAuthExperiment.hmacOracle key message).run state.1)).run
        state.2) at zRun
    have run : ∃ ghostState : PqxdhServerAuthExperiment.GameState KemSK,
        (PqxdhServerAuthExperiment.hmacOracle key message).run state.1 =
          (liftM (RootSpec.query (.inr (.publicHmac key message))) : OracleComp RootSpec _) >>= fun block =>
            pure (block, ghostState) := by
      unfold PqxdhServerAuthExperiment.hmacOracle
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨ghostState, runEq⟩ := run
    rw [runEq, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at zRun
    obtain ⟨middle, first, rest⟩ := (mem_support_bind_iff _ _ _).1 zRun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
    subst rest
    rw [rom_step setup.hmac setup.joint setup.dh seed scalar _ state.2 middle first]
    rfl
  · have notHmac : ∀ key message, query ≠ .inr (.hmac key message) :=
      fun key message same => hmacQuery ⟨key, message, same⟩
    have quiet := honest_no_rom_public setup codec checks publicValue beaconSeed query notHmac state.1
    rw [rom_quiet setup.hmac setup.joint setup.dh seed scalar _ (quiet.of_imp table_public) state.2 z zRun,
      romMessage_quiet query notHmac, List.append_nil]

/-- Every combined step adds at most one adversary touch, and only at a query in the table domain. -/
theorem fused_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : PqxdhServerAuthExperiment.ServerAuthSpec.Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : PqxdhServerAuthExperiment.ServerAuthSpec.Range query ×
      (PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State))
    (supported : result ∈ support ((fusedImpl setup codec checks publicValue beaconSeed seed scalar query).run state)) :
    (adversaryTouches result.2.1.ghost.touches).length ≤ (adversaryTouches state.1.ghost.touches).length +
      if PqxdhServerAuthExperiment.IsRomQuery query then 1 else 0 := by
  rw [fused_run, support_map] at supported
  obtain ⟨z, zRun, rfl⟩ := supported
  have inner : z.1 ∈ support ((PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed
      query).run state.1) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh
      seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ zRun
  dsimp only
  rw [adversary_step setup codec checks publicValue beaconSeed query state.1 z.1 inner, List.length_append]
  refine Nat.add_le_add_left ?_ _
  rcases query with coin | query
  · simp [romMessage]
  · cases query with
    | hmac key message =>
        by_cases inside : key = zeroSalt ∧ message.length = 192
        · simp [romMessage, PqxdhServerAuthExperiment.IsRomQuery, inside]
        · simp [romMessage, inside]
    | _ => simp [romMessage]

/-- Every final state of the experiment is reached by a run of the combined handler from the initial game state, with an empty ghost, and the empty family state. -/
theorem gameState_fused (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthExperiment.gameState setup codec checks revealSeed adversary)) :
    ∃ (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (input : PqxdhServerAuthExperiment.AuthInput)
      (initial : PqxdhServerAuthExperiment.GameState KemSK)
      (final : Unit × (PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)),
      initial.ghost = PqxdhServerAuthExperiment.Ghost.empty ∧
      final ∈ support ((simulateQ (fusedImpl setup codec checks publicValue beaconSeed result.1 result.2.1)
        (adversary input)).run (initial, PqxdhJointDhExtractFamily.empty)) ∧
      final.2 = (result.2.2.1, result.2.2.2) := by
  simp only [PqxdhServerAuthExperiment.gameState, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, scalar, _, run, member, rfl⟩ := supported
  simp only [PqxdhServerAuthExperiment.body, simulateQ_bind, StateT.run_bind, PqxdhServerAuthExperiment.rom_coins,
    bind_map_left, mem_support_bind_iff] at member
  obtain ⟨beaconSeed, _, oneTime, _, keys, _, published, _, member⟩ := member
  rw [simulateQ_map, StateT.run_map, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map,
    support_map] at member
  obtain ⟨final, finalRun, rfl⟩ := member
  exact ⟨_, beaconSeed, _, _, final, rfl, finalRun, rfl⟩

/-- `touches_history`: on every run of the experiment, the adversary touches of the final ghost are exactly the table-domain messages of the final family history, in order. -/
theorem touches_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthExperiment.gameState setup codec checks revealSeed adversary)) :
    adversaryTouches result.2.2.1.ghost.touches = romMessages result.2.2.2.history := by
  obtain ⟨publicValue, beaconSeed, input, initial, final, empty, finalRun, same⟩ :=
    gameState_fused setup codec checks revealSeed adversary result supported
  have lock := PqxdhServerAuthExperiment.run_rel (fusedImpl setup codec checks publicValue beaconSeed result.1 result.2.1)
    (fun before after => Lockstep before → Lockstep after) (fun _ => id)
    (fun _ _ _ left right => right ∘ left)
    (fun query state next reached => fused_lockstep setup codec checks publicValue beaconSeed result.1 result.2.1
      query state next reached)
    (adversary input) _ final finalRun (by simp [Lockstep, empty, PqxdhServerAuthExperiment.Ghost.empty,
      adversaryTouches, romMessages, PqxdhJointDhExtractFamily.empty])
  rw [same] at lock
  exact lock

/-- On every run of the experiment in which the adversary makes at most `qH` table-domain HMAC queries, the final ghost holds at most `qH` adversary touches. -/
theorem adversary_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (qH : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (result : IdentitySeed × ScalarBytes × PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthExperiment.gameState setup codec checks revealSeed adversary)) :
    (adversaryTouches result.2.2.1.ghost.touches).length ≤ qH := by
  obtain ⟨publicValue, beaconSeed, input, initial, final, empty, finalRun, same⟩ :=
    gameState_fused setup codec checks revealSeed adversary result supported
  have count := PqxdhServerAuthExperiment.run_count
    (fusedImpl setup codec checks publicValue beaconSeed result.1 result.2.1) PqxdhServerAuthExperiment.IsRomQuery
    (fun state => (adversaryTouches state.1.ghost.touches).length)
    (fun query state next reached => fused_count setup codec checks publicValue beaconSeed result.1 result.2.1
      query state next reached)
    (adversary input) qH (rom input) _ final finalRun
  rw [same] at count
  simpa [empty, PqxdhServerAuthExperiment.Ghost.empty, adversaryTouches] using count

/-- The DH1 candidates of a family history are the DH1 coordinates of its table-domain messages. -/
theorem romCandidates_eq (history : PqxdhJointDhExtractFamily.History) :
    PqxdhServerAuthExperiment.romCandidates history = (romMessages history).filterMap (readDh 32) := by
  simp only [PqxdhServerAuthExperiment.romCandidates, romMessages, List.filterMap_filterMap]
  congr 1
  funext entry
  cases entry with
  | publicHmac key message block =>
      by_cases inside : key = zeroSalt ∧ message.length = 192 <;> simp [inside]
  | _ => rfl

/-- `candidates_length`: on every run of the experiment in which the adversary makes at most `qH` table-domain HMAC queries, the final family history has at most `qH` DH1 candidates, so the padded candidate vector keeps all of them. -/
theorem candidates_length (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (qH : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (result : IdentitySeed × ScalarBytes × PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthExperiment.gameState setup codec checks revealSeed adversary)) :
    (PqxdhServerAuthExperiment.romCandidates result.2.2.2.history).length ≤ qH := by
  rw [romCandidates_eq, ← touches_history setup codec checks revealSeed adversary result supported]
  exact (List.length_filterMap_le _ _).trans (adversary_count setup codec checks revealSeed adversary qH rom result
    supported)

/-- A value among at most `count` values is among the padded values. -/
theorem mem_padded (count : Nat) (values : List DhOutput) (value : DhOutput) (short : values.length ≤ count)
    (member : value ∈ values) : value ∈ (PqxdhServerAuthExperiment.padded count values).toList := by
  change value ∈ (values ++ List.replicate count zeroDh).take count
  rw [List.take_append, List.take_of_length_le short]
  exact List.mem_append_left _ member

/-- The Beacon's first logged derivation is a logged Beacon touch. -/
theorem firstBeacon_mem (touches : List PqxdhServerAuthExperiment.Touch) (message : Message)
    (found : PqxdhServerAuthExperiment.firstBeacon touches = some message) :
    PqxdhServerAuthExperiment.Touch.beacon message ∈ touches := by
  obtain ⟨touch, member, same⟩ := List.exists_of_findSome?_eq_some found
  cases touch with
  | beacon other =>
      cases same
      exact member
  | session _ _ _ => cases same
  | adversary _ => cases same

/-- Step A1 of the hybrid chain (`badB_candidate`): on every run of the experiment without a seed reveal in which the adversary makes at most `qH` table-domain HMAC queries, an adversary table query at the Beacon's root input puts the nonzero cross value DH1 among the padded candidates of the family history. The Beacon's root input has the prekey as static peer, so its DH1 coordinate is the Gap-DH target, which is nonzero; the query is in the family history (`touches_history`), and the candidates are not truncated (`candidates_length`). -/
theorem badB_candidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (result : IdentitySeed × ScalarBytes × PqxdhServerAuthExperiment.GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthExperiment.gameState setup codec checks false adversary))
    (bad : PqxdhServerAuthExperiment.BadB setup result.1 result.2.1 result.2.2.1.ghost) :
    PqxdhServerAuthExperiment.CandHit setup result.1 result.2.1 qH result.2.2.2.history := by
  obtain ⟨invariant, _⟩ := PqxdhServerAuthExperiment.gameState_reachable setup codec checks false adversary result
    supported
  obtain ⟨bytes, beacon, touched⟩ := bad
  unfold PqxdhServerAuthExperiment.beaconInput at beacon
  cases hfirst : PqxdhServerAuthExperiment.firstBeacon result.2.2.1.ghost.touches with
  | none =>
      rw [hfirst] at beacon
      cases beacon
  | some message =>
      rw [hfirst, Option.bind_some] at beacon
      obtain ⟨collected, _, _, rfl, _⟩ := invariant.beaconOrigin message (firstBeacon_mem _ _ hfirst)
      obtain ⟨first, third, firstEq, _, assembled⟩ :=
        (PqxdhJointDhExtractFamily.input_some_iff _ _ _ _ _ bytes).mp beacon
      have target : setup.joint.staticDh result.1 (setup.dh.publicKey result.2.1) = some first := firstEq
      refine ⟨first, target, ?_, ?_⟩
      · rw [setup.dh.agreement] at target
        exact PqxdhServerAuthAssumptions.sourceScalarDh_nonzero setup.source.crypto result.2.1 _ first target
      · refine mem_padded qH _ first (candidates_length setup codec checks false adversary qH rom result supported) ?_
        rw [romCandidates_eq, ← touches_history setup codec checks false adversary result supported]
        refine List.mem_filterMap.mpr ⟨bytes, ?_, ?_⟩
        · exact List.mem_filterMap.mpr ⟨_, touched, rfl⟩
        · rw [← assembled, PqxdhJointGapDh.read_first]

set_option linter.deprecated false in
/-- Main result of stage B6 (`badB_le_gapDh`, steps A1 to A3 of the hybrid chain): under the X25519 class law, if the adversary makes at most `qH` table-domain HMAC queries, the probability that it queries the Extract table at the Beacon's root input in the experiment without a seed reveal is at most the Gap-DH term of the scanning reduction `PqxdhJointGapDh.extractor (scanClient …)`, which is constructed from the adversary and holds neither secret. -/
theorem badB_le_gapDh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat) (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH) :
    Pr[fun result => PqxdhServerAuthExperiment.BadB setup result.1 result.2.1 result.2.2.1.ghost |
        PqxdhServerAuthExperiment.gameState setup codec checks false adversary] ≤
      PqxdhServerAuthAssumptions.serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed
        setup.wiring (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH)) := by
  rw [← candHit_eq_gapDh setup codec checks adversary qH law]
  exact probEvent_mono fun result supported bad =>
    badB_candidate setup codec checks adversary qH rom result supported bad

/-! ## Query counts of the reduction -/

section Counting
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}

/-- Potential bound for a stateful simulation with several source budgets: if each step from state `s` with remaining budgets `n` costs at most `c` target queries, with `c` plus the bound after the step at most the bound before it, then the whole simulation costs at most the bound at the initial state and budgets. -/
theorem run_potential {k : Nat} (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (p : Fin k → ι₁ → Prop) [∀ i, DecidablePred (p i)] (target : ι₂ → Prop) [DecidablePred target]
    (bound : (Fin k → Nat) → σ → Nat)
    (step : ∀ query state (budget : Fin k → Nat), (∀ i, p i query → 0 < budget i) →
      ∃ cost, ((impl query).run state).IsQueryBoundP target cost ∧ cost ≤ bound budget state ∧
        ∀ result ∈ support ((impl query).run state),
          cost + bound (fun i => if p i query then budget i - 1 else budget i) result.2 ≤ bound budget state)
    {α : Type} (oa : OracleComp spec₁ α) (budget : Fin k → Nat) (bounded : ∀ i, oa.IsQueryBoundP (p i) (budget i))
    (state : σ) :
    ((simulateQ impl oa).run state).IsQueryBoundP target (bound budget state) := by
  induction oa using OracleComp.inductionOn generalizing budget state with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      have split := fun i => (isQueryBoundP_query_bind_iff (p i) query next (budget i)).mp (bounded i)
      obtain ⟨cost, costBound, costLe, after⟩ := step query state budget
        (fun i found => (split i).1.resolve_left (not_not.mpr found))
      rw [simulateQ_query_bind, StateT.run_bind]
      have rest : ∀ result ∈ support ((impl query).run state),
          ((simulateQ impl (next result.1)).run result.2).IsQueryBoundP target (bound budget state - cost) :=
        fun result member => (ih result.1 _ (fun i => (split i).2 result.1) result.2).mono
          (Nat.le_sub_of_add_le' (after result member))
      have combined := isQueryBoundP_bind costBound rest
      rw [Nat.add_sub_cancel' costLe] at combined
      exact combined

end Counting

/-- Family requests other than coins. -/
def IsFamilyRequest : RootSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

/-- Family requests are decidable. -/
instance : DecidablePred IsFamilyRequest := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Root derivation requests. -/
def IsDeriveRoot : RootSpec.Domain → Prop
  | .inr (.derive _) => True
  | _ => False

/-- Root derivation requests are decidable. -/
instance : DecidablePred IsDeriveRoot := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr (.sign _) => isFalse id
  | .inr (.publicHmac _ _) => isFalse id
  | .inr (.derive _) => isTrue trivial

/-- Coin requests of the root-valued family interface. -/
def IsCoinRoot (query : RootSpec.Domain) : Prop := query.isLeft = true

/-- Coin requests are decidable. -/
instance : DecidablePred IsCoinRoot := fun query => inferInstanceAs (Decidable (query.isLeft = true))

/-- A root derivation is a family request. -/
theorem derive_family (query : RootSpec.Domain) (derive : IsDeriveRoot query) : IsFamilyRequest query := by
  rcases query with coin | (message | ⟨key, message⟩ | message) <;> simp_all [IsDeriveRoot, IsFamilyRequest]

/-- A game computation that makes at most `count` family requests other than coins, from any state. -/
def Costs {α : Type} (count : Nat) (work : PqxdhServerAuthExperiment.Game KemSK α) : Prop :=
  ∀ state, (work.run state).IsQueryBoundP IsFamilyRequest count

/-- A returned value makes no family request. -/
theorem costs_pure {α : Type} (value : α) : Costs 0 (pure value : PqxdhServerAuthExperiment.Game KemSK α) :=
  fun state => by simp

/-- Costs add up along a bind. -/
theorem costs_bind {α β : Type} {first : PqxdhServerAuthExperiment.Game KemSK α}
    {next : α → PqxdhServerAuthExperiment.Game KemSK β} {n m : Nat} (costFirst : Costs n first)
    (costNext : ∀ value, Costs m (next value)) : Costs (n + m) (first >>= next) := fun state => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (costFirst state) (fun pair _ => costNext pair.1 pair.2)

/-- Costs add up along a bind, within a given total. -/
theorem costs_seq {α β : Type} {first : PqxdhServerAuthExperiment.Game KemSK α}
    {next : α → PqxdhServerAuthExperiment.Game KemSK β} {n m total : Nat} (costFirst : Costs n first)
    (costNext : ∀ value, Costs m (next value)) (within : n + m ≤ total) : Costs total (first >>= next) :=
  fun state => (costs_bind costFirst costNext state).mono within

/-- Costs are monotone. -/
theorem costs_mono {α : Type} {work : PqxdhServerAuthExperiment.Game KemSK α} {n m : Nat} (cost : Costs n work)
    (le : n ≤ m) : Costs m work :=
  fun state => (cost state).mono le

/-- State access makes no family request. -/
theorem costs_get : Costs 0 (get : PqxdhServerAuthExperiment.Game KemSK (PqxdhServerAuthExperiment.GameState KemSK)) :=
  fun state => by simp

/-- State writes make no family request. -/
theorem costs_set (value : PqxdhServerAuthExperiment.GameState KemSK) :
    Costs 0 (set value : PqxdhServerAuthExperiment.Game KemSK PUnit) :=
  fun state => by simp

/-- State updates make no family request. -/
theorem costs_modify (change : PqxdhServerAuthExperiment.GameState KemSK → PqxdhServerAuthExperiment.GameState KemSK) :
    Costs 0 (modify change : PqxdhServerAuthExperiment.Game KemSK PUnit) :=
  fun state => by simp

/-- Family coins make no family request other than coins. -/
theorem familyCoins_costs {α : Type} (work : ProbComp α) :
    (PqxdhServerAuthExperiment.familyCoins work).IsQueryBoundP IsFamilyRequest 0 :=
  IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false work 0) (fun _ absurd => absurd.elim)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).mpr (fun found => absurd found id))

/-- Lifted coins make no family request other than coins. -/
theorem costs_liftCoins {α : Type} (work : ProbComp α) :
    Costs 0 (PqxdhServerAuthExperiment.liftCoins (KemSK := KemSK) work) := fun state => by
  simp only [PqxdhServerAuthExperiment.liftCoins, StateT.run_lift]
  simpa using familyCoins_costs work

/-- A forwarded request is one family request, or none when it is a coin. -/
theorem costs_forward (query : RootSpec.Domain) :
    Costs (if IsFamilyRequest query then 1 else 0) (PqxdhServerAuthExperiment.forwardFamily (KemSK := KemSK) query) :=
  fun state => by
    simp only [PqxdhServerAuthExperiment.forwardFamily, StateT.run_lift]
    exact (isQueryBoundP_bind ((isQueryBoundP_query_iff IsFamilyRequest query
      (if IsFamilyRequest query then 1 else 0)).mpr (fun found => by simp [found]))
      (fun _ _ => isQueryBoundP_pure IsFamilyRequest _ 0)).mono (by simp)

/-- Recording a touch makes no family request. -/
theorem costs_record (touch : PqxdhServerAuthExperiment.Touch) :
    Costs 0 (PqxdhServerAuthExperiment.recordTouch (KemSK := KemSK) touch) :=
  fun state => by simp [PqxdhServerAuthExperiment.record_run]

/-- Work on the shared BLAKE2b cache makes no family request other than coins. -/
theorem costs_onCtx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    Costs 0 (PqxdhServerAuthExperiment.onCtx (KemSK := KemSK) work) := fun state => by
  change (PqxdhServerAuthExperiment.familyCoins (work.run ((), state.ctx)) >>= fun result =>
    pure (result.1, { state with ctx := result.2.2 })).IsQueryBoundP IsFamilyRequest 0
  simpa using familyCoins_costs (work.run ((), state.ctx))

/-- Family requests of the Server's root-consumer interface. -/
def IsClientFamily : PqxdhServerRelatedRootConsumer.Spec.Domain → Prop
  | .inl query => IsFamilyRequest query
  | .inr _ => False

/-- Root-consumer family requests are decidable. -/
instance : DecidablePred IsClientFamily := fun query =>
  match query with
  | .inl query => inferInstanceAs (Decidable (IsFamilyRequest query))
  | .inr _ => isFalse id

/-- The Server's root consumer makes at most one family request, its root derivation. -/
theorem client_costs (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) :
    (PqxdhServerRelatedRootConsumer.client binding input).IsQueryBoundP IsClientFamily 1 := by
  classical
  unfold PqxdhServerRelatedRootConsumer.client
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl id, fun _ => ?_⟩
  split
  · trivial
  · rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.one_pos, fun root => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl id, fun _ => ?_⟩
    split
    · trivial
    · rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun _ => trivial⟩

/-- A step of a Server session's callbacks makes a family request only when it forwards one. -/
theorem session_costs (index : Nat) (query : PqxdhServerRelatedRootConsumer.Spec.Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.sessionImpl index query).run state).IsQueryBoundP IsFamilyRequest
      (if IsClientFamily query then 1 else 0) := by
  rcases query with (coin | (message | ⟨key, message⟩ | message)) | aux
  · exact costs_forward _ state
  · exact costs_forward _ state
  · exact costs_forward _ state
  · exact costs_bind (costs_forward _) (fun reply => costs_bind (costs_record _) fun _ => costs_pure _) state
  · cases aux
    · exact costs_pure _ state
    · exact costs_pure _ state
    · exact costs_modify _ state

/-- A Server accept makes at most one family request, its root derivation. -/
theorem accept_costs (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) :
    Costs 1 (PqxdhServerAuthExperiment.acceptOracle setup codec checks publicValue raw) := by
  unfold PqxdhServerAuthExperiment.acceptOracle
  refine costs_seq (m := 1) costs_get (fun state => ?_) (by omega)
  refine costs_seq (m := 1) (costs_liftCoins _) (fun collected => ?_) (by omega)
  refine costs_seq (m := 1) (costs_set _) (fun _ => ?_) (by omega)
  split
  · exact costs_mono (costs_pure _) (Nat.zero_le _)
  · refine costs_seq (m := 0) (fun state => IsQueryBoundP.simulateQ_run_StateT_of_step (client_costs _ _)
      (fun query state => session_costs _ query state) state) (fun returned => ?_) (by omega)
    split
    · exact costs_seq (costs_modify _) (fun _ => costs_pure _) (by omega)
    · exact costs_pure _

/-- A Server build makes no family request other than coins. -/
theorem build_costs (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) :
    Costs 0 (PqxdhServerAuthExperiment.buildOracle setup codec checks session payload) := by
  unfold PqxdhServerAuthExperiment.buildOracle
  refine costs_seq (m := 0) costs_get (fun state => ?_) (by omega)
  split
  · exact costs_pure _
  · exact costs_seq (m := 0) (costs_liftCoins _)
      (fun result => costs_seq (costs_set _) (fun _ => costs_pure _) (by omega)) (by omega)

/-- Family requests of the Beacon's related-root tail interface. -/
def IsTailFamily : (PqxdhPhase2DhRootConsumer.Spec Response).Domain → Prop
  | .inl query => IsFamilyRequest query
  | .inr _ => False

/-- Tail family requests are decidable. -/
instance : DecidablePred (IsTailFamily (Response := Response)) := fun query =>
  match query with
  | .inl query => inferInstanceAs (Decidable (IsFamilyRequest query))
  | .inr _ => isFalse id

/-- Family requests of the Beacon's Phase 2 stage interface. -/
def IsStageFamily : (PqxdhPhase2DhStage.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain → Prop
  | .inl _ => False
  | .inr query => IsTailFamily query

/-- Stage family requests are decidable. -/
instance : DecidablePred (IsStageFamily (KemSK := KemSK) (Response := Response)) := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable (IsTailFamily query))

/-- The Beacon's related-root tail makes at most one family request, its root derivation. -/
theorem tail_costs (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (PqxdhPhase2DhRootConsumer.tail publicValue decode pending).IsQueryBoundP IsTailFamily 1 := by
  unfold PqxdhPhase2DhRootConsumer.tail
  refine isQueryBoundP_bind (n := 1) (m := 0) ?_ fun value _ => ?_
  · refine IsQueryBoundP.simulateQ_of_step (p := IsFamilyRequest) (n := 1) ?_ ?_ ?_
    · unfold PqxdhPhase2DhRootConsumer.root
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · intro query _
      exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
    · intro query quiet
      exact (isQueryBoundP_query_iff _ _ _).mpr fun found => absurd found quiet
  · split
    · trivial
    · refine IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false _ 0)
        (fun _ absurd => absurd.elim) ?_
      intro query _
      exact (isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim

/-- The Beacon's Phase 2 stage makes at most one family request. -/
theorem stage_costs (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (raw : Pqxdh.Bytes) :
    (PqxdhPhase2DhStage.stage (X := Unit) (Response := Response) publicValue decode control identity oneTime kem
      raw).IsQueryBoundP IsStageFamily 1 := by
  unfold PqxdhPhase2DhStage.stage
  refine isQueryBoundP_bind (n := 0) (m := 1) ?_ fun pending _ => ?_
  · refine IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false _ 0)
      (fun _ absurd => absurd.elim) ?_
    intro query _
    exact (isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim
  · split
    · trivial
    · refine IsQueryBoundP.simulateQ_of_step (p := IsTailFamily) (tail_costs _ _ _) ?_ ?_
      · intro query _
        exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
      · intro query quiet
        exact (isQueryBoundP_query_iff _ _ _).mpr fun found => absurd found quiet

/-- A step of the Beacon's stage callbacks makes a family request only when it forwards one. -/
theorem stage_costs_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (query : (PqxdhPhase2DhStage.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain)
    (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.stageImpl setup codec beaconSeed query).run state).IsQueryBoundP IsFamilyRequest
      (if IsStageFamily query then 1 else 0) := by
  rcases query with query | (coin | (message | ⟨key, message⟩ | message)) | query
  · exact costs_liftCoins _ state
  · exact costs_forward _ state
  · exact costs_forward _ state
  · exact costs_forward _ state
  · exact costs_bind (costs_record _) (fun _ => costs_forward _) state
  · exact costs_onCtx _ state

/-- Whether the Beacon is in the InitSent phase, as a number. -/
def initSentFlag (state : PqxdhServerAuthExperiment.GameState KemSK) : Nat :=
  match state.beacon.beacon.phase with
  | .initSent _ _ _ _ => 1
  | _ => 0

/-- Outside the InitSent phase the flag is zero. -/
theorem initSentFlag_zero (state : PqxdhServerAuthExperiment.GameState KemSK)
    (inactive : ¬ PqxdhServerAuthExperiment.InitSent state) : initSentFlag state = 0 := by
  unfold initSentFlag
  split
  · rename_i control prekey oneTime kem phase
    exact absurd ⟨control, prekey, oneTime, kem, phase⟩ inactive
  · rfl

/-- The flag is at most one. -/
theorem initSentFlag_le (state : PqxdhServerAuthExperiment.GameState KemSK) : initSentFlag state ≤ 1 := by
  unfold initSentFlag
  split <;> omega

/-- The Beacon's finish makes at most one family request, and none outside the InitSent phase. -/
theorem finish_costs (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (publicValue : PublicChallenge)
    (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.finishOracle setup codec publicValue beaconSeed raw).run state).IsQueryBoundP
      IsFamilyRequest (initSentFlag state) := by
  unfold PqxdhServerAuthExperiment.finishOracle initSentFlag
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rename_i control prekey oneTime kem phase
    rw [phase]
    exact costs_seq (m := 0) (fun state => IsQueryBoundP.simulateQ_run_StateT_of_step (stage_costs _ _ _ _ _ _ _)
      (fun query state => stage_costs_step setup codec beaconSeed query state) state)
      (fun staged => costs_seq (m := 0) costs_get
        (fun current => costs_seq (costs_set _) (fun _ => costs_pure _) (by omega)) (by omega)) (le_of_eq rfl) state
  · simp

/-- Family coins make no request outside the coins. -/
theorem familyCoins_bound (p : RootSpec.Domain → Prop) [DecidablePred p] (coins : ∀ coin, ¬ p (.inl coin))
    {α : Type} (work : ProbComp α) : (PqxdhServerAuthExperiment.familyCoins work).IsQueryBoundP p 0 :=
  IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false work 0) (fun _ absurd => absurd.elim)
    (fun coin _ => (isQueryBoundP_query_iff _ _ _).mpr (fun found => absurd found (coins coin)))

/-- The adversary's public HMAC query is one forwarded public HMAC request, after which the game state is fixed. -/
theorem hmac_run (key : HmacBlock) (message : Pqxdh.Bytes) (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ∃ after : PqxdhServerAuthExperiment.GameState KemSK,
      (PqxdhServerAuthExperiment.hmacOracle key message).run state =
        (liftM (RootSpec.query (.inr (.publicHmac key message))) : OracleComp RootSpec _) >>= fun block =>
          pure (block, after) := by
  unfold PqxdhServerAuthExperiment.hmacOracle
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The adversary's public HMAC query makes exactly one family request, its public HMAC request. -/
theorem hmac_costs (p : RootSpec.Domain → Prop) [DecidablePred p] (key : HmacBlock) (message : Pqxdh.Bytes)
    (state : PqxdhServerAuthExperiment.GameState KemSK) :
    ((PqxdhServerAuthExperiment.hmacOracle key message).run state).IsQueryBoundP p
      (if p (.inr (.publicHmac key message)) then 1 else 0) := by
  obtain ⟨after, run⟩ := hmac_run key message state
  rw [run]
  exact (isQueryBoundP_bind ((isQueryBoundP_query_iff p _ (if p (.inr (.publicHmac key message)) then 1 else 0)).mpr
    (fun found => by simp [found])) (fun _ _ => isQueryBoundP_pure p _ 0)).mono (by simp)

/-- A BLAKE2b query makes no family request other than coins. -/
theorem hash_costs (bytes : Pqxdh.Bytes) : Costs 0 (PqxdhServerAuthExperiment.hashOracle (KemSK := KemSK) bytes) :=
  fun state => by
    change (PqxdhServerAuthExperiment.familyCoins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx) >>=
      fun result => pure (result.1, { state with ctx := result.2 })).IsQueryBoundP IsFamilyRequest 0
    simpa using familyCoins_costs ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx)

/-- The experiment body inherits a bound on requests other than coins from every run of the adversary. -/
theorem body_bound (p : RootSpec.Domain → Prop) [DecidablePred p] (coins : ∀ coin, ¬ p (.inl coin))
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (adversary : Adversary)
    (revealed : Option IdentitySeed) (publicValue : PublicChallenge) (count : Nat)
    (run : ∀ beaconSeed input initial,
      ((simulateQ (PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed)
        (adversary input)).run initial).IsQueryBoundP p count) :
    (PqxdhServerAuthExperiment.body setup codec checks adversary revealed publicValue).IsQueryBoundP p count := by
  unfold PqxdhServerAuthExperiment.body
  refine (isQueryBoundP_bind (m := count) (familyCoins_bound p coins _) fun beaconSeed _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (m := count) (familyCoins_bound p coins _) fun oneTime _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (m := count) (familyCoins_bound p coins _) fun keys _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (m := count) (familyCoins_bound p coins _) fun published _ => ?_).mono (by omega)
  rw [isQueryBoundP_map_iff]
  exact run beaconSeed _ _

/-- The experiment body makes no signing request. -/
theorem body_sign (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    (PqxdhServerAuthExperiment.body setup codec checks adversary revealed publicValue).IsQueryBoundP IsSignRoot 0 := by
  refine body_bound IsSignRoot (fun _ found => found) setup codec checks adversary revealed publicValue 0 ?_
  intro beaconSeed input initial
  refine IsQueryBoundP.simulateQ_run_StateT_of_step (p := fun _ => False) (isQueryBoundP_false _ 0) ?_ initial
  intro query state
  simp only [↓reduceIte]
  by_cases hmacQuery : ∃ key message, query = .inr (.hmac key message)
  · obtain ⟨key, message, rfl⟩ := hmacQuery
    have bound : ((PqxdhServerAuthExperiment.hmacOracle key message).run state).IsQueryBoundP IsSignRoot 0 := by
      simpa [IsSignRoot] using hmac_costs IsSignRoot key message state
    exact bound
  · exact (honest_no_rom_public setup codec checks publicValue beaconSeed query
      (fun key message same => hmacQuery ⟨key, message, same⟩) state).of_imp sign_public

/-- The experiment body makes at most `qH` table requests when the adversary makes at most `qH` table-domain HMAC queries. -/
theorem body_table (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    (PqxdhServerAuthExperiment.body setup codec checks adversary revealed publicValue).IsQueryBoundP IsTableRoot qH := by
  refine body_bound IsTableRoot (fun _ found => found) setup codec checks adversary revealed publicValue qH ?_
  intro beaconSeed input initial
  refine IsQueryBoundP.simulateQ_run_StateT_of_step (rom input) ?_ initial
  intro query state
  by_cases hmacQuery : ∃ key message, query = .inr (.hmac key message)
  · obtain ⟨key, message, rfl⟩ := hmacQuery
    exact hmac_costs IsTableRoot key message state
  · have notRom : ¬ PqxdhServerAuthExperiment.IsRomQuery query := by
      rcases query with coin | query
      · exact id
      · cases query with
        | hmac key message => exact absurd ⟨key, message, rfl⟩ hmacQuery
        | _ => exact id
    simp only [notRom, ↓reduceIte]
    exact (honest_no_rom_public setup codec checks publicValue beaconSeed query
      (fun key message same => hmacQuery ⟨key, message, same⟩) state).of_imp table_public

/-- The experiment body makes at most `Q + 1` root derivations when the adversary makes at most `Q` Server accepts: one per accept, and one for the single-shot finish. -/
theorem body_derive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q : Nat)
    (accept : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsAcceptQuery Q)
    (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    (PqxdhServerAuthExperiment.body setup codec checks adversary revealed publicValue).IsQueryBoundP IsDeriveRoot
      (Q + 1) := by
  refine body_bound IsDeriveRoot (fun _ found => found) setup codec checks adversary revealed publicValue (Q + 1) ?_
  intro beaconSeed input initial
  have potential := run_potential (k := 1)
    (PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed)
    (fun _ => PqxdhServerAuthExperiment.IsAcceptQuery) IsDeriveRoot
    (fun budget state => budget 0 + initSentFlag state) ?_ (adversary input) (fun _ => Q)
    (fun _ => accept input) initial
  · exact potential.mono (Nat.add_le_add_left (initSentFlag_le initial) Q)
  intro query state budget positive
  have sameFlag : ∀ result ∈ support ((PqxdhServerAuthExperiment.authHandler setup codec checks publicValue beaconSeed
      query).run state), (∀ raw, query ≠ .inr (.finish raw)) → initSentFlag result.2 = initSentFlag state :=
    fun result member notFinish => by
      unfold initSentFlag
      rw [(PqxdhServerAuthExperiment.authHandler_step (Reader := Reader) (Response := Response) codec checks
        beaconSeed query state result member).2.2.2.2 notFinish]
  rcases query with coin | query
  · refine ⟨0, (costs_forward (KemSK := KemSK) (.inl coin) state).of_imp derive_family, Nat.zero_le _, ?_⟩
    intro result member
    rw [sameFlag result member (fun _ same => by cases same)]
    simp [PqxdhServerAuthExperiment.IsAcceptQuery]
  cases query with
  | accept raw =>
      have one := positive 0 trivial
      refine ⟨1, (accept_costs setup codec checks publicValue raw state).of_imp derive_family, by omega, ?_⟩
      intro result member
      rw [sameFlag result member (fun _ same => by cases same)]
      split_ifs with isAccept
      · dsimp only
        omega
      · exact absurd trivial isAccept
  | build session payload =>
      refine ⟨0, (build_costs setup codec checks session payload state).of_imp derive_family, Nat.zero_le _, ?_⟩
      intro result member
      rw [sameFlag result member (fun _ same => by cases same)]
      simp [PqxdhServerAuthExperiment.IsAcceptQuery]
  | finish raw =>
      refine ⟨initSentFlag state, (finish_costs setup codec publicValue beaconSeed raw state).of_imp derive_family,
        Nat.le_add_left _ _, ?_⟩
      intro result member
      have after := (PqxdhServerAuthExperiment.finish_step (Reader := Reader) (Response := Response)
        (publicValue := publicValue) codec beaconSeed raw state result member).2.2.2.1
      rw [initSentFlag_zero _ after]
      simp [PqxdhServerAuthExperiment.IsAcceptQuery]
      omega
  | hmac key message =>
      have bound : ((PqxdhServerAuthExperiment.hmacOracle key message).run state).IsQueryBoundP IsDeriveRoot 0 := by
        simpa [IsDeriveRoot] using hmac_costs IsDeriveRoot key message state
      refine ⟨0, bound, Nat.zero_le _, ?_⟩
      intro result member
      rw [sameFlag result member (fun _ same => by cases same)]
      simp [PqxdhServerAuthExperiment.IsAcceptQuery]
  | hash bytes =>
      refine ⟨0, (hash_costs bytes state).of_imp derive_family, Nat.zero_le _, ?_⟩
      intro result member
      rw [sameFlag result member (fun _ same => by cases same)]
      simp [PqxdhServerAuthExperiment.IsAcceptQuery]
  | reveal keyId =>
      refine ⟨0, by
        change (pure _ : OracleComp RootSpec _).IsQueryBoundP IsDeriveRoot 0
        trivial, Nat.zero_le _, ?_⟩
      intro result member
      rw [sameFlag result member (fun _ same => by cases same)]
      simp [PqxdhServerAuthExperiment.IsAcceptQuery]

/-! ## Query counts of the symbolic family -/

/-- A Gap-DH computation that makes at most `count` decision requests and no other request. -/
def Decides {α : Type} (count : Nat) (work : OracleComp PqxdhJointGapDh.AdversarySpec α) : Prop :=
  work.IsQueryBoundP PqxdhJointGapDh.IsDecision count ∧
    work.IsQueryBoundP (fun query => ¬ PqxdhJointGapDh.IsDecision query) 0

/-- A returned value makes no request. -/
theorem decides_pure {α : Type} (value : α) (count : Nat) :
    Decides count (pure value : OracleComp PqxdhJointGapDh.AdversarySpec α) :=
  ⟨trivial, trivial⟩

/-- Decision counts add up along a bind. -/
theorem decides_bind {α β : Type} {first : OracleComp PqxdhJointGapDh.AdversarySpec α}
    {next : α → OracleComp PqxdhJointGapDh.AdversarySpec β} {n m total : Nat} (decidesFirst : Decides n first)
    (decidesNext : ∀ value, Decides m (next value)) (within : n + m ≤ total) : Decides total (first >>= next) :=
  ⟨(isQueryBoundP_bind decidesFirst.1 fun value _ => (decidesNext value).1).mono within,
    isQueryBoundP_bind decidesFirst.2 fun value _ => (decidesNext value).2⟩

/-- Decision counts are monotone. -/
theorem decides_mono {α : Type} {work : OracleComp PqxdhJointGapDh.AdversarySpec α} {n m : Nat}
    (decides : Decides n work) (le : n ≤ m) : Decides m work :=
  ⟨decides.1.mono le, decides.2⟩

/-- One decision request. -/
theorem decides_decision (usePrekey : Bool) (peer : PeerEncoding) (candidate : DhOutput) :
    Decides 1 (decision usePrekey peer candidate) :=
  ⟨(isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos,
    (isQueryBoundP_query_iff _ _ _).mpr fun found => (found trivial).elim⟩

/-- The one-coordinate matcher makes at most one decision request. -/
theorem decides_testServer (address : ServerAddress) (candidate : Pqxdh.Bytes) :
    Decides 1 (testServer address candidate) := by
  unfold testServer
  split
  · exact decides_pure _ _
  · exact decides_decision _ _ _

/-- Testing concrete bytes against a message makes at most two decision requests. -/
theorem decides_concreteTest (message : Message) (candidate : Pqxdh.Bytes) :
    Decides 2 (concreteTest message candidate) := by
  unfold concreteTest
  split
  · exact decides_mono (decides_testServer _ _) (by omega)
  · exact ⟨(PqxdhJointGapDh.testInput_query_bound _ _).isQueryBoundP,
      PqxdhJointGapDh.testInput_excludes _ _ _ fun _ _ _ found => found trivial⟩

/-- Comparing two third coordinates makes at most one decision request. -/
theorem decides_thirdSame (c : Pqxdh.Crypto) (left right : Third) : Decides 1 (thirdSame c left right) := by
  cases left <;> cases right
  · exact decides_pure _ _
  · exact decides_decision _ _ _
  · exact decides_decision _ _ _
  · exact decides_pure _ _

/-- Comparing two messages makes at most one decision request. -/
theorem decides_messageSame (c : Pqxdh.Crypto) (left right : Message) : Decides 1 (messageSame c left right) := by
  unfold messageSame
  split
  · exact decides_thirdSame _ _ _
  · exact decides_pure _ _

/-- Decision cost of comparing a queried key with a table key: none for two concrete keys, at most one for two messages, at most two otherwise. -/
def sameCost : SymKey → SymKey → Nat
  | .concrete _, .concrete _ => 0
  | .message _, .message _ => 1
  | _, _ => 2

/-- A comparison makes at most its cost in decision requests. -/
theorem decides_symSame (c : Pqxdh.Crypto) (query entry : SymKey) :
    Decides (sameCost query entry) (symSame c query entry) := by
  cases query <;> cases entry
  · exact decides_pure _ _
  · exact decides_concreteTest _ _
  · exact decides_concreteTest _ _
  · exact decides_messageSame _ _ _

/-- Decision cost of a lookup: the sum of the comparison costs over the table. -/
def lookupCost (query : SymKey) (table : List (SymKey × HmacBlock)) : Nat :=
  (table.map fun entry => sameCost query entry.1).sum

/-- A lookup makes at most its cost in decision requests. -/
theorem decides_symLookup (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock)) :
    Decides (lookupCost query table) (symLookup c query table) := by
  induction table with
  | nil => exact decides_pure _ _
  | cons entry rest ih =>
      unfold symLookup
      refine decides_bind (m := lookupCost query rest) (decides_symSame c query entry.1) (fun hit => ?_)
        (by simp [lookupCost])
      split
      · exact decides_pure _ _
      · exact ih

/-- Whether a symbolic key is concrete. -/
def SymKey.isConcrete : SymKey → Bool
  | .concrete _ => true
  | .message _ => false

/-- The number of concrete entries of a table. -/
def concreteCount (table : List (SymKey × HmacBlock)) : Nat :=
  (table.filter fun entry => entry.1.isConcrete).length

/-- The number of message entries of a table. -/
def messageCount (table : List (SymKey × HmacBlock)) : Nat :=
  (table.filter fun entry => !entry.1.isConcrete).length

/-- A concrete lookup costs at most two decisions per message entry. -/
theorem lookupCost_concrete (bytes : Pqxdh.Bytes) (table : List (SymKey × HmacBlock)) :
    lookupCost (.concrete bytes) table = 2 * messageCount table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, block⟩
      cases key <;> simp_all [lookupCost, messageCount, sameCost, SymKey.isConcrete]
      omega

/-- A message lookup costs at most two decisions per concrete entry and one per message entry. -/
theorem lookupCost_message (message : Message) (table : List (SymKey × HmacBlock)) :
    lookupCost (.message message) table = 2 * concreteCount table + messageCount table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, block⟩
      cases key <;> simp_all [lookupCost, messageCount, concreteCount, sameCost, SymKey.isConcrete] <;> omega

/-- Lifted uniform work preserves its complete source sampling bill. -/
theorem symCoins_uniform {α : Type} (work : ProbComp α) (count : Nat)
    (bounded : work.IsTotalQueryBound count) :
    (symCoins work).IsQueryBoundP PqxdhJointGapDh.IsUniform count := by
  exact IsQueryBoundP.simulateQ_of_step bounded.isQueryBoundP
    (fun query _ => (isQueryBoundP_query_iff _ _ _).mpr (fun _ => Nat.one_pos))
    (fun _ absent => (absent trivial).elim)

/-- Lifted uniform work cannot ask either secret-dependent service. -/
theorem symCoins_excludes {α : Type} (work : ProbComp α)
    (p : PqxdhJointGapDh.AdversarySpec.Domain → Prop) [DecidablePred p]
    (excluded : ∀ coin, ¬ p (.inl coin)) : (symCoins work).IsQueryBoundP p 0 := by
  exact IsQueryBoundP.simulateQ_of_step (p := fun _ => False) (isQueryBoundP_false work 0)
    (fun _ absent => absent.elim)
    (fun coin _ => (isQueryBoundP_query_iff _ _ _).mpr (fun found => (excluded coin found).elim))

/-- A symbolic lookup asks only decisions, within its explicit comparison sum. -/
theorem symRead_decisions (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock)) :
    (symRead c query table).IsQueryBoundP PqxdhJointGapDh.IsDecision (lookupCost query table) := by
  unfold symRead
  apply (isQueryBoundP_bind (m := 0) (decides_symLookup c query table).1 _).mono (by omega)
  intro result _
  cases result
  · simpa using symCoins_excludes ($ᵗ HmacBlock) PqxdhJointGapDh.IsDecision (fun _ found => found)
  · trivial

/-- Every table miss samples exactly one 64-byte block; hits sample none. -/
theorem symRead_uniform (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock)) :
    (symRead c query table).IsQueryBoundP PqxdhJointGapDh.IsUniform 64 := by
  unfold symRead
  apply (isQueryBoundP_bind (n := 0) (m := 64)
    ((decides_symLookup c query table).2.of_imp (fun query found => by
      rcases query with coin | request
      · exact fun impossible => impossible
      · cases found)) _).mono (by omega)
  intro result _
  cases result
  · simpa using symCoins_uniform ($ᵗ HmacBlock) 64 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
  · trivial

/-- Reading the table makes no signing request. -/
theorem symRead_signing (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock)) :
    (symRead c query table).IsQueryBoundP PqxdhJointGapDh.IsSigning 0 := by
  unfold symRead
  apply isQueryBoundP_bind (m := 0) ((decides_symLookup c query table).2.of_imp (fun query found => by
    rcases query with coin | request
    · cases found
    · cases request with
      | sign _ => exact fun impossible => impossible
      | decideDh _ _ _ => cases found))
  intro result _
  cases result
  · simpa using symCoins_excludes ($ᵗ HmacBlock) PqxdhJointGapDh.IsSigning (fun _ found => found)
  · trivial

/-- A table read either keeps the table or appends its one sampled entry. -/
theorem symRead_table (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock))
    (result : HmacBlock × List (SymKey × HmacBlock)) (reached : result ∈ support (symRead c query table)) :
    result.2 = table ∨ result.2 = table ++ [(query, result.1)] := by
  simp only [symRead, mem_support_bind_iff] at reached
  obtain ⟨found, _, reached⟩ := reached
  cases found with
  | some block =>
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst result
      exact Or.inl rfl
  | none =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
      obtain ⟨block, _, rfl⟩ := reached
      exact Or.inr rfl

/-- A read adds at most one concrete or one symbolic message entry, as requested. -/
theorem symRead_growth (c : Pqxdh.Crypto) (query : SymKey) (table : List (SymKey × HmacBlock))
    (result : HmacBlock × List (SymKey × HmacBlock)) (reached : result ∈ support (symRead c query table)) :
    concreteCount result.2 ≤ concreteCount table + (if query.isConcrete then 1 else 0) ∧
    messageCount result.2 ≤ messageCount table + (if query.isConcrete then 0 else 1) := by
  obtain same | same := symRead_table c query table result reached
  · rw [same]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · rw [same]
    cases query <;> simp [concreteCount, messageCount, List.filter_append, SymKey.isConcrete]

/-- The root projection adds a real Expand evaluation outside the Extract table. -/
theorem symRoot_derive (setup : Setup baseSpec KemSK) (message : Message) (state : SymState) :
    ((symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) (.inr (.derive message))).run state =
      if symAccepts setup message then do
        let read ← symRead setup.source.crypto (.message message) state.table
        let block := setup.hmac.eval read.1 rootExpandInput
        pure (some (first32 block), ⟨state.history ++ [.derive message (some read.1),
          .publicHmac read.1 rootExpandInput block], read.2⟩)
      else pure (none, { state with history := state.history ++ [.derive message none] }) := by
  change (simulateQ (symImpl setup) (PqxdhJointDhExtractRoot.root message)).run state = _
  simp only [PqxdhJointDhExtractRoot.root, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((if symAccepts setup message then _ else _) >>= _) = _
  split <;> simp only [bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
  apply bind_congr
  intro read
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((if read.1 = zeroSalt ∧ rootExpandInput.length = 192 then _ else _) >>= _) = _
  rw [ite_eq_right (PqxdhExtractRomFamily.rootExpand_outside read.1)]
  simp [List.append_assoc]

/-- Decision allowance for one root-interface request. -/
def rootDecisionCost (query : RootSpec.Domain) (state : SymState) : Nat :=
  match query with
  | .inr (.publicHmac key message) =>
      if key = zeroSalt ∧ message.length = 192 then 2 * messageCount state.table else 0
  | .inr (.derive _) => 2 * concreteCount state.table + messageCount state.table
  | _ => 0

/-- Each root-interface request pays its full symbolic table scan. -/
theorem symRoot_decisions (setup : Setup baseSpec KemSK) (query : RootSpec.Domain) (state : SymState) :
    (((symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run state).IsQueryBoundP
      PqxdhJointGapDh.IsDecision (rootDecisionCost query state) := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · change ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inl coin)) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>= fun value =>
      pure (value, state)).IsQueryBoundP PqxdhJointGapDh.IsDecision 0
    exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim)
      (fun _ _ => trivial)
  · change ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.sign message))) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>= fun value =>
      pure (value, { state with history := state.history ++ [PqxdhJointDhExtractFamily.Observation.sign message value] })).IsQueryBoundP PqxdhJointGapDh.IsDecision 0
    exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim)
      (fun _ _ => trivial)
  · simp only [QueryImpl.compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query]
    change OracleComp.IsQueryBoundP (if key = zeroSalt ∧ message.length = 192 then _ else _) _ _
    unfold rootDecisionCost
    split_ifs with inside
    · simpa [inside, lookupCost_concrete] using
        symRead_decisions setup.source.crypto (.concrete message) state.table
    · trivial
  · rw [symRoot_derive]
    unfold rootDecisionCost
    split
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff, lookupCost_message] using
        symRead_decisions setup.source.crypto (.message message) state.table
    · trivial

/-- The interpreter signs only a source signing request. -/
theorem symRoot_signing (setup : Setup baseSpec KemSK) (query : RootSpec.Domain) (state : SymState) :
    (((symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run state).IsQueryBoundP
      PqxdhJointGapDh.IsSigning (if IsSignRoot query then 1 else 0) := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · change ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inl coin)) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>=
      fun value => pure (value, state)).IsQueryBoundP PqxdhJointGapDh.IsSigning 0
    exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr fun found => found.elim)
      (fun _ _ => trivial)
  · change ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.sign message))) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>=
      fun value => pure (value, { state with history := state.history ++
        [PqxdhJointDhExtractFamily.Observation.sign message value] })).IsQueryBoundP PqxdhJointGapDh.IsSigning 1
    exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos)
      (fun _ _ => trivial)
  · simp only [QueryImpl.compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query]
    change OracleComp.IsQueryBoundP (if key = zeroSalt ∧ message.length = 192 then _ else _) _ 0
    split
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        symRead_signing setup.source.crypto (.concrete message) state.table
    · trivial
  · rw [symRoot_derive]
    change OracleComp.IsQueryBoundP (if symAccepts setup message then _ else _) _ 0
    split
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        symRead_signing setup.source.crypto (.message message) state.table
    · trivial

/-- The complete scanning client makes no signing request, including its honest Phase 1. Its Beacon signatures use the locally generated Beacon seed, not the challenge Server seed. -/
theorem scanClient_signing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH : Nat) (publicValue : PublicChallenge) :
    (scanClient setup codec checks adversary qH publicValue).IsQueryBoundP PqxdhJointGapDh.IsSigning 0 := by
  unfold scanClient
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (body_sign setup codec checks adversary none publicValue)
    (symRoot_signing setup) SymState.empty

/-- Uniform allowance for one root-interface request, including a possible table miss. -/
def rootUniformCost (query : RootSpec.Domain) : Nat :=
  (if IsCoinRoot query then 1 else 0) + 64 * (if IsTableRoot query then 1 else 0) +
    64 * (if IsDeriveRoot query then 1 else 0)

/-- Each symbolic request retains its source coins and charges possible new table sampling. -/
theorem symRoot_uniform (setup : Setup baseSpec KemSK) (query : RootSpec.Domain) (state : SymState) :
    (((symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run state).IsQueryBoundP
      PqxdhJointGapDh.IsUniform (rootUniformCost query) := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · change ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inl coin)) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>=
      fun value => pure (value, state)).IsQueryBoundP PqxdhJointGapDh.IsUniform 1
    exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos)
      (fun _ _ => trivial)
  · change ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.sign message))) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>=
      fun value => pure (value, { state with history := state.history ++
        [PqxdhJointDhExtractFamily.Observation.sign message value] })).IsQueryBoundP PqxdhJointGapDh.IsUniform 0
    exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).mpr fun found => by cases found)
      (fun _ _ => trivial)
  · simp only [QueryImpl.compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query]
    change OracleComp.IsQueryBoundP (if key = zeroSalt ∧ message.length = 192 then _ else _) _ _
    split_ifs with inside
    · simpa [rootUniformCost, IsCoinRoot, IsTableRoot, IsDeriveRoot, inside] using
        symRead_uniform setup.source.crypto (.concrete message) state.table
    · trivial
  · rw [symRoot_derive]
    change OracleComp.IsQueryBoundP (if symAccepts setup message then _ else _) _ 64
    split
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        symRead_uniform setup.source.crypto (.message message) state.table
    · trivial

/-- The three source classes charged by the uniform-query ledger. -/
def uniformClasses : Fin 3 → RootSpec.Domain → Prop := ![IsCoinRoot, IsTableRoot, IsDeriveRoot]

/-- Each source sampling class has its ordinary decidable predicate. -/
instance : ∀ i, DecidablePred (uniformClasses i) :=
  Fin.cases (inferInstanceAs (DecidablePred IsCoinRoot))
    (Fin.cases (inferInstanceAs (DecidablePred IsTableRoot))
      (Fin.cases (inferInstanceAs (DecidablePred IsDeriveRoot)) (fun i => Fin.elim0 i)))

/-- The symbolic interpreter retains the full source sampling budget and charges 64 draws for every possible table-domain request or derivation. -/
theorem symRun_uniform (setup : Setup baseSpec KemSK) {α : Type} (work : OracleComp RootSpec α)
    (u h d : Nat) (coins : work.IsQueryBoundP IsCoinRoot u) (table : work.IsQueryBoundP IsTableRoot h)
    (derive : work.IsQueryBoundP IsDeriveRoot d) (state : SymState) :
    ((simulateQ (symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) work).run state).IsQueryBoundP
      PqxdhJointGapDh.IsUniform (u + 64 * (h + d)) := by
  have counted := run_potential (symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) uniformClasses
    PqxdhJointGapDh.IsUniform (fun budget _ => budget 0 + 64 * (budget 1 + budget 2)) ?_
    work ![u, h, d] (by
      intro i
      fin_cases i
      · exact coins
      · exact table
      · exact derive) state
  · exact counted
  intro query initial budget positive
  have coin : IsCoinRoot query → 0 < budget 0 := positive 0
  have table : IsTableRoot query → 0 < budget 1 := positive 1
  have derive : IsDeriveRoot query → 0 < budget 2 := positive 2
  have decrease : rootUniformCost query +
      ((if IsCoinRoot query then budget 0 - 1 else budget 0) +
        64 * ((if IsTableRoot query then budget 1 - 1 else budget 1) +
          (if IsDeriveRoot query then budget 2 - 1 else budget 2))) ≤
      budget 0 + 64 * (budget 1 + budget 2) := by
    by_cases hc : IsCoinRoot query <;> by_cases ht : IsTableRoot query <;> by_cases hd : IsDeriveRoot query
    all_goals simp only [rootUniformCost, hc, ht, hd, ite_true, ite_false]
    all_goals simp only [hc, ht, hd, true_implies, false_implies] at coin table derive
    all_goals omega
  exact ⟨rootUniformCost query, symRoot_uniform setup query initial,
    (Nat.le_add_right _ _).trans decrease, fun _ _ => decrease⟩

/-- Each source request can add only its own kind of table entry; the extra real Expand call adds none. -/
theorem symRoot_growth (setup : Setup baseSpec KemSK) (query : RootSpec.Domain) (state : SymState)
    (result : RootSpec.Range query × SymState)
    (reached : result ∈ support (((symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run state)) :
    concreteCount result.2.table ≤ concreteCount state.table + (if IsTableRoot query then 1 else 0) ∧
    messageCount result.2.table ≤ messageCount state.table + (if IsDeriveRoot query then 1 else 0) := by
  rcases query with coin | (message | ⟨key, message⟩ | message)
  · change result ∈ support ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inl coin)) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>=
      fun value => pure (value, state)) at reached
    obtain ⟨_, _, rfl⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp [IsTableRoot, IsDeriveRoot]
  · change result ∈ support ((liftM (PqxdhJointGapDh.AdversarySpec.query (.inr (.sign message))) : OracleComp PqxdhJointGapDh.AdversarySpec _) >>=
      fun value => pure (value, { state with history := state.history ++
        [PqxdhJointDhExtractFamily.Observation.sign message value] })) at reached
    obtain ⟨_, _, rfl⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp [IsTableRoot, IsDeriveRoot]
  · simp only [QueryImpl.compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query] at reached
    change result ∈ support (if key = zeroSalt ∧ message.length = 192 then _ else _) at reached
    split at reached
    · rename_i inside
      obtain ⟨read, readReached, equal⟩ := (mem_support_bind_iff _ _ _).mp reached
      simp only [support_pure, Set.mem_singleton_iff] at equal
      subst result
      simpa [IsTableRoot, IsDeriveRoot, inside, SymKey.isConcrete] using
        symRead_growth setup.source.crypto (.concrete message) state.table read readReached
    · simp only [support_pure, Set.mem_singleton_iff] at reached
      subst result
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · rw [symRoot_derive] at reached
    split at reached
    · obtain ⟨read, readReached, equal⟩ := (mem_support_bind_iff _ _ _).mp reached
      simp only [support_pure, Set.mem_singleton_iff] at equal
      subst result
      simpa [IsTableRoot, IsDeriveRoot, SymKey.isConcrete] using
        symRead_growth setup.source.crypto (.message message) state.table read readReached
    · simp only [support_pure, Set.mem_singleton_iff] at reached
      subst result
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Remaining scan allowance with `h` table queries, `d` derives, and current concrete/message entry counts `c,m`. -/
def scanPotential (h d c m : Nat) : Nat := 2 * h * (m + d) + 2 * d * (c + h + m + d)

/-- The scan allowance is monotone in both current table counts. -/
theorem scanPotential_mono (h d c m c' m' : Nat) (concrete : c' ≤ c) (message : m' ≤ m) :
    scanPotential h d c' m' ≤ scanPotential h d c m := by
  unfold scanPotential
  gcongr

/-- A concrete query's scan and possible insertion fit within the remaining allowance. -/
theorem scanPotential_concrete (h d c m : Nat) :
    2 * m + scanPotential h d (c + 1) m ≤ scanPotential (h + 1) d c m := by
  unfold scanPotential
  nlinarith

/-- A message query's scan and possible insertion fit within the remaining allowance. -/
theorem scanPotential_message (h d c m : Nat) :
    (2 * c + m) + scanPotential h d c (m + 1) ≤ scanPotential h (d + 1) c m := by
  unfold scanPotential
  nlinarith

/-- The two source classes charged by the decision ledger. -/
def decisionClasses : Fin 2 → RootSpec.Domain → Prop := ![IsTableRoot, IsDeriveRoot]

/-- Both source decision classes have their ordinary decidable predicates. -/
instance : ∀ i, DecidablePred (decisionClasses i) :=
  Fin.cases (inferInstanceAs (DecidablePred IsTableRoot))
    (Fin.cases (inferInstanceAs (DecidablePred IsDeriveRoot)) (fun i => Fin.elim0 i))

/-- A complete source step pays its scan and leaves enough allowance for every possible continuation state. -/
theorem symRoot_potential (setup : Setup baseSpec KemSK) (query : RootSpec.Domain) (state : SymState)
    (h d : Nat) (tablePositive : IsTableRoot query → 0 < h) (derivePositive : IsDeriveRoot query → 0 < d) :
    rootDecisionCost query state ≤ scanPotential h d (concreteCount state.table) (messageCount state.table) ∧
    ∀ result ∈ support (((symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) query).run state),
      rootDecisionCost query state + scanPotential
        (if IsTableRoot query then h - 1 else h) (if IsDeriveRoot query then d - 1 else d)
        (concreteCount result.2.table) (messageCount result.2.table) ≤
          scanPotential h d (concreteCount state.table) (messageCount state.table) := by
  by_cases table : IsTableRoot query
  · have positive := tablePositive table
    have cost : rootDecisionCost query state = 2 * messageCount state.table := by
      rcases query with coin | (message | ⟨key, message⟩ | message)
      · cases table
      · cases table
      · simp [rootDecisionCost, show key = zeroSalt ∧ message.length = 192 from table]
      · cases table
    have notDerive : ¬ IsDeriveRoot query := by
      rcases query with coin | (message | ⟨key, message⟩ | message) <;>
        simp_all [IsTableRoot, IsDeriveRoot]
    have allowance := scanPotential_concrete (h - 1) d (concreteCount state.table) (messageCount state.table)
    rw [Nat.sub_add_cancel (by omega)] at allowance
    rw [cost]
    refine ⟨(Nat.le_add_right _ _).trans allowance, ?_⟩
    intro result reached
    have growth := symRoot_growth setup query state result reached
    simp only [table, notDerive, ite_true, ite_false, Nat.add_zero] at growth ⊢
    exact (Nat.add_le_add_left (scanPotential_mono (h - 1) d _ _ _ _ growth.1 growth.2) _).trans allowance
  · by_cases derive : IsDeriveRoot query
    · have positive := derivePositive derive
      have cost : rootDecisionCost query state = 2 * concreteCount state.table + messageCount state.table := by
        rcases query with coin | (message | ⟨key, message⟩ | message)
        · cases derive
        · cases derive
        · cases derive
        · rfl
      have allowance := scanPotential_message h (d - 1) (concreteCount state.table) (messageCount state.table)
      rw [Nat.sub_add_cancel (by omega)] at allowance
      rw [cost]
      refine ⟨(Nat.le_add_right _ _).trans allowance, ?_⟩
      intro result reached
      have growth := symRoot_growth setup query state result reached
      simp only [table, derive, ite_true, ite_false, Nat.add_zero] at growth ⊢
      exact (Nat.add_le_add_left (scanPotential_mono h (d - 1) _ _ _ _ growth.1 growth.2) _).trans allowance
    · have cost : rootDecisionCost query state = 0 := by
        rcases query with coin | (message | ⟨key, message⟩ | message)
        · rfl
        · rfl
        · exact ite_eq_right table
        · exact (derive trivial).elim
      rw [cost]
      refine ⟨Nat.zero_le _, ?_⟩
      intro result reached
      have growth := symRoot_growth setup query state result reached
      simp only [table, derive, ite_false, Nat.add_zero, Nat.zero_add] at growth ⊢
      exact scanPotential_mono h d _ _ _ _ growth.1 growth.2

/-- The potential pays every adaptive comparison, retaining all query-dependent table growth. -/
theorem symRun_decisions (setup : Setup baseSpec KemSK) {α : Type} (work : OracleComp RootSpec α)
    (h d : Nat) (table : work.IsQueryBoundP IsTableRoot h) (derive : work.IsQueryBoundP IsDeriveRoot d)
    (state : SymState) :
    ((simulateQ (symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) work).run state).IsQueryBoundP
      PqxdhJointGapDh.IsDecision (scanPotential h d (concreteCount state.table) (messageCount state.table)) := by
  exact run_potential (symImpl setup ∘ₛ PqxdhJointDhExtractRoot.reduction) decisionClasses
    PqxdhJointGapDh.IsDecision
    (fun budget current => scanPotential (budget 0) (budget 1) (concreteCount current.table) (messageCount current.table))
    (fun query initial budget positive => ⟨rootDecisionCost query initial, symRoot_decisions setup query initial,
      symRoot_potential setup query initial (budget 0) (budget 1) (positive 0) (positive 1)⟩)
    work ![h, d] (by intro i; fin_cases i; exact table; exact derive) state

/-- The adaptive scan client uses at most the declared quadratic decision allowance. `Q` counts every Server accept request, including rejection; the additional derive is the single-shot Beacon finish. -/
theorem scanClient_decisions (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH Q : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (accept : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsAcceptQuery Q)
    (publicValue : PublicChallenge) :
    (scanClient setup codec checks adversary qH publicValue).IsQueryBoundP PqxdhJointGapDh.IsDecision
      (2 * qH * (Q + 1) + 2 * (Q + 1) * (qH + Q + 1)) := by
  unfold scanClient
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  simpa [scanPotential, SymState.empty, concreteCount, messageCount, Nat.add_assoc] using
    symRun_decisions setup (PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue) qH (Q + 1)
      (body_table setup codec checks adversary qH rom none publicValue)
      (body_derive setup codec checks adversary Q accept none publicValue) SymState.empty

/-- The scan client retains the complete source-body uniform bill `u`, including Beacon generation, KEM implementation/base interpretation, ephemeral generation, CTX hashes and adversary coins. Each possible table read adds at most 64 draws. This is a conditional resource premise on that concrete body, never a free ambient computation. -/
theorem scanClient_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH Q u : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (accept : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsAcceptQuery Q)
    (publicValue : PublicChallenge)
    (coins : (PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue).IsQueryBoundP IsCoinRoot u) :
    (scanClient setup codec checks adversary qH publicValue).IsQueryBoundP PqxdhJointGapDh.IsUniform
      (u + 64 * (qH + Q + 1)) := by
  unfold scanClient
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  simpa only [Nat.add_assoc] using
    symRun_uniform setup (PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue) u qH (Q + 1)
      coins (body_table setup codec checks adversary qH rom none publicValue)
      (body_derive setup codec checks adversary Q accept none publicValue) SymState.empty

/-- The actual Gap-DH reduction used by `badB_le_gapDh` makes zero signing requests, pays the entire symbolic scan and at most `qH` final candidate decisions, and preserves the explicit source and table uniform bill. -/
theorem extractor_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH Q u : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (accept : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsAcceptQuery Q)
    (publicValue : PublicChallenge)
    (coins : (PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue).IsQueryBoundP IsCoinRoot u) :
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
        PqxdhJointGapDh.IsSigning 0 ∧
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
        PqxdhJointGapDh.IsDecision (2 * qH * (Q + 1) + 2 * (Q + 1) * (qH + Q + 1) + qH) ∧
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
        PqxdhJointGapDh.IsUniform (u + 64 * (qH + Q + 1)) :=
  ⟨PqxdhJointGapDh.extractor_signing _ publicValue 0 (scanClient_signing setup codec checks adversary qH publicValue),
    PqxdhJointGapDh.extractor_class_bound _ publicValue _ _
      (scanClient_decisions setup codec checks adversary qH Q rom accept publicValue),
    PqxdhJointGapDh.extractor_uniform _ publicValue _
      (scanClient_uniform setup codec checks adversary qH Q u rom accept publicValue coins)⟩

/-- The ordinary Gap-DH game additionally charges its own 32-byte Server identity seed and 32-byte Beacon prekey sample. -/
theorem extractor_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qH Q u : Nat)
    (rom : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsRomQuery qH)
    (accept : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthExperiment.IsAcceptQuery Q)
    (coins : ∀ publicValue,
      (PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue).IsQueryBoundP IsCoinRoot u) :
    (PqxdhJointGapDh.game setup.joint setup.dh
      (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).IsTotalQueryBound
        (64 + (u + 64 * (qH + Q + 1))) :=
  PqxdhJointGapDh.extractor_game_uniform setup.joint setup.dh (scanClient setup codec checks adversary qH) _
    (fun publicValue => scanClient_uniform setup codec checks adversary qH Q u rom accept publicValue (coins publicValue))

end BeaconcryptCore.Computational.PqxdhServerAuthGapDh

/-! ## Checked theorem dependencies -/

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.service_fst' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.service_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.answer_coins' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.answer_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.answer_decision' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.answer_decision

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.read_second' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.read_second

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.read_fourth' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.read_fourth

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.read_kem' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.read_kem

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.assemble_inj' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.assemble_inj

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.serverCoordinate_some_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.serverCoordinate_some_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.testServer_answer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.testServer_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.input_known' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.input_known

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.input_selected' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.input_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.concreteTest_answer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.concreteTest_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.thirdSame_answer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.thirdSame_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.messageSame_answer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.messageSame_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symSame_answer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symSame_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symLookup_answer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symLookup_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symCache_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symCache_append

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_answer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symAccepts_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symAccepts_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_concretize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_concretize

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.sym_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.sym_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.sym_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.sym_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.concretize_empty' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.concretize_empty

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_answer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_answer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.candidate_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.candidate_game

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.candHit_eq_gapDh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.candHit_eq_gapDh

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.sign_public' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.sign_public

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.table_public' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.table_public

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_get

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_set

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_modify

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.familyCoins_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.familyCoins_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_liftCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_liftCoins

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_forward

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.forward_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.forward_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_record

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.client_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.client_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.session_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.session_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_session

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_build

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.tail_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.tail_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_onCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_onCtx

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_stage

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.quiet_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.honest_no_rom_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.honest_no_rom_public

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.romMessage_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.romMessage_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.tableMessage_quiet' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.tableMessage_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.rom_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.rom_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.rom_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.rom_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.accept_touches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.accept_touches

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.build_touches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.build_touches

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.finish_touches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.finish_touches

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.adversary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.adversary_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.fused_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.fused_run

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.fused_lockstep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.fused_lockstep

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.fused_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.fused_count

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.gameState_fused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.gameState_fused

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.touches_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.touches_history

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.adversary_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.adversary_count

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.romCandidates_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.romCandidates_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.candidates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.candidates_length

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.mem_padded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.mem_padded

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.firstBeacon_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.firstBeacon_mem

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.badB_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.badB_candidate

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.badB_le_gapDh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.badB_le_gapDh

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.run_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.run_potential

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.derive_family' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.derive_family

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_seq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_seq

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_get

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_set

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_modify

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.familyCoins_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.familyCoins_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_liftCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_liftCoins

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_forward

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_record

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_onCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.costs_onCtx

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.client_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.client_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.session_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.session_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.accept_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.accept_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.build_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.build_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.tail_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.tail_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_costs_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.stage_costs_step

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.initSentFlag_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.initSentFlag_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.initSentFlag_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.initSentFlag_le

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.finish_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.finish_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.familyCoins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.familyCoins_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.hmac_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.hmac_run

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.hmac_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.hmac_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.hash_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.hash_costs

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_sign

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_table

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.body_derive

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_pure' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_decision

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_testServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_testServer

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_concreteTest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_concreteTest

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_thirdSame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_thirdSame

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_messageSame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_messageSame

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_symSame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_symSame

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_symLookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.decides_symLookup

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.lookupCost_concrete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.lookupCost_concrete

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.lookupCost_message' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.lookupCost_message

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symCoins_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symCoins_excludes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symCoins_excludes

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_decisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_decisions

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_signing

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_table

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRead_growth

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_derive

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_decisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_decisions

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_signing

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_signing

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRun_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRun_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_growth

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanPotential_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanPotential_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanPotential_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanPotential_concrete

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanPotential_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanPotential_message

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRoot_potential

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRun_decisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.symRun_decisions

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_decisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_decisions

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.scanClient_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.extractor_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.extractor_resources

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthGapDh.extractor_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthGapDh.extractor_game_uniform
