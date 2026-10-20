import BeaconcryptCore.Computational.PqxdhOptionalKemSourceQueryBounds

/-!
# Joint Ed25519 / converted X25519 identity endpoint

One uniformly generated 32-byte Ed25519 seed determines both public keys, every signature, and every converted-static-DH reply. The adversary may request signatures and DH at arbitrary typed 32-byte peer encodings; malformed/invalid-point rejection is retained as an optional reply. A public functional alias law can relate encodings without asserting constructor injectivity.

The endpoint winning event is ordinary weak-EUF message freshness and valid signature verification. The DH auxiliary interface makes its security assumption stronger than plain Ed25519 EUF-CMA. No protocol-authentication event or primitive implementation proof appears in the endpoint. Identity reveals belong to the later global wrapper and its explicit target freshness rule.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointIdentity

open PqxdhEd25519EufCma

abbrev IdentitySeed := List.Vector UInt8 32
abbrev PeerEncoding := List.Vector UInt8 32
abbrev DhOutput := List.Vector UInt8 32

/-- Correlated public values from the same seed; their byte representations remain exact. -/
structure PublicIdentity where
  ed25519 : Ed25519PublicKey
  convertedX25519 : X25519PublicKey
  deriving DecidableEq

/-- Ordinary deterministic primitive operations. Optional DH includes validation and all required rejection checks. -/
structure Primitives where
  publicKeys : IdentitySeed → PublicIdentity
  sign : IdentitySeed → Pqxdh.Bytes → Ed25519Signature
  verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool
  staticDh : IdentitySeed → PeerEncoding → Option DhOutput

/-- Exact public peer equivalence is supplied by the primitive functional interface; the game does not use injectivity or block any target DH class. -/
structure PeerEquivalence (primitives : Primitives) where
  same : PeerEncoding → PeerEncoding → Prop
  decidable : DecidableRel same
  equivalence : Equivalence same
  replies : ∀ seed left right, same left right →
    primitives.staticDh seed left = primitives.staticDh seed right

/-- A seed is sampled as 32 independent uniform bytes, with its full sampling cost retained. -/
def sampleSeed : ProbComp IdentitySeed := $ᵗ IdentitySeed

inductive Query where
  | sign (message : Pqxdh.Bytes)
  | staticDh (peer : PeerEncoding)

/-- Signatures and optional DH outputs are distinct oracle result types. -/
def JointSpec : OracleSpec Query
  | .sign _ => Ed25519Signature
  | .staticDh _ => Option DhOutput

abbrev AdversarySpec := unifSpec + JointSpec

/-- Preserve exact interleaving, input bytes, and replies, including failed static-DH requests. -/
inductive Event where
  | signed (message : Pqxdh.Bytes) (signature : Ed25519Signature)
  | staticDh (peer : PeerEncoding) (reply : Option DhOutput)
  deriving DecidableEq

abbrev History := List Event

/-- The message log records every signing request; a different signature on the same message is not a weak-EUF win. -/
def signedMessages (history : History) : List Pqxdh.Bytes :=
  history.filterMap fun event => match event with
    | .signed message _ => some message
    | .staticDh _ _ => none

/-- Actual primitive reply at an exact typed request. -/
def primitiveReply (primitives : Primitives) (seed : IdentitySeed) :
    (query : JointSpec.Domain) → JointSpec.Range query
  | .sign message => primitives.sign seed message
  | .staticDh peer => primitives.staticDh seed peer

/-- Preserve the full request and returned answer in chronological source order. -/
def requestEvent : (query : JointSpec.Domain) → JointSpec.Range query → Event
  | .sign message, signature => .signed message signature
  | .staticDh peer, reply => .staticDh peer reply

/-- The private seed appears only in the challenger interpreter. -/
def jointImpl (primitives : Primitives) (seed : IdentitySeed) :
    QueryImpl AdversarySpec (StateT History ProbComp) := fun query history =>
  match query with
  | .inl coin => do
    let answer ← unifSpec.query coin
    pure (answer, history)
  | .inr request =>
    let answer := primitiveReply primitives seed request
    pure (answer, history ++ [requestEvent request answer])

/-- Ordinary detached weak-EUF output, without any protocol transcript or authentication predicate. -/
structure Forgery where
  message : Pqxdh.Bytes
  signature : Ed25519Signature

/-- Complete source-shaped adversarial execution, with seed-derived joint public values and retained history. -/
def run (primitives : Primitives) (seed : IdentitySeed) {Result : Type}
    (adversary : PublicIdentity → OracleComp AdversarySpec Result) : ProbComp (Result × History) :=
  (simulateQ (jointImpl primitives seed) (adversary (primitives.publicKeys seed))).run []

/-- The only winning conditions are fresh message and valid signature under the generated Ed25519 key. -/
def wins (primitives : Primitives) (jointPublic : PublicIdentity) (forgery : Forgery)
    (history : History) : Bool :=
  primitives.verify jointPublic.ed25519 forgery.message forgery.signature &&
    !decide (forgery.message ∈ signedMessages history)

/-- Joint-use weak-EUF experiment; the static-DH service is an explicit auxiliary capability. -/
def game (primitives : Primitives)
    (adversary : PublicIdentity → OracleComp AdversarySpec Forgery) : ProbComp Bool := do
  let seed ← sampleSeed
  let (forgery, history) ← run primitives seed adversary
  pure (wins primitives (primitives.publicKeys seed) forgery history)

noncomputable def advantage (primitives : Primitives)
    (adversary : PublicIdentity → OracleComp AdversarySpec Forgery) : ℝ≥0∞ :=
  Pr{let x ← game primitives adversary}[x = true]

/-- Equivalent valid encodings have the same optional DH reply while both exact raw requests remain recorded. -/
theorem equivalent_peer_reply (primitives : Primitives) (aliases : PeerEquivalence primitives)
    (seed : IdentitySeed) (left right : PeerEncoding) (same : aliases.same left right) :
    primitives.staticDh seed left = primitives.staticDh seed right :=
  aliases.replies seed left right same

/-- The seed sampler accounts for all 32 independent byte draws. -/
theorem sampleSeed_uniform_bound : sampleSeed.IsTotalQueryBound 32 :=
  CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

/-- The optional typed view of the byte model's static DH, retaining all-zero rejection. -/
def sourceDhReply (c : Pqxdh.Crypto) (secret : Pqxdh.Bytes) (peer : PeerEncoding) : Option DhOutput :=
  let output : DhOutput := ⟨c.x25519 (c.xsk secret) peer.toList, c.x25519_length _ _⟩
  if output.toList = Pqxdh.zero32 then none else some output

/-- Functional adapter contract: one native Ed25519 secret representation is derived from the sampled seed and used consistently by both primitive interfaces. -/
structure SourceWiring (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) : Prop where
  edPublic : ∀ seed, (primitives.publicKeys seed).ed25519.toList = c.edPub (secretOfSeed seed).toList
  xPublic : ∀ seed, (primitives.publicKeys seed).convertedX25519.toList =
    c.xpub (c.xsk (secretOfSeed seed).toList)
  attachedSign : ∀ seed message, attachSignature (primitives.sign seed message) message =
    c.sign (secretOfSeed seed).toList message
  verifyAttached : ∀ publicKey message signature,
    c.verify publicKey.toList (attachSignature signature message) =
      if primitives.verify publicKey message signature then some message else none
  staticDh : ∀ seed peer, primitives.staticDh seed peer = sourceDhReply c (secretOfSeed seed).toList peer

/-- The exposed X25519 public value is exactly the public conversion of the exposed Ed25519 key, not an independently sampled key. -/
theorem jointPublic_conversion (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (seed : IdentitySeed) :
    c.xpkConv (primitives.publicKeys seed).ed25519.toList =
      some (primitives.publicKeys seed).convertedX25519.toList := by
  rw [wiring.edPublic, wiring.xPublic, c.conv_agree]

/-- A successful auxiliary reply is the exact source DH byte string, with no uniform-output assumption. -/
theorem sourceDhReply_some (c : Pqxdh.Crypto) (secret : Pqxdh.Bytes)
    (peer : PeerEncoding) (reply : DhOutput)
    (accepted : sourceDhReply c secret peer = some reply) :
    c.x25519 (c.xsk secret) peer.toList = reply.toList := by
  dsimp only [sourceDhReply] at accepted
  split at accepted
  · contradiction
  · exact congrArg List.Vector.toList (Option.some.inj accepted)

/-- Reconstruct the server's exact four-DH tuple from one static auxiliary reply and its locally known ephemeral. -/
def serverDhsFromAux (c : Pqxdh.Crypto) (ephemeral convertedBeacon prekey oneTime : Pqxdh.Bytes)
    (reply : DhOutput) : Pqxdh.Bytes × Pqxdh.Bytes × Pqxdh.Bytes × Pqxdh.Bytes :=
  (reply.toList, c.x25519 ephemeral convertedBeacon, c.x25519 ephemeral prekey, c.x25519 ephemeral oneTime)

/-- Reconstruct the beacon's exact four-DH tuple from one static auxiliary reply and locally retained prekey/one-time secrets. -/
def beaconDhsFromAux (c : Pqxdh.Crypto) (prekeySecret oneTimeSecret convertedServer ephemeral : Pqxdh.Bytes)
    (reply : DhOutput) : Pqxdh.Bytes × Pqxdh.Bytes × Pqxdh.Bytes × Pqxdh.Bytes :=
  (c.x25519 prekeySecret convertedServer, reply.toList, c.x25519 prekeySecret ephemeral,
    c.x25519 oneTimeSecret ephemeral)

/-- The source server's seed-dependent DH coordinate is supplied by one exact auxiliary request. -/
theorem serverDhsFromAux_eq (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (seed : IdentitySeed) (ephemeral convertedBeacon oneTime : Pqxdh.Bytes)
    (prekey : PeerEncoding) (reply : DhOutput) (accepted : primitives.staticDh seed prekey = some reply) :
    serverDhsFromAux c ephemeral convertedBeacon prekey.toList oneTime reply =
      Pqxdh.serverDHs c (secretOfSeed seed).toList ephemeral convertedBeacon prekey.toList oneTime := by
  rw [wiring.staticDh] at accepted
  simp only [serverDhsFromAux, Pqxdh.serverDHs, sourceDhReply_some c _ _ _ accepted]

/-- The source beacon's seed-dependent DH coordinate is supplied by one exact auxiliary request. -/
theorem beaconDhsFromAux_eq (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (seed : IdentitySeed) (prekeySecret oneTimeSecret convertedServer : Pqxdh.Bytes)
    (ephemeral : PeerEncoding) (reply : DhOutput) (accepted : primitives.staticDh seed ephemeral = some reply) :
    beaconDhsFromAux c prekeySecret oneTimeSecret convertedServer ephemeral.toList reply =
      Pqxdh.beaconDHs c (secretOfSeed seed).toList prekeySecret oneTimeSecret convertedServer ephemeral.toList := by
  rw [wiring.staticDh] at accepted
  simp only [beaconDhsFromAux, Pqxdh.beaconDHs, sourceDhReply_some c _ _ _ accepted]

/-- The auxiliary primitive request preserves every subsequent adaptive computation and the exact accumulated history. -/
theorem primitive_query_complete_continuation (primitives : Primitives) (seed : IdentitySeed)
    (history : History) (request : JointSpec.Domain) {Result : Type}
    (next : JointSpec.Range request → OracleComp AdversarySpec Result) :
    (simulateQ (jointImpl primitives seed) (do
      let answer ← AdversarySpec.query (.inr request)
      next answer)).run history =
    (simulateQ (jointImpl primitives seed) (next (primitiveReply primitives seed request))).run
      (history ++ [requestEvent request (primitiveReply primitives seed request)]) := by
  simp only [simulateQ_query_bind, StateT.run_bind]
  change (pure (primitiveReply primitives seed request, history ++ [requestEvent request (primitiveReply primitives seed request)]) >>= _) = _
  simp

end BeaconcryptCore.Computational.PqxdhJointIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentity.serverDhsFromAux_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentity.serverDhsFromAux_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentity.primitive_query_complete_continuation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentity.primitive_query_complete_continuation
