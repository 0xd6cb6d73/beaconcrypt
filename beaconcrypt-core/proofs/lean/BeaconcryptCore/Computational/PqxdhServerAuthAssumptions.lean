import BeaconcryptCore.Computational.PqxdhJointGapDh
import BeaconcryptCore.Model.Pqxdh.ResponseEncodingAlias

/-!
# Server authentication: the X25519 class law and the Gap-DH term

This module collects the functional primitive contracts and the hardness term that the Server-authentication proof (Milestone B, route R1) adds to the development. It states no protocol property and declares no new Lean axioms. `X25519ScalarSpread` and `NonzeroHonestDh` are two further functional contracts approved on 2026-09-30: the first bounds how many scalars give one nonzero DH value for a fixed peer and is used for the session-collision term, the second says honest DH values are never zero and is used only by the negative controls. The contract is a `Prop` that later theorems take as an explicit premise, and the hardness term is the advantage of an adversary in an existing game.

`X25519ClassLaw` is a functional contract on the abstract X25519 function of `Pqxdh.Crypto`, of the same kind as `Pqxdh.Crypto.dh_comm` but kept as a separate premise rather than a new field, so no existing theorem gains a premise: if two peer inputs give the same output under one scalar, they give the same output under every scalar, which is `Pqxdh.ResponseEncodingAlias.SameDhReplies`. It is plausible for clamped X25519 as specified in RFC 7748, because equal nonzero outputs under one clamped scalar imply that the two peers agree up to negation and a small-order torsion point, equal zero outputs imply that both peers have small order, and in both cases every clamped scalar maps the two peers to the same output.

The consequences proved here let a reduction that holds neither the Server seed nor the Beacon's prekey scalar compare DH values computed with those secrets. `class_iff` states the law as an equivalence between any two scalars. `static_iff` decides whether two peers give the same Server static DH by evaluating both peers under any one scalar the reduction holds, and `scalar_iff` does the same for the Beacon's prekey scalar. `classEquivalence` packages `static_iff` as an instance of the existing `PqxdhJointIdentity.PeerEquivalence`. `scalar_agreement` restates `Pqxdh.Crypto.dh_comm` for the optional typed interface `PqxdhJointGapDh.sourceInterface`, which `PqxdhJointGapDh.DhInterface` does not state.

`serverGapDhAdvantage` is the advantage in the existing game `PqxdhJointGapDh.game`, instantiated with `PqxdhJointGapDh.sourceInterface`. It is the Gap-DH term of the Server-authentication bound, in the form of anchored two-sided strong CDH for libsodium's X25519 function treated as a black box, with decision services on every 32-byte input the function accepts, including points of the quadratic twist; this strengthens textbook Gap-DH, and its plausibility rests on Signal's Gap-DH assumption and on the twist security of Curve25519 (Bernstein, PKC 2006; RFC 7748). No new hardness game is defined. `honest_accepts` shows that the game counts a guess `some value` as a win exactly when `value` is the Beacon's honestly computed DH1, `honest_candidate` gives the success condition of `PqxdhJointGapDh.candidateGame` from the Beacon's DH1, and `candidate_eq_serverGapDh` restates the existing candidate-scan equality for this instance.

The only premises are `X25519ClassLaw` where it is named and the functional adapter contract `PqxdhJointIdentity.SourceWiring`. Messages are abstract byte strings that each side can decode; no serialization-library behaviour and no internal property of libsodium is used.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthAssumptions
open PqxdhJointIdentity PqxdhJointGapDh

/-- X25519 class law, a functional contract on the abstract X25519 function of the same kind as `Pqxdh.Crypto.dh_comm`, used only as an explicit premise: if two peer inputs give the same output under one scalar, they give the same output under every scalar. Plausibility: for clamped X25519 as specified in RFC 7748, equal nonzero outputs under one scalar imply that the two peers agree up to negation and a small-order torsion point, equal zero outputs imply that both peers have small order, and in both cases every clamped scalar maps the two peers to the same output. The law quantifies over byte strings of every length because the abstract function does; production calls X25519 only on 32-byte arrays, and a model can meet the law on other lengths by normalizing its inputs. -/
def X25519ClassLaw (c : Pqxdh.Crypto) : Prop :=
  ∀ a left right, c.x25519 a left = c.x25519 a right →
    Pqxdh.ResponseEncodingAlias.SameDhReplies c left right

/-- X25519 scalar spread, a functional contract on the abstract X25519 function used only as an explicit premise: for a fixed peer, a nonzero output is produced by at most 64 of the 32-byte scalar strings. Plausibility: if the peer has small order every clamped output is zero, which the contract excludes; otherwise a clamped scalar is 2^254 + 8m with m below 2^251, which is below the large prime subgroup orders of the curve and the twist, so m determines the point and a nonzero u-coordinate comes from at most two points and hence at most two clamped scalars; clamping ignores five bits, which gives at most 64 strings (RFC 7748; Bernstein, PKC 2006). It bounds the chance that two independent honest scalars give the same DH value. -/
def X25519ScalarSpread (c : Pqxdh.Crypto) : Prop :=
  ∀ (peer : PeerEncoding) (value : DhOutput), value ≠ zeroDh →
    (Finset.univ.filter fun scalar : ScalarBytes => c.x25519 scalar.toList peer.toList = value.toList).card ≤ 64

/-- Nonzero honest DH, a functional contract on the abstract X25519 function used only as an explicit premise of the negative controls: X25519 of any scalar with an honestly generated public key is never the all-zero string. Plausibility: an honest public key has the large prime order of the curve's base-point subgroup, and no clamped scalar is a multiple of that order (RFC 7748); the existing model states the same fact as the side condition `HonestRun.Ok`. -/
def NonzeroHonestDh (c : Pqxdh.Crypto) : Prop := ∀ a b, c.x25519 a (c.xpub b) ≠ Pqxdh.zero32

/-- Under the class law, two peers give equal outputs under one scalar exactly when they do under any other scalar. -/
theorem class_iff (c : Pqxdh.Crypto) (law : X25519ClassLaw c) (a b left right : Pqxdh.Bytes) :
    c.x25519 a left = c.x25519 a right ↔ c.x25519 b left = c.x25519 b right :=
  ⟨fun same => law a left right same b, fun same => law b left right same a⟩

/-- The optional typed view shared by `sourceScalarDh` and `sourceDhReply` determines the raw 32-byte output, including the rejected all-zero case. -/
theorem optional_inj (x y : Pqxdh.Bytes) (hx : x.length = 32) (hy : y.length = 32)
    (same : (if x = Pqxdh.zero32 then (none : Option DhOutput) else some ⟨x, hx⟩) =
      (if y = Pqxdh.zero32 then none else some ⟨y, hy⟩)) : x = y := by
  by_cases zx : x = Pqxdh.zero32 <;> by_cases zy : y = Pqxdh.zero32
  · exact zx.trans zy.symm
  · simp [zx, zy] at same
  · simp [zx, zy] at same
  · simp only [zx, zy, ↓reduceIte] at same
    exact congrArg (fun value : DhOutput => value.toList) (Option.some.inj same)

/-- Equal raw 32-byte outputs give equal optional typed views. -/
theorem optional_congr (x y : Pqxdh.Bytes) (hx : x.length = 32) (hy : y.length = 32) (same : x = y) :
    (if x = Pqxdh.zero32 then (none : Option DhOutput) else some ⟨x, hx⟩) =
      (if y = Pqxdh.zero32 then none else some ⟨y, hy⟩) := by
  subst same
  rfl

/-- Two optional scalar DH results agree exactly when the raw X25519 outputs agree. -/
theorem sourceScalarDh_eq_iff (c : Pqxdh.Crypto) (a : ScalarBytes) (left right : PeerEncoding) :
    sourceScalarDh c a left = sourceScalarDh c a right ↔
      c.x25519 a.toList left.toList = c.x25519 a.toList right.toList := by
  constructor
  · intro same
    exact optional_inj _ _ (c.x25519_length _ _) (c.x25519_length _ _) same
  · intro same
    unfold sourceScalarDh
    exact optional_congr _ _ _ _ same

/-- Two optional converted-static DH results agree exactly when the raw X25519 outputs agree. -/
theorem sourceDhReply_eq_iff (c : Pqxdh.Crypto) (secret : Pqxdh.Bytes) (left right : PeerEncoding) :
    sourceDhReply c secret left = sourceDhReply c secret right ↔
      c.x25519 (c.xsk secret) left.toList = c.x25519 (c.xsk secret) right.toList := by
  constructor
  · intro same
    exact optional_inj _ _ (c.x25519_length _ _) (c.x25519_length _ _) same
  · intro same
    unfold sourceDhReply
    exact optional_congr _ _ _ _ same

/-- Evaluating both peers under one scalar the reduction holds decides whether they give the same Server static DH, whose seed the reduction does not hold. -/
theorem static_iff (c : Pqxdh.Crypto) (law : X25519ClassLaw c) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (a : ScalarBytes) (left right : PeerEncoding) (seed : IdentitySeed) :
    joint.staticDh seed left = joint.staticDh seed right ↔
      sourceScalarDh c a left = sourceScalarDh c a right := by
  rw [wiring.staticDh, wiring.staticDh, sourceDhReply_eq_iff, sourceScalarDh_eq_iff]
  exact class_iff c law _ _ _ _

/-- Evaluating both peers under one scalar the reduction holds decides whether they give the same DH under another scalar, such as the Beacon's prekey scalar, which the reduction does not hold. -/
theorem scalar_iff (c : Pqxdh.Crypto) (law : X25519ClassLaw c) (a b : ScalarBytes)
    (left right : PeerEncoding) :
    sourceScalarDh c b left = sourceScalarDh c b right ↔
      sourceScalarDh c a left = sourceScalarDh c a right := by
  rw [sourceScalarDh_eq_iff, sourceScalarDh_eq_iff]
  exact class_iff c law _ _ _ _

/-- The existing `PeerEquivalence` interface, inhabited by the class law with any fixed reference scalar: two peers are equivalent when they give the same optional DH under that scalar. -/
def classEquivalence (c : Pqxdh.Crypto) (law : X25519ClassLaw c) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (reference : ScalarBytes) : PeerEquivalence joint where
  same left right := sourceScalarDh c reference left = sourceScalarDh c reference right
  decidable := fun _ _ => inferInstance
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun same other => same.trans other⟩
  replies := fun seed left right same =>
    (static_iff c law joint secretOfSeed wiring reference left right seed).mpr same

/-- Scalar-scalar agreement for the optional typed interface, from `Pqxdh.Crypto.dh_comm`; `DhInterface` itself states only the converted-static agreement. -/
theorem scalar_agreement (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (a b : ScalarBytes) :
    (sourceInterface c joint secretOfSeed wiring).dh a
        ((sourceInterface c joint secretOfSeed wiring).publicKey b) =
      (sourceInterface c joint secretOfSeed wiring).dh b
        ((sourceInterface c joint secretOfSeed wiring).publicKey a) := by
  change sourceScalarDh c a ⟨c.xpub b.toList, c.xpub_length _⟩ =
    sourceScalarDh c b ⟨c.xpub a.toList, c.xpub_length _⟩
  unfold sourceScalarDh
  exact optional_congr _ _ _ _ (c.dh_comm a.toList b.toList)

/-- An optional scalar DH result that is present is never the all-zero value, because the typed view rejects it. -/
theorem sourceScalarDh_nonzero (c : Pqxdh.Crypto) (a : ScalarBytes) (peer : PeerEncoding)
    (value : DhOutput) (accepted : sourceScalarDh c a peer = some value) : value ≠ zeroDh := by
  dsimp only [sourceScalarDh] at accepted
  split at accepted
  · contradiction
  · rename_i nonzero
    intro zero
    subst zero
    exact nonzero ((congrArg List.Vector.toList (Option.some.inj accepted)).trans rfl)

/-- The Gap-DH game on the byte-model interface counts a guess `some value` as a win exactly when `value` is the Beacon's honestly computed DH1, the prekey scalar's optional DH with the Server's converted public key. -/
theorem honest_accepts (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (value : DhOutput) :
    PqxdhJointGapDh.wins
        (joint.staticDh seed ((sourceInterface c joint secretOfSeed wiring).publicKey scalar)) (some value) =
        true ↔
      sourceScalarDh c scalar (joint.publicKeys seed).convertedX25519 = some value := by
  rw [(sourceInterface c joint secretOfSeed wiring).agreement seed scalar]
  change decide (value ≠ zeroDh ∧ sourceScalarDh c scalar (joint.publicKeys seed).convertedX25519 = some value) =
    true ↔ _
  constructor
  · intro won
    exact (of_decide_eq_true won).2
  · intro honest
    exact decide_eq_true ⟨sourceScalarDh_nonzero c scalar _ value honest, honest⟩

/-- If the Beacon's honestly computed DH1 is among the candidates, the success condition of `PqxdhJointGapDh.candidateGame` holds for the byte-model interface. -/
theorem honest_candidate (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (value : DhOutput) (candidates : List DhOutput)
    (honest : sourceScalarDh c scalar (joint.publicKeys seed).convertedX25519 = some value)
    (mem : value ∈ candidates) :
    ∃ target, joint.staticDh seed ((sourceInterface c joint secretOfSeed wiring).publicKey scalar) = some target ∧
      target ≠ zeroDh ∧ target ∈ candidates :=
  ⟨value, ((sourceInterface c joint secretOfSeed wiring).agreement seed scalar).trans honest,
    sourceScalarDh_nonzero c scalar _ value honest, mem⟩

/-- Gap-DH term of the Server-authentication bound: the advantage of `adversary` in the existing game `PqxdhJointGapDh.game`, instantiated with the byte-model X25519 interface `PqxdhJointGapDh.sourceInterface`; no new game is defined. The assumption is a Gap-DH-type assumption, anchored two-sided strong CDH, for libsodium's X25519 function treated as a black box over 32-byte strings. The game samples a uniform 32-byte Ed25519 seed for the Server, whose converted X25519 secret is one anchor, and a uniform 32-byte X25519 scalar for the Beacon's prekey, which is the other anchor. It publishes the Server's public identity and the prekey, provides Ed25519 signatures under the Server seed, and provides one decision service per anchor, which answers whether a supplied candidate equals the function's output at that anchor and a chosen peer, on every 32-byte input the function accepts. The adversary wins by returning the nonzero cross value, the function's output at the Server's converted secret and the prekey. Plausibility: Signal's PQXDH specification assumes Gap-DH on Curve25519; gap problems are due to Okamoto and Pointcheval (PKC 2001), and each decision service is a strong-DH oracle in the sense of Abdalla, Bellare and Rogaway (CT-RSA 2001). It is a separate assumption on this game, and this module does not claim that textbook Gap-DH implies it. The decision services answer on every 32-byte input the function accepts, which includes points of the quadratic twist under the same clamped scalar, so the assumption strengthens textbook Gap-DH rather than following from it; this is plausible because Curve25519 was chosen so that its twist is also secure (its large twist subgroup has prime order about 2^253, and clamping removes the small subgroups of the curve and the twist), see Bernstein (PKC 2006) and RFC 7748. -/
noncomputable def serverGapDhAdvantage (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (adversary : PublicChallenge → OracleComp PqxdhJointGapDh.AdversarySpec (Option DhOutput)) : ℝ≥0∞ :=
  PqxdhJointGapDh.advantage joint (sourceInterface c joint secretOfSeed wiring) adversary

/-- `serverGapDhAdvantage` is the success probability of the existing game on the byte-model interface. -/
theorem serverGapDhAdvantage_eq (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (adversary : PublicChallenge → OracleComp PqxdhJointGapDh.AdversarySpec (Option DhOutput)) :
    serverGapDhAdvantage c joint secretOfSeed wiring adversary =
      Pr{let x ← PqxdhJointGapDh.game joint (sourceInterface c joint secretOfSeed wiring) adversary}[x = true] :=
  rfl

/-- The success probability of a candidate client on the byte-model interface equals the Gap-DH term of its executable scanning extractor, with no guessing factor. -/
theorem candidate_eq_serverGapDh {count : Nat} (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (client : PublicChallenge → OracleComp PqxdhJointGapDh.AdversarySpec (List.Vector DhOutput count)) :
    Pr{let x ← candidateGame joint (sourceInterface c joint secretOfSeed wiring) client}[x = true] =
      serverGapDhAdvantage c joint secretOfSeed wiring (extractor client) :=
  candidate_success_eq_advantage joint (sourceInterface c joint secretOfSeed wiring) client

end BeaconcryptCore.Computational.PqxdhServerAuthAssumptions

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.class_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.class_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.optional_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.optional_inj

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.optional_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.optional_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.sourceScalarDh_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.sourceScalarDh_eq_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.sourceDhReply_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.sourceDhReply_eq_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.static_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.static_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.scalar_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.scalar_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.classEquivalence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.classEquivalence

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.scalar_agreement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.scalar_agreement

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.sourceScalarDh_nonzero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.sourceScalarDh_nonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.honest_accepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.honest_accepts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.honest_candidate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.honest_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.serverGapDhAdvantage_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.serverGapDhAdvantage_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.candidate_eq_serverGapDh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthAssumptions.candidate_eq_serverGapDh
