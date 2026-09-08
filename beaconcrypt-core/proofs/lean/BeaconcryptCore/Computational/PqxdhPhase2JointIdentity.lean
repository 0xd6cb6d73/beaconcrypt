import BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds

/-!
The selected generated Beacon retains only its original joint-identity index and public identity when converting its private identity handle. Static DH is requested through the existing source service at the original callback point. No executable definition receives an identity seed, converted secret bytes, or target KEM secret. Missing identities and rejected DH replies retain the complete original source transcript and signing/DH/reveal history.

The realization uses the existing joint source wiring, including its optional all-zero DH rejection. The model's private conversion is total; an optional native conversion must separately satisfy that representation contract for a reached generated identity. These laws do not prove native library correctness, physical erasure, freshness, or a completed Phase2 scheduler. Live disclosures retain the existing source behavior; storage and restoration are outside scope.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2JointIdentity
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting
open PqxdhPhase1AcceptanceOracle PqxdhJointPhase1AcceptanceComposition
open PqxdhPrivateKemQueryBounds PqxdhPrivateKemSource
open PqxdhJointIdentityFamily PqxdhJointPhase1Reports

/-- Private provenance, with no seed or converted scalar field. -/
structure Converted where
  index : Nat
  publicIdentity : PublicIdentity

/-- Source private conversion keeps the original handle inside the trusted compiler. -/
def convert (index : Nat) (publicIdentity : PublicIdentity) : OracleComp SourceSpec (Option Converted) :=
  pure (some ⟨index, publicIdentity⟩)

def request (handle : Converted) (peer : PeerEncoding) : DynamicSpec.Domain :=
  .inr (.service handle.index (.staticDh peer))

/-- Flatten the dynamic service's missing-index Option and its actual optional DH reply. -/
def staticDh (handle : Converted) (peer : PeerEncoding) : OracleComp SourceSpec (Option DhOutput) := do
  let reply ← SourceSpec.query (.inl (request handle peer))
  pure reply.join

/-- Exact source bookkeeping, including an unavailable identity and a rejected scalar multiplication. -/
def afterDh {count : Nat} (handle : Converted) (peer : PeerEncoding)
    (reply : Option (Option DhOutput)) (state : BareState count) : BareState count :=
  (historyUpdate count (request handle peer) reply state.1,
   record (request handle peer) reply state.2)

/-- A reached handle denotes the same generated seed and its original public identity. -/
def Represents (primitives : Primitives) {count : Nat} (state : BareState count)
    (handle : Converted) (seed : IdentitySeed) : Prop :=
  state.2.seeds[handle.index]? = some seed ∧ primitives.publicKeys seed = handle.publicIdentity

/-- Handle conversion neither queries a service nor changes its complete private state. -/
theorem convert_complete (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count index : Nat) (publicIdentity : PublicIdentity)
    (state : BareState count) :
    (simulateQ (bareImpl attachedVerify primitives count) (convert index publicIdentity)).run state =
      pure (some (⟨index, publicIdentity⟩ : Converted), state) := by
  rfl

/-- The full optional reply and all source histories come from the original joint service. -/
theorem staticDh_complete (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (handle : Converted) (peer : PeerEncoding)
    (state : BareState count) :
    (simulateQ (bareImpl attachedVerify primitives count) (staticDh handle peer)).run state =
      let reply := state.2.seeds[handle.index]?.map (fun seed => primitives.staticDh seed peer)
      pure (reply.join, afterDh handle peer reply state) := by
  simp only [staticDh, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  change ((sourceWithHistory count (lazyImpl primitives) (request handle peer)).run state >>= _) = _
  rw [sourceWithHistory_run]
  simp [request, lazyImpl, poolImpl, primitiveReply, afterDh, StateT.run]
  exact ⟨rfl, rfl, rfl⟩

/-- Arbitrary adaptive source continuations start after the exact recorded optional reply. -/
theorem staticDh_continuation {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (handle : Converted) (peer : PeerEncoding)
    (next : Option DhOutput → OracleComp SourceSpec Result) (state : BareState count) :
    (simulateQ (bareImpl attachedVerify primitives count) (staticDh handle peer >>= next)).run state =
      let reply := state.2.seeds[handle.index]?.map (fun seed => primitives.staticDh seed peer)
      (simulateQ (bareImpl attachedVerify primitives count) (next reply.join)).run
        (afterDh handle peer reply state) := by
  rw [simulateQ_bind, StateT.run_bind, staticDh_complete]
  simp only [pure_bind]

/-- Original generated public provenance supplies the same public conversion. -/
theorem converted_public (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64)
    (wiring : SourceWiring c primitives secretOfSeed)
    {count : Nat} (state : BareState count) (handle : Converted) (seed : IdentitySeed)
    (represented : Represents primitives state handle seed) :
    c.xpkConv handle.publicIdentity.ed25519.toList =
      some handle.publicIdentity.convertedX25519.toList := by
  rw [← represented.2]
  exact jointPublic_conversion c primitives secretOfSeed wiring seed

/-- The reached service returns the exact optional source DH, preserving its original history entry even on rejection. -/
theorem staticDh_source (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64)
    (wiring : SourceWiring c primitives secretOfSeed)
    (count : Nat) (handle : Converted) (peer : PeerEncoding)
    (state : BareState count) (seed : IdentitySeed)
    (represented : Represents primitives state handle seed) :
    (simulateQ (bareImpl attachedVerify primitives count) (staticDh handle peer)).run state =
      let reply := sourceDhReply c (secretOfSeed seed).toList peer
      pure (reply, afterDh handle peer (some reply) state) := by
  rw [staticDh_complete, represented.1]
  simp only [Option.map_some, Option.join_some, wiring.staticDh]

/-- No DH success premise is needed to preserve the whole subsequent source computation. -/
theorem staticDh_source_continuation {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64)
    (wiring : SourceWiring c primitives secretOfSeed)
    (count : Nat) (handle : Converted) (peer : PeerEncoding)
    (next : Option DhOutput → OracleComp SourceSpec Result)
    (state : BareState count) (seed : IdentitySeed)
    (represented : Represents primitives state handle seed) :
    (simulateQ (bareImpl attachedVerify primitives count) (staticDh handle peer >>= next)).run state =
      let reply := sourceDhReply c (secretOfSeed seed).toList peer
      (simulateQ (bareImpl attachedVerify primitives count) (next reply)).run
        (afterDh handle peer (some reply) state) := by
  rw [simulateQ_bind, StateT.run_bind, staticDh_source attachedVerify c primitives secretOfSeed
    wiring count handle peer state seed represented]
  simp only [pure_bind]

/-- The optional native conversion contract is used only as a representation equation, never to expose its private result. -/
theorem convert_realization {Native : Type} (index : Nat) (publicIdentity : PublicIdentity)
    (interpret : Converted → Native) (native : Option Native)
    (conversion : native = some (interpret ⟨index, publicIdentity⟩)) :
    Option.map interpret <$> convert index publicIdentity = (pure native : OracleComp SourceSpec _) := by
  simp [convert, conversion]

/-- Replacing a private representation neither creates an identity nor performs an oracle call. -/
theorem convert_bound (index : Nat) (publicIdentity : PublicIdentity) :
    (convert index publicIdentity).IsTotalQueryBound 0 := by
  trivial

/-- Every attempted DH service has exactly its original selective one-query bill, including missing and rejected replies. -/
theorem staticDh_class_bound (handle : Converted) (peer : PeerEncoding)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] :
    (staticDh handle peer).IsQueryBoundP predicate
      (if predicate (.inl (request handle peer)) then 1 else 0) := by
  simp only [staticDh, bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  by_cases selected : predicate (.inl (request handle peer)) <;> simp [selected]

/-- All replies use at most one source static-DH request. -/
theorem staticDh_bound (handle : Converted) (peer : PeerEncoding) :
    (staticDh handle peer).IsTotalQueryBound 1 := by
  unfold staticDh
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- Static DH retains the existing zero-extra-signing restriction. -/
theorem staticDh_no_sign (handle : Converted) (peer : PeerEncoding) :
    (staticDh handle peer).IsQueryBoundP IsSigning 0 := by
  simpa [IsSigning, dynamicClass, IsClass, request] using staticDh_class_bound handle peer IsSigning

/-- Static DH retains the existing zero-extra-creation restriction. -/
theorem staticDh_no_create (handle : Converted) (peer : PeerEncoding) :
    (staticDh handle peer).IsQueryBoundP (IsSourceClass (SourceClass IsCreate)) 0 := by
  simpa [IsSourceClass, sourceQuery, SourceClass, IsCreate, request] using
    staticDh_class_bound handle peer (IsSourceClass (SourceClass IsCreate))

/-- Source operations cross the existing generated selector without changing their addresses or optional reply types. -/
def selectorLift {ι : Type} {baseSpec : OracleSpec ι} :
    QueryImpl SourceSpec (OracleComp (SelectorSpec baseSpec)) :=
  fun query => (SelectorSpec baseSpec).query (.inl query)

def selectorDh {ι : Type} {baseSpec : OracleSpec ι} (handle : Converted) (peer : PeerEncoding) :
    OracleComp (SelectorSpec baseSpec) (Option DhOutput) :=
  simulateQ selectorLift (staticDh handle peer)

/-- Original source-class costs are preserved by the selector lift, for every possible optional response. -/
theorem selectorDh_class_bound {ι : Type} {baseSpec : OracleSpec ι}
    (handle : Converted) (peer : PeerEncoding)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] :
    (selectorDh (baseSpec := baseSpec) handle peer).IsQueryBoundP (SelectorSource (baseSpec := baseSpec) predicate)
      (if predicate (.inl (request handle peer)) then 1 else 0) := by
  change ((liftM ((SelectorSpec baseSpec).query (.inl (.inl (request handle peer)))) : OracleComp (SelectorSpec baseSpec) _) >>=
    fun reply => pure reply.join).IsQueryBoundP (SelectorSource (baseSpec := baseSpec) predicate) _
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨?_, fun _ => by trivial⟩
  by_cases selected : predicate (.inl (request handle peer)) <;> simp [SelectorSource, selected]

/-- The same actual source histories accompany the publicly typed selector request. -/
theorem selectorDh_complete {ι : Type} {baseSpec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (SelectorSpec baseSpec) m) (sourceImpl : QueryImpl SourceSpec m)
    (source : impl ∘ₛ selectorLift = sourceImpl) (handle : Converted) (peer : PeerEncoding) :
    simulateQ impl (selectorDh handle peer) = simulateQ sourceImpl (staticDh handle peer) := by
  rw [selectorDh, ← QueryImpl.simulateQ_compose, source]

/-- The full source seeds, chronological transcript and prior signed-message history survive each static-DH call. -/
theorem afterDh_preserves {count : Nat} (handle : Converted) (peer : PeerEncoding)
    (reply : Option (Option DhOutput)) (state : BareState count) :
    (afterDh handle peer reply state).2.seeds = state.2.seeds ∧
    (afterDh handle peer reply state).2.transcript =
      state.2.transcript ++ [⟨request handle peer, reply⟩] ∧
    ∀ index : Fin count, signedMessages ((afterDh handle peer reply state).1.histories index) =
      signedMessages (state.1.histories index) := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  exact historyUpdate_noSign count index (request handle peer) reply state.1
    (by simp [request, dynamicClass, IsClass])

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting the source service inside the ordinary CCA reduction retains the complete actual joint-identity state and its original local coin program. -/
theorem borrowed_source {ι Result : Type} {baseSpec : OracleSpec ι}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp SourceSpec Result)
    (state : BareState count) :
    (simulateQ (borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count)
      (simulateQ selectorLift client)).run state =
      ccaCoins ((simulateQ (bareImpl attachedVerify primitives count) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, selectorLift]
    simp only [ih, ccaCoins, simulateQ_bind]
    rfl

end BeaconcryptCore.Computational.PqxdhPhase2JointIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.convert_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.convert_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.converted_public' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.converted_public

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_source

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_source_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_source_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.convert_realization' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.convert_realization

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.convert_bound' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.convert_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_bound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_no_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_no_sign

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_no_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.staticDh_no_create

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.selectorDh_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.selectorDh_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.selectorDh_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.selectorDh_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.afterDh_preserves' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.afterDh_preserves

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.borrowed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2JointIdentity.borrowed_source
