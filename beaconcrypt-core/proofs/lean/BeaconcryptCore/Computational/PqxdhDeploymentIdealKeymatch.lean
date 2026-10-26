-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCut

/-!
# The key match of the ideal registration (CE-11b, unit U6)

The decision step of the second compile lemma (design-v2 section 8.4) needs, on the CE side, that a public designation of the target can only happen when the selected accept was active: this is `ideal_keymatch`, the analogue for the ideal registration of CE-9's `PqxdhDeploymentKemTransfer.keymatch_point` (design-v2 section 7.2, item 2, where it is listed under unit U4; U4 is not on central, so the key match is built here for U6).

- The trace invariant `KeyTrace` relates the secrecy ledger's transcript to the extended deployment state with the ideal backend: the session counter equals the raw-accept counter; every accept entry that returned a session returned one below the counter; an accept entry that returned the selected ordinal has bytes that pass the native verification prefix and, when they verify to the selected PQ key, the selected session is marked; every owner that still holds a KEM key pair holds the challenger's pool entry at its owner index (`PoolOwners`); and every published bundle is the Phase 1 writer output of a candidate whose PQ key is the pool entry at its index (`BundleKey`).
- Every query of the complete interface keeps it (`handler_trace` for the native interface, `coinSend_keeps` for the secrecy commands' coins and sends, `query_trace` for the secrecy layer composed with the handler, `ledgerHandler`), it holds at the start (`keyTrace_initial`), and so it holds on every outcome of the common deployment experiment with the ideal registration (`game_trace`, through the flattening of the secrecy layer).
- The per-command facts behind it, on the slot program of the ideal registration (`prog_create`, `prog_bundle`, `prog_accept`, `prog_build`, `prog_finish`, `prog_hmac`), cover the CE-native hidden steps: the selected accept (`acceptExposed_facts` from `acceptInactive_facts`, `acceptActive_facts` and `tailCE_tail`: a returned session is the session counter before the call and, on the active path, follows the hidden root read that marks it), the marked build (`buildHidden_sessions`) and owner k's challenge finish (`finishChallenge_facts`, `groupCE_sessions`: the reinstalled owner holds no KEM key pair or is unchanged). Every outcome of a slot core is an outcome of its slot program (`slotCore_support`, `idealReg_support`).
- `ideal_keymatch`: under the approved `Phase1ReadBack`, on every outcome, a designation of the target's raw-accept ordinal and KEM creation index on the final transcript names accept bytes of the selected session (`PqxdhDeploymentKemTransfer.designate_keys`) that verify to owner k's published PQ key, which is pool entry k, the selected key; so the selected session is marked. `target_marked` states it for a CE designation `g` through `PqxdhDeploymentKemTransfer.target`.
- The mark changes only at the selected accept (`handler_core`); once the accept counter is beyond the selected ordinal no run changes it (`run_settled`); and the selected accept on bytes that do not verify to the selected PQ key leaves no mark (`handler_accept_inactive`). The branches of the second compile lemma use these (`PqxdhDeploymentIdealBranch`).

These are support facts and one consequence of the approved codec contract `Phase1ReadBack`. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhLiveKemReservation (Pair)
open PqxdhDeploymentEligibility (Alike kemPublic)
open PqxdhJointIdentity (IdentitySeed)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Owners holding pool keys -/

/-- Every owner that still holds a KEM key pair holds the pool entry at its index, when the pool has one. -/
def PoolOwners (pool : List (Pair KemSK)) (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) : Prop :=
  ∀ (j : ℕ) (owner : PqxdhRegistrationSchedule.Owner KemSK) (pk : PqxdhKemIndCca.MlKem768PublicKey) (pair : Pair KemSK),
    owners[j]? = some owner → kemPublic owner.beacon.phase = some pk → pool[j]? = some pair → pk = pair.1

/-- Steps that keep every owner's view keep the pool owners. -/
theorem poolOwners_alike (pool : List (Pair KemSK)) (before after : PqxdhRegistrationSchedule.State KemSK)
    (alike : Alike before after) (held : PoolOwners pool before.owners) : PoolOwners pool after.owners := by
  intro j owner pk pair found kem slot
  have view := alike.2.2 j
  rw [found] at view
  cases old : before.owners[j]? with
  | none => rw [old] at view; cases view
  | some prior =>
      rw [old] at view
      simp only [Option.map_some, Option.some.injEq] at view
      have kemEq : kemPublic owner.beacon.phase = kemPublic prior.beacon.phase :=
        congrArg (fun value => value.2.2.2.2) view
      exact held j prior pk pair old (kemEq ▸ kem) slot

/-- Replacing an owner by one that holds no KEM key pair, or the same one, keeps the pool owners. -/
theorem poolOwners_set (pool : List (Pair KemSK)) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (held : PoolOwners pool owners) (index : ℕ) (next : PqxdhRegistrationSchedule.Owner KemSK)
    (kept : kemPublic next.beacon.phase = none ∨
      ∃ prior, owners[index]? = some prior ∧ kemPublic next.beacon.phase = kemPublic prior.beacon.phase) :
    PoolOwners pool (owners.set index next) := by
  intro j owner pk pair found kem slot
  by_cases same : j = index
  · subst same
    by_cases bound : j < owners.length
    · rw [List.getElem?_set_self bound, Option.some.injEq] at found
      subst found
      rcases kept with none | ⟨prior, priorFound, priorKem⟩
      · rw [none] at kem; cases kem
      · exact held j prior pk pair priorFound (priorKem ▸ kem) slot
    · rw [List.set_eq_of_length_le (by omega)] at found
      exact held j owner pk pair found kem slot
  · rw [List.getElem?_set_ne (Ne.symm same)] at found
    exact held j owner pk pair found kem slot

/-- A terminal owner holds no KEM key pair. -/
theorem terminal_kem (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (terminal : PqxdhRegistrationSchedule.Terminal owner) : kemPublic owner.beacon.phase = none := by
  unfold PqxdhRegistrationSchedule.Terminal at terminal
  cases phase : owner.beacon.phase <;> simp_all [kemPublic]

/-- Appending an owner whose KEM key pair is the pool entry at its index (or any key pair beyond the pool) keeps the pool owners. -/
theorem poolOwners_append (pool : List (Pair KemSK)) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (held : PoolOwners pool owners) (next : PqxdhRegistrationSchedule.Owner KemSK)
    (fits : ∀ pk pair, kemPublic next.beacon.phase = some pk → pool[owners.length]? = some pair → pk = pair.1) :
    PoolOwners pool (owners ++ [next]) := by
  intro j owner pk pair found kem slot
  by_cases below : j < owners.length
  · rw [List.getElem?_append_left below] at found
    exact held j owner pk pair found kem slot
  · have equal : j = owners.length := by
      have := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst equal
    rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at found
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    exact fits pk pair kem slot


/-! ### Native steps -/

section Native
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- A native raw accept keeps the owners, advances the session counter by one, and a successful one returns the counter before the call and has bytes that pass the native verification prefix. -/
theorem reg_accept (seed : IdentitySeed) (raw : Pqxdh.Bytes) (native : PqxdhRegistrationSchedule.State KemSK)
    (inner : Option ℕ × PqxdhRegistrationSchedule.State KemSK)
    (member : inner ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed (.inr (.accept raw))).run
      native)) :
    inner.2.owners = native.owners ∧ inner.2.shared.2.sessions = native.shared.2.sessions + 1 ∧
      ∀ session, inner.1 = some session → session = native.shared.2.sessions ∧
        ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value := by
  change inner ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeAccept setup codec checks seed
    PqxdhRegistrationSchedule.observationScalar raw)).run native) at member
  rw [PqxdhRegistrationSchedule.onShared_run, support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  obtain ⟨sessions, returned⟩ := PqxdhDeploymentRegistrationTrace.nativeAccept_session setup codec checks seed raw _
    reached reachedMember
  exact ⟨rfl, sessions, returned⟩

/-- A native registration command other than a raw accept keeps the session counter. -/
theorem reg_sessions (seed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (notAccept : ∀ raw, request ≠ .accept raw) (native : PqxdhRegistrationSchedule.State KemSK)
    (inner : PqxdhRegistrationSchedule.QuerySpec request × PqxdhRegistrationSchedule.State KemSK)
    (member : inner ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed (.inr request)).run native)) :
    inner.2.shared.2.sessions = native.shared.2.sessions :=
  PqxdhDeploymentRegistrationTrace.native_sessions setup codec checks seed (.inl (.inr request))
    (fun raw same => notAccept raw (by cases same; rfl)) native inner member

/-- The owner after a native finish attempt holds no KEM key pair, or is unchanged. -/
theorem nativeOwner_kem (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × NativeState KemSK)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run shared)) :
    kemPublic result.1.2.beacon.phase = none ∨ result.1.2 = owner := by
  cases phase : owner.beacon.phase with
  | initSent control prekey oneTime kem =>
      exact Or.inl (terminal_kem _ (PqxdhRegistrationSchedule.native_attempt_terminal setup codec raw owner control
        prekey oneTime kem phase shared result member))
  | _ =>
      right
      simp only [PqxdhBeaconPhase2Publication.nativeOwner, PqxdhBeaconPhase2Publication.owner, phase, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl

/-- A native bundle call keeps the session counter and the pool owners, and a published bundle is the Phase 1 writer output of a candidate whose PQ key the owner holds. -/
theorem reg_bundle (seed : IdentitySeed) (index : ℕ) (pool : List (Pair KemSK))
    (native : PqxdhRegistrationSchedule.State KemSK) (held : PoolOwners pool native.owners)
    (inner : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)
    (member : inner ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed (.inr (.bundle index))).run
      native)) :
    inner.2.shared.2.sessions = native.shared.2.sessions ∧ PoolOwners pool inner.2.owners ∧
      ∀ bytes, inner.1 = some bytes → ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK)
        (keys : PqxdhEd25519EufCma.Phase1KeyTuple) (s1 s2 s3 : PqxdhEd25519EufCma.Ed25519Signature),
        native.owners[index]? = some owner ∧
        codec.write1 (PqxdhJointPhase1SourceWriter.candidate (setup.joint.publicKeys owner.beacon.identity).ed25519 keys
          s1 s2 s3) = some bytes ∧ kemPublic owner.beacon.phase = some keys.pqKey := by
  have sessions := reg_sessions setup codec checks seed (.bundle index) (fun _ same => by cases same) native
    inner member
  cases found : native.owners[index]? with
  | none =>
      have run : (PqxdhRegistrationSchedule.handler setup codec checks seed (.inr (.bundle index))).run native =
          pure (none, native) := by
        simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.bundle, StateT.run_bind,
          StateT.run_get, pure_bind, found, StateT.run_pure]
      rw [run, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, held, fun bytes none => by cases none⟩
  | some owner =>
      change inner ∈ support (PqxdhRegistrationSchedule.bundle setup codec index native) at member
      rw [PqxdhRegistrationSchedule.bundle_source setup codec index native owner found, support_map] at member
      obtain ⟨reached, reachedMember, rfl⟩ := member
      obtain ⟨rejected, published⟩ := PqxdhDeploymentEligibility.bundle_candidate setup codec index owner reached
        reachedMember
      refine ⟨sessions, ?_, ?_⟩
      · refine poolOwners_set pool native.owners held index reached.2 (Or.inr ⟨owner, found, ?_⟩)
        rcases outcome : reached.1 with _ | bytes
        · rw [rejected outcome]
        · obtain ⟨fresh, prekey, oneTime, kem, _, _, _, wasFresh, installed, _⟩ := published bytes outcome
          rw [installed]
          rcases wasFresh with isFresh | isFresh <;> simp [isFresh, kemPublic]
      · intro bytes outcome
        obtain ⟨fresh, prekey, oneTime, kem, s1, s2, s3, wasFresh, _, written⟩ := published bytes outcome
        refine ⟨owner, ⟨setup.dh.publicKey prekey, setup.dh.publicKey oneTime, kem.1⟩, s1, s2, s3, rfl, written, ?_⟩
        rcases wasFresh with isFresh | isFresh <;> simp [isFresh, kemPublic]

/-- A native finish keeps the session counter and the pool owners. -/
theorem reg_finish (seed : IdentitySeed) (index : ℕ) (raw : Pqxdh.Bytes) (pool : List (Pair KemSK))
    (native : PqxdhRegistrationSchedule.State KemSK) (held : PoolOwners pool native.owners)
    (inner : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)
    (member : inner ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed (.inr (.finish index raw))).run
      native)) :
    inner.2.shared.2.sessions = native.shared.2.sessions ∧ PoolOwners pool inner.2.owners := by
  have sessions := reg_sessions setup codec checks seed (.finish index raw) (fun _ same => by cases same) native
    inner member
  refine ⟨sessions, ?_⟩
  cases found : native.owners[index]? with
  | none =>
      change inner ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run native) at member
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw native found, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact held
  | some owner =>
      change inner ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw native) at member
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw native owner found, support_map] at member
      obtain ⟨reached, reachedMember, rfl⟩ := member
      refine poolOwners_set pool native.owners held index reached.1.2 ?_
      rcases nativeOwner_kem setup codec raw owner native.shared reached reachedMember with none | same
      · exact Or.inl none
      · exact Or.inr ⟨owner, found, by rw [same]⟩

/-- A shared native command (raw accept, build, HMAC, BLAKE2b) keeps the owners. -/
theorem reg_shared_owners (seed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (kind : match request with
      | .accept _ | .build _ _ | .hmac _ _ | .hash _ => True
      | _ => False)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (inner : PqxdhRegistrationSchedule.QuerySpec request × PqxdhRegistrationSchedule.State KemSK)
    (member : inner ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed (.inr request)).run native)) :
    inner.2.owners = native.owners := by
  · cases request <;> simp only at kind <;>
      simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.onShared_run, support_map,
        Set.mem_image] at member <;>
      obtain ⟨_, _, rfl⟩ := member <;> rfl

end Native


/-! ### Support invariants of stateful slot clients -/

section Keeps

/-- An invariant kept by every step of a stateful handler over any oracle interface is kept by every simulated program, on the support. -/
theorem keeps_any {ι₁ ι₂ σ α : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (inv : σ → Prop)
    (keeps : ∀ query state, inv state → ∀ result ∈ support ((impl query).run state), inv result.2)
    (work : OracleComp spec₁ α) (state : σ) (holds : inv state) :
    ∀ result ∈ support ((simulateQ impl work).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact holds
  | query_bind query next ih =>
      intro result supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, member, final⟩ := supported
      exact ih middle.1 middle.2 (keeps query state holds middle member) result final

end Keeps

/-! ### The selected accept -/

section Selected
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (tailCE liftS)

variable {KemSK Reader : Type}

/-- The marker client under `tailCE`, from any state: the session counter is kept, and a successful reply follows a hidden read with the challenge marker, which marks the session. -/
theorem tailCE_client (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader)
    (marker : input.shared = .challenge) (s : NativeState KemSK × Option (ℕ × Coord))
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
      (PqxdhRegistrationJointKemOpaqueClient.client control binding input))).run s)) :
    result.2.1.2.sessions = s.1.2.sessions ∧ (∀ token, result.1 = RustM.ok (some token) → result.2.2.isSome) := by
  have auxStep : ∀ (query : PqxdhServerRelatedRootConsumer.Auxiliary) (st : NativeState KemSK × Option (ℕ × Coord)),
      (match query with
        | .consume _ => False
        | _ => True) →
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr query) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st = pure ((), st) := by
    intro query st kind
    cases query <;> simp only at kind <;> rfl
  have consumeStep : ∀ (rid : beaconcrypt_core.pqxdh.RegistrationId) (st : NativeState KemSK × Option (ℕ × Coord)),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr (.consume rid)) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        pure ((), ((st.1.1, { st.1.2 with server := { st.1.2.server with
          consumed := st.1.2.server.consumed ++ [absBytes rid.bytes] } }), st.2)) := by
    intro rid st
    rfl
  have rootStep : ∀ st : NativeState KemSK × Option (ℕ × Coord),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inl input) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        (fun _ => (PqxdhServerAuthEntryFactor.sentinel, (st.1, some (index, PqxdhDeploymentIdealSteps.coordsOf input)))) <$>
          (SlotSpec.query (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) : OracleComp SlotSpec _) := by
    intro st
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      PqxdhRegistrationJointKemOpaqueTail.forward]
    simp only [tailCE, StateT.run, marker, map_eq_bind_pure_comp]
    rfl
  unfold PqxdhRegistrationJointKemOpaqueClient.client at member
  simp only [simulateQ_bind, StateT.run_bind, auxStep .eraseShared s trivial, pure_bind] at member
  split at member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, fun token same => by cases same⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, fun token same => by cases same⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, fun token same => by cases same⟩
  · simp only [simulateQ_bind, StateT.run_bind, rootStep, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨_, _, member⟩ := member
    simp only [auxStep .eraseInput _ trivial, consumeStep, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, rfl, _, rfl, rfl⟩ := member
    exact ⟨rfl, fun _ _ => rfl⟩

/-- The marker tail under `tailCE`: the installed game state advances the session counter of the given state by one, every later request keeps it, and a returned session is the counter of the given state and follows a hidden read that marked the session. -/
theorem tailCE_tail (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge)
    (s : NativeState KemSK × Option (ℕ × Coord))
    (result : Option ℕ × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run s)) :
    result.2.1.2.sessions = state.sessions + 1 ∧
      ∀ session, result.1 = some session → session = state.sessions ∧ result.2.2.isSome := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail at member
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at member
  obtain ⟨installed, installedMember, member⟩ := member
  change installed ∈ support ((fun r => (r.1, (r.2, s.2))) <$> liftS ((PqxdhRegistrationJointKemOpaqueTail.mutation
    (.install _)).run s.1)) at installedMember
  simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
    PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState, StateT.run, support_pure,
    Set.image_singleton, Set.mem_singleton_iff] at installedMember
  subst installedMember
  rcases found : collected.1 with _ | input
  · simp only [found, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, fun session none => by cases none⟩
  · simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨returned, returnedMember, member⟩ := member
    have client := tailCE_client hmac index state.server.control
      ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input (marker input found) _
      returned returnedMember
    rcases outcome : returned.1 with (_ | token) | _ | _ <;> simp only [outcome] at member
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨client.1, fun session none => by cases none⟩
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨published, publishedMember, rfl⟩ := member
      change published ∈ support ((fun r => (r.1, (r.2, returned.2.2))) <$> liftS ((PqxdhRegistrationJointKemOpaqueTail.mutation
        (.publish _ _)).run returned.2.1)) at publishedMember
      simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
        PqxdhServerAuthNative.nativeModify, PqxdhServerAuthNative.localState, StateT.run, support_pure,
        Set.image_singleton, Set.mem_singleton_iff] at publishedMember
      subst publishedMember
      exact ⟨client.1, fun session same => ⟨by simpa using same.symm, client.2 token outcome⟩⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨client.1, fun session none => by cases none⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨client.1, fun session none => by cases none⟩

/-- Item 2's candidate-free suffix with a marker returns prepared inputs carrying that marker, under any interpreter. -/
theorem program_marker {E Shared σ ι' : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (StateT σ (OracleComp spec')))
    (verified : PqxdhServerRootPreparation.Verified Reader) (ephemeral : PqxdhServerRootPreparation.Ephemeral E)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (state : σ) (prepared : Option (PqxdhRegistrationJointKemOpaqueSuffix.Prepared Reader E Shared) × σ)
    (member : prepared ∈ support ((simulateQ impl
      (PqxdhRegistrationJointKemOpaqueSuffix.program verified ephemeral ciphertext token)).run state)) :
    ∀ input, prepared.1 = some input → input.shared = token := by
  rw [PqxdhRegistrationJointKemOpaqueSuffix.program, simulateQ_map, StateT.run_map, support_map] at member
  obtain ⟨inner, -, rfl⟩ := member
  intro input found
  rcases inner with ⟨_ | original, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    rfl

end Selected

/-! ### The selected accept, natively -/

section SelectedAccept
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (tailCE liftS acceptActive acceptInactive acceptExposed AcceptOut)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The LQ-F logged accept as the inactive selected accept: it advances the session counter by one, sets no mark, and a returned session is the counter before the call and has bytes that pass the native verification prefix. -/
theorem acceptInactive_facts (seed : IdentitySeed) (raw : Pqxdh.Bytes) (s : NativeState KemSK)
    (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptInactive setup codec checks seed raw).run s)) :
    r.2.2.sessions = s.2.sessions + 1 ∧ r.1.2 = (false, none) ∧
      ∀ session, r.1.1.1 = some session → session = s.2.sessions ∧
        ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value := by
  change r ∈ support ((fun r : (Option ℕ × Option PqxdhJointGapDh.ScalarBytes) × NativeState KemSK =>
    ((r.1, (false, none)), r.2)) <$> liftS ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
      raw).run s)) at member
  rw [support_map, support_liftComp] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  have native : (inner.1.1, inner.2) ∈ support ((PqxdhServerAuthNative.nativeAccept setup codec checks seed
      PqxdhRegistrationSchedule.observationScalar raw).run s) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨inner, innerMember, rfl⟩
  obtain ⟨sessions, returned⟩ := PqxdhDeploymentRegistrationTrace.nativeAccept_session setup codec checks seed raw s
    _ native
  exact ⟨sessions, rfl, returned⟩

/-- The selected accept on a verified key match: it advances the session counter by one, and a returned session is the counter before the call and follows a hidden read that marked it. -/
theorem acceptActive_facts (seed : IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) (s : NativeState KemSK) (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptActive setup codec checks seed challenge verified).run s)) :
    r.2.2.sessions = s.2.sessions + 1 ∧ ∀ session, r.1.1.1 = some session → session = s.2.sessions ∧ r.1.2.2.isSome := by
  change r ∈ support (do
    let pre ← liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
      (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) verified)).run
        s.2.server.consumed)
    match pre.1.1 with
    | none => do
        let r ← liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup (setup.joint.publicKeys seed) s.2
          (none, pre.2)).run s)
        pure (((r.1, pre.1.2), (false, none)), r.2)
    | some ephemeral => do
        let prepared ← liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
          (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := PqxdhBeaconPhase2Preparation.Word32) verified
            ephemeral (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge)).run pre.2)
        let answer ← (simulateQ (tailCE setup.hmac s.2.sessions)
          (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared)).run
            (s, none)
        pure (((answer.1, pre.1.2), (true, answer.2.2)), answer.2.1)) at member
  rw [mem_support_bind_iff] at member
  obtain ⟨pre, -, member⟩ := member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨tailed, tailedMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [support_liftComp] at tailedMember
    simp only [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run] at tailedMember
    subst tailedMember
    exact ⟨rfl, fun session none => by cases none⟩
  · rw [mem_support_bind_iff] at member
    obtain ⟨prepared, preparedMember, member⟩ := member
    rw [mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [support_liftComp] at preparedMember
    have marker := program_marker (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed) verified
      _ _ _ _ prepared preparedMember
    have tailed := tailCE_tail setup.hmac s.2.sessions setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared marker
      (s, none) answer answerMember
    exact ⟨tailed.1, fun session found => ⟨(tailed.2 session found).1, (tailed.2 session found).2⟩⟩

/-- The selected accept with its encapsulation exposed: it advances the session counter by one, and a returned session is the counter before the call and has bytes that pass the native verification prefix; on the selected PQ key it also followed a hidden read that marked it. -/
theorem acceptExposed_facts (seed : IdentitySeed) (chosen : Pair KemSK) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (raw : Pqxdh.Bytes) (s : NativeState KemSK) (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptExposed setup codec checks seed chosen challenge raw).run s)) :
    r.2.2.sessions = s.2.sessions + 1 ∧
      ∀ session, r.1.1.1 = some session → session = s.2.sessions ∧
        ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
          (value.keys.pqKey = chosen.1 → r.1.2.2.isSome) := by
  unfold acceptExposed at member
  rcases found : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | verified
  · rw [found] at member
    obtain ⟨sessions, _, returned⟩ := acceptInactive_facts setup codec checks seed raw s r member
    refine ⟨sessions, fun session returnedSome => ?_⟩
    obtain ⟨_, value, verifiedSome⟩ := returned session returnedSome
    rw [found] at verifiedSome
    cases verifiedSome
  · rw [found] at member
    by_cases same : verified.keys.pqKey = chosen.1
    · simp only [same, ↓reduceIte] at member
      obtain ⟨sessions, returned⟩ := acceptActive_facts setup codec checks seed challenge verified s r member
      exact ⟨sessions, fun session returnedSome =>
        ⟨(returned session returnedSome).1, verified, rfl, fun _ => (returned session returnedSome).2⟩⟩
    · simp only [same, ↓reduceIte] at member
      obtain ⟨sessions, _, returned⟩ := acceptInactive_facts setup codec checks seed raw s r member
      refine ⟨sessions, fun session returnedSome => ⟨(returned session returnedSome).1, verified, rfl, ?_⟩⟩
      intro matched
      exact absurd matched same

end SelectedAccept

/-! ### The registration commands of the ideal registration -/

section Program
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (liftS onSlots realRegAt createPool createReg acceptStep buildStep finishStep idealProg
  buildHidden finishChallenge IdealCore)
open PqxdhDeploymentIdealParams (Target Params)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- Every outcome of `realRegAt` is an outcome of the native deployment handler on the deployment state, with the backend kept. -/
theorem realRegAt_support {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK Bk n)
    (result : PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK Bk n)
    (member : result ∈ support ((realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x)) :
    (result.1, result.2.base) ∈ support ((PqxdhDeploymentNative.handler setup codec checks route created.seed
      (.inr query.val)).run x.base) ∧ result.2.backend = x.backend := by
  refine ⟨?_, (PqxdhDeploymentIdealCut.realRegAt_keeps setup codec route checks created query x result member).1⟩
  rw [← PqxdhDeploymentIdealCut.realRegAt_base setup codec route checks created query x, support_map]
  exact ⟨result, member, rfl⟩

/-- A native registration command of the deployment state is the source14 handler on the registration state, with the rest of the deployment state kept. -/
theorem onNative_native {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α)
    (base : PqxdhDeploymentNative.State KemSK) (reply : α) (after : PqxdhDeploymentNative.State KemSK)
    (member : (reply, after) ∈ support ((PqxdhDeploymentNative.onNative work).run base)) :
    (reply, after.native) ∈ support (work.run base.native) := by
  obtain ⟨inner, innerMember, same⟩ := PqxdhDeploymentEligibility.onNative_support work base _ member
  simp only [Prod.mk.injEq] at same
  rw [same.1, same.2]
  exact innerMember

/-- The body of a pool create keeps the shared native state and appends one owner whose KEM key pair is the pool entry at its index, when the pool has one. -/
theorem createPool_facts (pool : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) (r : ℕ × PqxdhRegistrationSchedule.State KemSK)
    (member : r ∈ support ((createPool setup pool pin keyId).run state)) :
    r.2.shared = state.shared ∧ ∃ owner : PqxdhRegistrationSchedule.Owner KemSK, r.2.owners = state.owners ++ [owner] ∧
      ∀ pk pair, kemPublic owner.beacon.phase = some pk → pool[state.owners.length]? = some pair → pk = pair.1 := by
  simp only [createPool, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get, StateT.run_set,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨identity, -, prekey, -, keys, keysMember, rfl⟩ := member
  refine ⟨rfl, _, rfl, fun pk pair kem slot => ?_⟩
  rw [slot] at keysMember
  simp only [support_pure, Set.mem_singleton_iff] at keysMember
  subst keysMember
  simp only [kemPublic, Option.some.injEq] at kem
  exact kem.symm

/-- The create command of the ideal registration keeps the backend and the session counter and appends an owner holding the pool entry at its index. -/
theorem prog_create {count : ℕ} (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (y : XState KemSK IdealCore 2) (r : Option ℕ × XState KemSK IdealCore 2)
    (member : r ∈ support ((idealProg setup codec route checks t p hidden created ⟨.create pin keyId, trivial⟩).run y)) :
    r.2.backend = y.backend ∧ r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions ∧
      (PoolOwners (p.pool t) y.base.native.owners → PoolOwners (p.pool t) r.2.base.native.owners) := by
  change r ∈ support (liftS ((createReg setup (p.pool t) pin keyId).run y)) at member
  rw [support_liftComp] at member
  have based := PqxdhDeploymentIdealCut.onBase_base (match PqxdhDeploymentInterface.parsePin pin with
    | none => pure none
    | some word => some <$> PqxdhDeploymentNative.onNative (createPool setup (p.pool t) word keyId)) y
  have step : (r.1, r.2.base) ∈ support ((match PqxdhDeploymentInterface.parsePin pin with
      | none => pure none
      | some word => some <$> PqxdhDeploymentNative.onNative (createPool setup (p.pool t) word keyId) :
      StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option ℕ)).run y.base) := by
    rw [← based.1, support_map]
    exact ⟨r, member, rfl⟩
  refine ⟨(based.2 r member).1, ?_⟩
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none =>
      simp only [parsed, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at step
      rw [step.2]
      exact ⟨rfl, id⟩
  | some word =>
      simp only [parsed, StateT.run_map] at step
      rw [support_map] at step
      obtain ⟨native, nativeMember, same⟩ := step
      simp only [Prod.mk.injEq] at same
      rw [← same.2]
      obtain ⟨reached, reachedMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ y.base native nativeMember
      obtain ⟨shared, owner, owners, fits⟩ := createPool_facts setup (p.pool t) word keyId y.base.native reached
        reachedMember
      refine ⟨by simp only [shared], fun held => ?_⟩
      simp only [owners]
      exact poolOwners_append _ _ held owner fits

/-- A bundle published at owner index `k` is the Phase 1 writer output of a candidate whose PQ key is the pool entry at `k`, when the pool has one. -/
def BundleKey (pool : List (Pair KemSK)) (k : ℕ) (bytes : Pqxdh.Bytes) : Prop :=
  ∃ (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (s1 s2 s3 : PqxdhEd25519EufCma.Ed25519Signature),
    codec.write1 (PqxdhJointPhase1SourceWriter.candidate identity keys s1 s2 s3) = some bytes ∧
      ∀ pair, pool[k]? = some pair → keys.pqKey = pair.1

/-- The bundle command of the ideal registration keeps the backend, the session counter and the pool owners, and a published bundle carries the pool key at its index. -/
theorem prog_bundle {count : ℕ} (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (k : ℕ)
    (y : XState KemSK IdealCore 2) (r : Option Pqxdh.Bytes × XState KemSK IdealCore 2)
    (member : r ∈ support ((idealProg setup codec route checks t p hidden created ⟨.bundle k, trivial⟩).run y)) :
    r.2.backend = y.backend ∧ r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions ∧
      (PoolOwners (p.pool t) y.base.native.owners → PoolOwners (p.pool t) r.2.base.native.owners ∧
        ∀ bytes, r.1 = some bytes → BundleKey codec (p.pool t) k bytes) := by
  change r ∈ support (liftS ((realRegAt setup codec route checks created ⟨.bundle k, trivial⟩).run y)) at member
  rw [support_liftComp] at member
  obtain ⟨native, backend⟩ := realRegAt_support setup codec route checks created ⟨.bundle k, trivial⟩ y r member
  have lowered := onNative_native _ y.base r.1 r.2.base native
  have sessions := reg_sessions setup codec checks created.seed (.bundle k) (fun _ same => by cases same) y.base.native
    (r.1, r.2.base.native) lowered
  refine ⟨backend, sessions, fun held => ?_⟩
  obtain ⟨-, owners, published⟩ := reg_bundle setup codec checks created.seed k (p.pool t) y.base.native held
    (r.1, r.2.base.native) lowered
  refine ⟨owners, fun bytes found => ?_⟩
  obtain ⟨owner, keys, s1, s2, s3, ownerFound, written, kem⟩ := published bytes found
  exact ⟨_, keys, s1, s2, s3, written, fun pair slot => held k owner keys.pqKey pair ownerFound kem slot⟩

/-- The HMAC command of the ideal registration keeps the backend, the session counter and the owners. -/
theorem prog_hmac {count : ℕ} (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
    (y : XState KemSK IdealCore 2) (r : PqxdhSecretInputKdf.HmacBlock × XState KemSK IdealCore 2)
    (member : r ∈ support ((idealProg setup codec route checks t p hidden created
      ⟨.hmac key message, trivial⟩).run y)) :
    r.2.backend = y.backend ∧ r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions ∧
      r.2.base.native.owners = y.base.native.owners := by
  change r ∈ support (liftS ((realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run y)) at member
  rw [support_liftComp] at member
  obtain ⟨native, backend⟩ := realRegAt_support setup codec route checks created ⟨.hmac key message, trivial⟩ y r member
  have lowered := onNative_native _ y.base r.1 r.2.base native
  exact ⟨backend, reg_sessions setup codec checks created.seed (.hmac key message) (fun _ same => by cases same)
    y.base.native (r.1, r.2.base.native) lowered,
    reg_shared_owners setup codec checks created.seed (.hmac key message) trivial y.base.native
      (r.1, r.2.base.native) lowered⟩

/-- The raw accept of the ideal registration advances the accept counter and the session counter by one and keeps the owners; only the selected ordinal may change the mark; a returned session is the session counter before the call, and at the selected ordinal it has bytes that pass the native verification prefix and, on the selected PQ key, a mark. -/
theorem prog_accept {count : ℕ} (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes)
    (y : XState KemSK IdealCore 2) (r : Option ℕ × XState KemSK IdealCore 2)
    (member : r ∈ support ((idealProg setup codec route checks t p hidden created ⟨.accept raw, trivial⟩).run y)) :
    r.2.backend.accepts = y.backend.accepts + 1 ∧
      r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions + 1 ∧
      r.2.base.native.owners = y.base.native.owners ∧
      (y.backend.accepts ≠ t.accept → r.2.backend.marks = y.backend.marks) ∧
      ∀ session, r.1 = some session → session = y.base.native.shared.2.sessions ∧
        (y.backend.accepts = t.accept → ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw =
          some value ∧ (value.keys.pqKey = p.chosen.1 → r.2.backend.marks.isSome)) := by
  change r ∈ support (acceptStep setup codec route checks t p created raw y) at member
  have accepts := PqxdhDeploymentIdealSteps.acceptStep_accepts setup codec route checks t p created raw y r member
  unfold acceptStep at member
  by_cases selected : y.backend.accepts = t.accept
  · simp only [selected, ↓reduceIte] at member
    rw [support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    obtain ⟨sessions, returned⟩ := acceptExposed_facts setup codec checks created.seed p.chosen p.challenge raw
      y.base.native.shared inner innerMember
    refine ⟨accepts, sessions, rfl, fun other => absurd selected other, fun session found => ?_⟩
    obtain ⟨same, value, verified, marked⟩ := returned session found
    exact ⟨same, fun _ => ⟨value, verified, marked⟩⟩
  · simp only [selected, ↓reduceIte] at member
    change r ∈ support (liftS _) at member
    rw [support_liftComp] at member
    obtain ⟨native, backend⟩ := realRegAt_support setup codec route checks created ⟨.accept raw, trivial⟩ _ r member
    have lowered := onNative_native _ _ r.1 r.2.base native
    obtain ⟨owners, sessions, returned⟩ := reg_accept setup codec checks created.seed raw y.base.native
      (r.1, r.2.base.native) lowered
    refine ⟨accepts, sessions, owners, fun _ => by rw [backend], fun session found => ⟨(returned session found).1,
      fun same => absurd same selected⟩⟩

/-- The marked build keeps the session counter. -/
theorem buildHidden_sessions (hidden : PqxdhRegistrationJointKemPostSkeleton.Hidden Response) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (s : NativeState KemSK)
    (r : Option PqxdhServerRegistrationPublication.Response × NativeState KemSK)
    (member : r ∈ support ((buildHidden hidden session payload).run s)) : r.2.2.sessions = s.2.sessions := by
  unfold buildHidden at member
  rw [PqxdhDeploymentBackend.nativeGet_bind] at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl
  · rw [PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff] at member
    obtain ⟨_, _, member⟩ := member
    simp only [PqxdhServerAuthNative.nativeSet, StateT.run] at member
    subst member
    rfl

/-- The build command of the ideal registration keeps the accept counter, the mark, the session counter and the owners. -/
theorem prog_build {count : ℕ} (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (y : XState KemSK IdealCore 2) (r : Option PqxdhServerRegistrationPublication.Response × XState KemSK IdealCore 2)
    (member : r ∈ support ((idealProg setup codec route checks t p hidden created
      ⟨.build session payload, trivial⟩).run y)) :
    r.2.backend.accepts = y.backend.accepts ∧ r.2.backend.marks = y.backend.marks ∧
      r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions ∧
      r.2.base.native.owners = y.base.native.owners := by
  have real : r ∈ support ((onSlots (realRegAt setup codec route checks created
      ⟨.build session payload, trivial⟩)).run y) →
      r.2.backend.accepts = y.backend.accepts ∧ r.2.backend.marks = y.backend.marks ∧
        r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions ∧
        r.2.base.native.owners = y.base.native.owners := by
    intro realMember
    change r ∈ support (liftS _) at realMember
    rw [support_liftComp] at realMember
    obtain ⟨native, backend⟩ := realRegAt_support setup codec route checks created ⟨.build session payload, trivial⟩ y r
      realMember
    have lowered := onNative_native _ y.base r.1 r.2.base native
    exact ⟨by rw [backend], by rw [backend], reg_sessions setup codec checks created.seed (.build session payload)
      (fun _ same => by cases same) y.base.native (r.1, r.2.base.native) lowered,
      reg_shared_owners setup codec checks created.seed (.build session payload) trivial y.base.native
        (r.1, r.2.base.native) lowered⟩
  change r ∈ support (buildStep setup codec route checks hidden created session payload y) at member
  unfold buildStep at member
  split at member
  · rename_i index coords _
    split at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨value, -, member⟩ := member
      rw [mem_support_bind_iff] at member
      obtain ⟨built, builtMember, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [support_liftComp] at builtMember
      exact ⟨rfl, rfl, buildHidden_sessions (hidden value) session payload _ built builtMember, rfl⟩
    · exact real member
  · exact real member

/-- The CE-native grouped finish keeps the session counter. -/
theorem groupCE_sessions (hidden : PqxdhRegistrationJointKemEntryFactor.Output →
      PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) (s : NativeState KemSK × Option Coord)
    (r : Option PqxdhBeaconPhase2Publication.Staged × (NativeState KemSK × Option Coord))
    (member : r ∈ support ((PqxdhDeploymentIdealSteps.groupCE setup codec hidden pending).run s)) :
    r.2.1.2.sessions = s.1.2.sessions := by
  unfold PqxdhDeploymentIdealSteps.groupCE at member
  change r ∈ support (match pending.root.shared with
    | .challenge => _
    | .known _ => _) at member
  split at member
  · split at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨value, -, member⟩ := member
      rw [mem_support_bind_iff] at member
      obtain ⟨ctx, ctxMember, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [support_liftComp] at ctxMember
      simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at ctxMember
      obtain ⟨_, _, rfl⟩ := ctxMember
      rfl
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
  · rw [support_map, support_liftComp] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    rw [StateT.run_bind, mem_support_bind_iff] at innerMember
    obtain ⟨rooted, rootedMember, innerMember⟩ := innerMember
    have rootKept : rooted.2.2 = s.1.2 := by
      unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot at rootedMember
      split at rootedMember
      · simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, support_map, Set.mem_image] at rootedMember
        obtain ⟨_, _, rfl⟩ := rootedMember
        rfl
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rootedMember
        subst rootedMember
        rfl
    change inner.2.2.sessions = s.1.2.sessions
    rw [← rootKept]
    split at innerMember
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerMember
      subst innerMember
      rfl
    · simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at innerMember
      obtain ⟨_, _, rfl⟩ := innerMember
      rfl

/-- Owner k's challenge finish keeps the session counter, and the reinstalled owner holds no KEM key pair or is unchanged; hence it keeps the pool owners. -/
theorem finishChallenge_facts (hidden : PqxdhRegistrationJointKemEntryFactor.Output →
      PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes) (pool : List (Pair KemSK))
    (st : PqxdhRegistrationSchedule.State KemSK × Option Coord)
    (r : Option Pqxdh.Bytes × (PqxdhRegistrationSchedule.State KemSK × Option Coord))
    (member : r ∈ support ((finishChallenge setup codec hidden challenge index raw).run st)) :
    r.2.1.shared.2.sessions = st.1.shared.2.sessions ∧ (PoolOwners pool st.1.owners → PoolOwners pool r.2.1.owners) := by
  unfold finishChallenge at member
  change r ∈ support (match st.1.owners[index]? with
    | none => _
    | some owner => _) at member
  split at member
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, id⟩
  · rename_i owner found
    rw [mem_support_bind_iff] at member
    obtain ⟨result, resultMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    have kept := keeps_any (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge)
      (fun s : NativeState KemSK × Option Coord => s.1.2.sessions = st.1.shared.2.sessions)
      (fun query state good after afterMember => by
        rcases query with preparation | pending
        · change after ∈ support ((fun reply => (reply, state)) <$> liftS _) at afterMember
          rw [support_map] at afterMember
          obtain ⟨_, _, rfl⟩ := afterMember
          exact good
        · exact (groupCE_sessions setup codec hidden pending state after afterMember).trans good)
      (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner) (st.1.shared, st.2) rfl result
      resultMember
    refine ⟨kept, fun held => ?_⟩
    have produced : result.1 ∈ support (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge)
        _ (st.1.shared, st.2)
      rw [StateT.run'_eq, support_map]
      exact ⟨result, resultMember, rfl⟩
    refine poolOwners_set pool st.1.owners held index result.1.2 ?_
    unfold PqxdhDeploymentIdealSteps.groupedOwnerCE at produced
    split at produced
    · rename_i control prekey oneTime kem phase
      rw [mem_support_bind_iff] at produced
      obtain ⟨prepared, -, produced⟩ := produced
      left
      split at produced
      · rw [support_pure, Set.mem_singleton_iff] at produced
        rw [produced]
        exact terminal_kem _ (PqxdhRegistrationSchedule.finish_terminal control owner none)
      · rw [mem_support_bind_iff] at produced
        obtain ⟨staged, -, produced⟩ := produced
        rw [support_pure, Set.mem_singleton_iff] at produced
        rw [produced]
        exact terminal_kem _ (PqxdhRegistrationSchedule.finish_terminal control owner staged)
    · rw [support_pure, Set.mem_singleton_iff] at produced
      right
      exact ⟨owner, found, by rw [produced]⟩

/-- The finish command of the ideal registration keeps the accept counter, the mark, the session counter and the pool owners. -/
theorem prog_finish {count : ℕ} (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes)
    (y : XState KemSK IdealCore 2) (r : Option Pqxdh.Bytes × XState KemSK IdealCore 2)
    (member : r ∈ support ((idealProg setup codec route checks t p hidden created ⟨.finish owner raw, trivial⟩).run y)) :
    r.2.backend.accepts = y.backend.accepts ∧ r.2.backend.marks = y.backend.marks ∧
      r.2.base.native.shared.2.sessions = y.base.native.shared.2.sessions ∧
      (PoolOwners (p.pool t) y.base.native.owners → PoolOwners (p.pool t) r.2.base.native.owners) := by
  change r ∈ support (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p hidden created owner raw y)
    at member
  unfold PqxdhDeploymentIdealSteps.finishStep at member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨finished, finishedMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    obtain ⟨sessions, owners⟩ := finishChallenge_facts setup codec hidden p.challenge owner raw (p.pool t)
      (y.base.native, none) finished finishedMember
    exact ⟨rfl, rfl, sessions, owners⟩
  · change r ∈ support (liftS _) at member
    rw [support_liftComp] at member
    obtain ⟨native, backend⟩ := realRegAt_support setup codec route checks created ⟨.finish owner raw, trivial⟩ y r
      member
    have lowered := onNative_native _ y.base r.1 r.2.base native
    exact ⟨by rw [backend], by rw [backend], reg_sessions setup codec checks created.seed (.finish owner raw)
      (fun _ same => by cases same) y.base.native (r.1, r.2.base.native) lowered,
      fun held => (reg_finish setup codec checks created.seed owner raw (p.pool t) y.base.native held
        (r.1, r.2.base.native) lowered).2⟩

end Program

/-! ### The trace invariant of the ideal registration -/

section Trace
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSlots (Coord SlotSpec slotCore detach attach)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState idealReg idealProg)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (Entry)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- The trace invariant of the ideal registration at a target and draws, between the transcript and the deployment state with the ideal backend: the session counter is the accept counter, every accept entry that returned a session returned one below the accept counter, an accept entry that returned the selected ordinal has bytes that pass the native verification prefix and, on the selected PQ key, the selected session is marked, every owner holding a KEM key pair holds the pool entry at its index, and every published bundle carries the pool key at its index. -/
structure KeyTrace (transcript : List Entry) (base : PqxdhDeploymentNative.State KemSK) (core : IdealCore) : Prop where
  sessions : base.native.shared.2.sessions = core.accepts
  below : ∀ raw s, (⟨.inl (.inr (.accept raw)), some s⟩ : Entry) ∈ transcript → s < core.accepts
  selected : ∀ raw, (⟨.inl (.inr (.accept raw)), some t.accept⟩ : Entry) ∈ transcript →
    ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      (value.keys.pqKey = p.chosen.1 → core.marks.isSome)
  owners : PoolOwners (p.pool t) base.native.owners
  bundles : ∀ k bytes, (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ transcript → BundleKey codec (p.pool t) k bytes

/-- A query that is neither a raw accept nor a bundle call. -/
def Quiet : PqxdhDeploymentInterface.Query → Prop
  | .inl (.inr (.accept _)) => False
  | .inl (.inr (.bundle _)) => False
  | _ => True

/-- An entry of a quiet query is neither an accept entry nor a bundle entry. -/
theorem quiet_entry (query : PqxdhDeploymentInterface.Query) (quiet : Quiet query)
    (reply : PqxdhDeploymentInterface.FullSpec.Range query) :
    (∀ raw s, (⟨.inl (.inr (.accept raw)), some s⟩ : Entry) ≠ ⟨query, reply⟩) ∧
      ∀ k bytes, (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ≠ ⟨query, reply⟩ := by
  refine ⟨fun raw s same => ?_, fun k bytes same => ?_⟩
  · have queries := congrArg Entry.query same
    simp only at queries
    rw [← queries] at quiet
    exact quiet
  · have queries := congrArg Entry.query same
    simp only at queries
    rw [← queries] at quiet
    exact quiet

/-- The trace invariant survives a quiet query that keeps the session counter, the pool owners, the accept counter and the mark. -/
theorem keyTrace_quiet (transcript : List Entry) (base base' : PqxdhDeploymentNative.State KemSK) (core core' : IdealCore)
    (trace : KeyTrace setup codec checks t p transcript base core) (query : PqxdhDeploymentInterface.Query)
    (quiet : Quiet query) (reply : PqxdhDeploymentInterface.FullSpec.Range query)
    (sessions : base'.native.shared.2.sessions = base.native.shared.2.sessions)
    (owners : PoolOwners (p.pool t) base'.native.owners) (accepts : core'.accepts = core.accepts)
    (marks : core'.marks = core.marks) :
    KeyTrace setup codec checks t p (transcript ++ [⟨query, reply⟩]) base' core' := by
  obtain ⟨notAccept, notBundle⟩ := quiet_entry query quiet reply
  refine ⟨by rw [sessions, accepts]; exact trace.sessions, fun raw s found => ?_, fun raw found => ?_, owners,
    fun k bytes found => ?_⟩
  · rcases List.mem_append.mp found with old | new
    · rw [accepts]; exact trace.below raw s old
    · exact absurd (List.mem_singleton.mp new) (notAccept raw s)
  · rcases List.mem_append.mp found with old | new
    · rw [marks]; exact trace.selected raw old
    · exact absurd (List.mem_singleton.mp new) (notAccept raw t.accept)
  · rcases List.mem_append.mp found with old | new
    · exact trace.bundles k bytes old
    · exact absurd (List.mem_singleton.mp new) (notBundle k bytes)

/-- Every outcome of a slot core is an outcome of its slot program on the detached state. -/
theorem slotCore_support {Γ : Type} {n : ℕ}
    (prog : PqxdhLiveServerConstruction.Created Unit → PqxdhDeploymentIdealSlots.SlotProgram KemSK Γ n) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × Γ)) n)
    (result : PqxdhRecordLiftInterface.EnvSpec.Range query ×
      XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × Γ)) n)
    (member : result ∈ support ((slotCore prog svc created query).run x)) :
    (result.1, detach result.2) ∈ support ((prog created query).run (detach x)) := by
  rw [PqxdhDeploymentIdealSlots.slotCore_run, support_map] at member
  obtain ⟨r, rMember, rfl⟩ := member
  apply OracleComp.support_simulateQ_run'_subset (PqxdhRegistrationJointKemSecondEntry.slotImpl svc) _
    (x.backend.2.1, x.backend.1)
  rw [StateT.run'_eq, support_map]
  exact ⟨r, rMember, rfl⟩

/-- Every outcome of a base step of the extended state is an outcome of the step on the deployment state, with the backend kept. -/
theorem onBase_support {Bk : Type} {n : ℕ} {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (x : XState KemSK Bk n) (result : α × XState KemSK Bk n)
    (member : result ∈ support ((PqxdhDeploymentBackend.onBase step).run x)) :
    result.2.backend = x.backend ∧ (result.1, result.2.base) ∈ support (step.run x.base) := by
  have based := PqxdhDeploymentIdealCut.onBase_base step x
  refine ⟨(based.2 result member).1, ?_⟩
  rw [← based.1, support_map]
  exact ⟨result, member, rfl⟩

/-- Every outcome of a registration command of the ideal registration is an outcome of its slot program on the detached state. -/
theorem idealReg_support (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhRecordLiftInterface.EnvQuery)
    (x : XState KemSK (IdealBk TableState) 2)
    (result : PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK (IdealBk TableState) 2)
    (member : result ∈ support ((idealReg setup codec route checks t p created query).run x)) :
    (result.1, detach result.2) ∈ support ((idealProg setup codec route checks t p
      (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created query).run (detach x)) :=
  slotCore_support _ _ created query x result member

/-- Every request of the handler with the ideal registration keeps the trace invariant, with the request and its reply appended to the transcript. -/
theorem handler_trace (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (transcript : List Entry) (x : XState KemSK (IdealBk TableState) 2)
    (trace : KeyTrace setup codec checks t p transcript x.base x.backend.2.2)
    (result : PqxdhDeploymentInterface.Spec.Range query × XState KemSK (IdealBk TableState) 2)
    (member : result ∈ support ((handlerWith setup codec route (idealReg setup codec route checks t p created)
      query).run x)) :
    KeyTrace setup codec checks t p (transcript ++ [⟨.inl query, result.1⟩]) result.2.base result.2.backend.2.2 := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inl coin)) trivial _ rfl trace.owners rfl
      rfl
  · cases command with
    | create pin keyId =>
        have prog := idealReg_support setup codec route checks t p created ⟨.create pin keyId, trivial⟩ x result member
        obtain ⟨backend, sessions, owners⟩ := prog_create setup codec route checks t p _ created pin keyId _ _ prog
        replace owners := owners trace.owners
        dsimp only [detach] at *
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.create pin keyId))) trivial _
          sessions owners (by rw [backend]) (by rw [backend])
    | bundle k =>
        have prog := idealReg_support setup codec route checks t p created ⟨.bundle k, trivial⟩ x result member
        obtain ⟨backend, sessions, keyed⟩ := prog_bundle setup codec route checks t p _ created k _ _ prog
        obtain ⟨owners, published⟩ := keyed trace.owners
        dsimp only [detach] at *
        change result.2.backend.2.2 = x.backend.2.2 at backend
        refine ⟨by rw [backend]; exact sessions.trans trace.sessions, fun raw s found => ?_, fun raw found => ?_,
          owners, fun k' bytes found => ?_⟩
        · rcases List.mem_append.mp found with old | new
          · rw [backend]; exact trace.below raw s old
          · cases List.mem_singleton.mp new
        · rcases List.mem_append.mp found with old | new
          · rw [backend]; exact trace.selected raw old
          · cases List.mem_singleton.mp new
        · rcases List.mem_append.mp found with old | new
          · exact trace.bundles k' bytes old
          · have same := List.mem_singleton.mp new
            injection same with queries replies
            injection queries with queries
            injection queries with queries
            injection queries with queries
            subst queries
            exact published bytes replies.symm
    | accept raw =>
        have prog := idealReg_support setup codec route checks t p created ⟨.accept raw, trivial⟩ x result member
        obtain ⟨accepts, sessions, owners, marks, returned⟩ := prog_accept setup codec route checks t p _ created raw _
          _ prog
        dsimp only [detach] at *
        change result.2.backend.2.2.accepts = x.backend.2.2.accepts + 1 at accepts
        change x.backend.2.2.accepts ≠ t.accept → result.2.backend.2.2.marks = x.backend.2.2.marks at marks
        refine ⟨by rw [accepts, sessions, trace.sessions], fun raw' s found => ?_, fun raw' found => ?_,
          by rw [owners]; exact trace.owners, fun k bytes found => ?_⟩
        · rcases List.mem_append.mp found with old | new
          · rw [accepts]; exact Nat.lt_succ_of_lt (trace.below raw' s old)
          · have same := List.mem_singleton.mp new
            injection same with queries replies
            injection queries with queries
            injection queries with queries
            injection queries with queries
            subst queries
            have back := (returned s replies.symm).1
            rw [accepts, back, trace.sessions]
            exact Nat.lt_succ_self _
        · rcases List.mem_append.mp found with old | new
          · have earlier := trace.below raw' t.accept old
            rw [marks (Nat.ne_of_gt earlier)]
            exact trace.selected raw' old
          · have same := List.mem_singleton.mp new
            injection same with queries replies
            injection queries with queries
            injection queries with queries
            injection queries with queries
            subst queries
            have back := returned t.accept replies.symm
            exact back.2 (by rw [← trace.sessions]; exact back.1.symm)
        · rcases List.mem_append.mp found with old | new
          · exact trace.bundles k bytes old
          · cases List.mem_singleton.mp new
    | build session payload =>
        have prog := idealReg_support setup codec route checks t p created ⟨.build session payload, trivial⟩ x result member
        obtain ⟨accepts, marks, sessions, owners⟩ := prog_build setup codec route checks t p _ created session payload _
          _ prog
        dsimp only [detach] at *
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.build session payload))) trivial _ sessions
          (by rw [owners]; exact trace.owners) accepts marks
    | finish owner raw =>
        have prog := idealReg_support setup codec route checks t p created ⟨.finish owner raw, trivial⟩ x result member
        obtain ⟨accepts, marks, sessions, owners⟩ := prog_finish setup codec route checks t p _ created owner raw _ _ prog
        replace owners := owners trace.owners
        dsimp only [detach] at *
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.finish owner raw))) trivial _ sessions owners accepts marks
    | hmac key message =>
        have prog := idealReg_support setup codec route checks t p created ⟨.hmac key message, trivial⟩ x result member
        obtain ⟨backend, sessions, owners⟩ := prog_hmac setup codec route checks t p _ created key message _ _ prog
        dsimp only [detach] at *
        change result.2.backend.2.2 = x.backend.2.2 at backend
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.hmac key message))) trivial _ sessions
          (by rw [owners]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | hash bytes =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have lowered := onNative_native _ x.base result.1 result.2.base native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.hash bytes))) trivial _
          (reg_sessions setup codec checks created.seed (.hash bytes) (fun _ same => by cases same) x.base.native
            (result.1, result.2.base.native) lowered)
          (by rw [reg_shared_owners setup codec checks created.seed (.hash bytes) trivial x.base.native
            (result.1, result.2.base.native) lowered]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | serverSend keyId plaintext =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.serverStep_fields setup codec route _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.serverSend keyId plaintext))) trivial _ fields.2.2.2.2.1
          (by rw [fields.1]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | serverRaw raw =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.serverStep_fields setup codec route _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.serverRaw raw))) trivial _ fields.2.2.2.2.1
          (by rw [fields.1]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | beaconSend owner plaintext =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.beaconStep_fields setup codec owner _ x.base _ native
        have alike := PqxdhDeploymentEligibility.beaconStep_alike setup codec owner _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.beaconSend owner plaintext))) trivial _ fields.2.2.2.2.1
          (poolOwners_alike _ _ _ alike trace.owners) (by rw [backend]) (by rw [backend])
    | beaconRaw owner raw =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.beaconStep_fields setup codec owner _ x.base _ native
        have alike := PqxdhDeploymentEligibility.beaconStep_alike setup codec owner _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.beaconRaw owner raw))) trivial _ fields.2.2.2.2.1
          (poolOwners_alike _ _ _ alike trace.owners) (by rw [backend]) (by rw [backend])

/-- A native-interface program that issues only coins and sends, run under the handler with any registration handler, keeps the backend, the session counter and every owner's view. -/
theorem coinSend_keeps {Bk : Type} {n : ℕ} {Value : Type} (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n)
    (program : OracleComp PqxdhDeploymentInterface.Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (x : XState KemSK Bk n) (result : Value × XState KemSK Bk n)
    (member : result ∈ support ((simulateQ (handlerWith setup codec route reg) program).run x)) :
    result.2.backend = x.backend ∧ result.2.base.native.shared.2.sessions = x.base.native.shared.2.sessions ∧
      PqxdhDeploymentEligibility.Alike x.base.native result.2.base.native := by
  induction program using OracleComp.inductionOn generalizing x with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, PqxdhDeploymentEligibility.alike_refl _⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨⟨reply, middle⟩, first, second⟩ := member
      have firstKept : middle.backend = x.backend ∧
          middle.base.native.shared.2.sessions = x.base.native.shared.2.sessions ∧
          PqxdhDeploymentEligibility.Alike x.base.native middle.base.native := by
        rcases query with coin | command
        · simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at first
          obtain ⟨_, _, same⟩ := first
          cases same
          exact ⟨rfl, rfl, PqxdhDeploymentEligibility.alike_refl _⟩
        · cases command with
          | serverSend kid plaintext =>
              obtain ⟨backend, native⟩ := onBase_support _ x _ first
              exact ⟨backend, (PqxdhDeploymentNative.serverStep_fields setup codec route _ x.base _ native).2.2.2.2.1,
                PqxdhDeploymentEligibility.serverStep_alike setup codec route _ x.base _ native⟩
          | beaconSend index plaintext =>
              obtain ⟨backend, native⟩ := onBase_support _ x _ first
              exact ⟨backend, (PqxdhDeploymentNative.beaconStep_fields setup codec index _ x.base _ native).2.2.2.2.1,
                PqxdhDeploymentEligibility.beaconStep_alike setup codec index _ x.base _ native⟩
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      obtain ⟨backend, sessions, alike⟩ := ih reply restBound middle second
      exact ⟨backend.trans firstKept.1, sessions.trans firstKept.2.1,
        PqxdhDeploymentEligibility.alike_trans _ _ _ firstKept.2.2 alike⟩

/-- The ideal registration's handler composed with the secrecy layer, on the product of the ledger and the extended state. -/
noncomputable def ledgerHandler (bounds : PqxdhDeploymentInterface.FreshBounds) (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl PqxdhDeploymentInterface.FullSpec
      (StateT (PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk TableState) 2) ProbComp) :=
  ((handlerWith setup codec route (idealReg setup codec route checks t p created)).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)).flattenStateT

/-- Every query of the complete interface keeps the trace invariant between the ledger's transcript and the extended state. -/
theorem query_trace (bounds : PqxdhDeploymentInterface.FreshBounds) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk TableState) 2)
    (trace : KeyTrace setup codec checks t p state.1.transcript state.2.base state.2.backend.2.2)
    (result : PqxdhDeploymentInterface.FullSpec.Range query ×
      (PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk TableState) 2))
    (member : result ∈ support ((ledgerHandler setup codec route checks t p bounds created query).run state)) :
    KeyTrace setup codec checks t p result.2.1.transcript result.2.2.base result.2.2.backend.2.2 := by
  rcases state with ⟨ledger, x⟩
  change result ∈ support ((fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)).run x)
    at member
  rw [support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at reachedMember
    obtain ⟨answer, answerMember, rfl⟩ := reachedMember
    exact handler_trace setup codec route checks t p created request ledger.transcript x trace answer answerMember
  · have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds
        (.inr secrecy)).run ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (handlerWith setup codec route
        (idealReg setup codec route checks t p created)) _ x
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, reachedMember, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      ledger reached.1 value
    obtain ⟨backend, sessions, alike⟩ := coinSend_keeps setup codec route _ _
      (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy ledger) x reached
      reachedMember
    change KeyTrace setup codec checks t p reached.1.2.transcript reached.2.base reached.2.backend.2.2
    rw [recorded]
    exact keyTrace_quiet setup codec checks t p ledger.transcript _ _ _ _ trace (.inr secrecy) trivial _ sessions
      (poolOwners_alike _ _ _ alike trace.owners) (by rw [backend]) (by rw [backend])

/-- The trace invariant holds at the start of the experiment: empty transcript, the initial deployment state and the initial ideal backend. -/
theorem keyTrace_initial (created : PqxdhLiveServerConstruction.Created Unit) :
    KeyTrace setup codec checks t p [] (PqxdhDeploymentNative.initial created) PqxdhDeploymentIdealSteps.IdealCore.initial := by
  refine ⟨?_, (fun _ _ found => nomatch found), (fun _ found => nomatch found), ?_, (fun _ _ found => nomatch found)⟩
  · rfl
  · intro j owner pk pair found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found

/-- On every outcome of the common deployment experiment with the ideal registration at a target and draws, the trace invariant holds between the final transcript and the final extended state. -/
theorem game_trace {A X : Type} (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK (IdealBk TableState) 2) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.idealInit
      (idealReg setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (final : XState KemSK (IdealBk TableState) 2)
    (reached : outcome.1 = some (created, output, ledger, final)) :
    KeyTrace setup codec checks t p ledger.transcript final.base final.backend.2.2 := by
  simp only [PqxdhDeploymentBackend.gameWith, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    simp only [Option.some.injEq, Prod.mk.injEq] at reached
    obtain ⟨-, -, rfl, rfl⟩ := reached
    have flatEq := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (handlerWith setup codec route (idealReg setup codec route checks t p constructed))
      (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)
      (PqxdhDeploymentInterface.asModeO mode adversary) PqxdhDeploymentSecrecy.Ledger.empty
      (PqxdhDeploymentBackend.xinitial constructed (PqxdhDeploymentIdealSteps.idealInit constructed))
    simp only [StateT.run] at flatEq
    simp only [PqxdhDeploymentSecrecy.wrap, StateT.run] at executedMember
    rw [flatEq, support_map] at executedMember
    obtain ⟨flat, flatMember, rfl⟩ := executedMember
    exact OracleComp.simulateQ_run_preserves_inv_of_query (ledgerHandler setup codec route checks t p bounds constructed)
      (fun state => KeyTrace setup codec checks t p state.1.transcript state.2.base state.2.backend.2.2)
      (fun query state trace result member => query_trace setup codec route checks t p bounds constructed query state
        trace result member)
      _ _ (keyTrace_initial setup codec checks t p constructed) flat flatMember

/-- The key match of the ideal registration (design-v2 section 7.2, `ideal_keymatch`; the analogue of `PqxdhDeploymentKemTransfer.keymatch_point`): on every outcome of the common deployment experiment with the ideal registration at a target and draws, under `Phase1ReadBack`, a public designation of the target's raw-accept ordinal and KEM creation index on the final transcript implies that the selected session is marked. The designation names accept bytes of the selected session that verify to owner `k`'s published PQ key, which is pool entry `k`, the selected key, so the selected accept reached its encapsulation with the key match and its session was marked at the hidden root read. -/
theorem ideal_keymatch {A X : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (serverKid : Std.U64) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK (IdealBk TableState) 2) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.idealInit
      (idealReg setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (final : XState KemSK (IdealBk TableState) 2)
    (reached : outcome.1 = some (created, output, ledger, final)) (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto codec serverKid ledger.transcript handle =
      some (t.accept, t.kem.val)) :
    final.backend.2.2.marks.isSome := by
  have trace := game_trace setup codec route checks t p ensureInit identityIndex bounds mode adversary runtime outcome
    supported created output ledger final reached
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto codec serverKid ledger.transcript handle t.accept
      t.kem.val designated
  obtain ⟨value, verified, marked⟩ := trace.selected raw
    (PqxdhDeploymentKemTransfer.acceptOf_mem ledger.transcript t.accept raw rawFound)
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw value verified
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := trace.bundles t.kem.val bytes
    (PqxdhDeploymentKeyMatch.bundleOf_mem ledger.transcript t.kem.val bytes bytesFound)
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  apply marked
  rw [← pqFound]
  exact pooled p.chosen (PqxdhDeploymentIdealParams.pool_kem t p)

/-- The key match in the form of the CE target (`PqxdhDeploymentKemTransfer.target`): on every outcome of the common deployment experiment with the ideal registration at the target of a CE designation `g`, if the claim on the observation designates `g`, the selected session is marked. -/
theorem target_marked {A X : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (budget : PqxdhDeploymentInterface.Budget) (g : Fin budget.accept × Fin budget.capacity)
    (p' : Params KemSK budget.create) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK (IdealBk TableState) 2) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.idealInit
      (idealReg setup codec route checks (Target.ofCE budget g) p') ensureInit identityIndex bounds mode adversary).run
        runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (final : XState KemSK (IdealBk TableState) 2)
    (reached : outcome.1 = some (created, output, ledger, final))
    (claim : PqxdhDeploymentKemTransfer.Observed X → Option PqxdhDeploymentInterface.Handle)
    (chosen : PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim
      (output, ledger, final.base.produced) = some g) :
    final.backend.2.2.marks.isSome := by
  obtain ⟨handle, -, designatedIn⟩ := Option.bind_eq_some_iff.mp chosen
  exact ideal_keymatch setup codec route checks (Target.ofCE budget g) p' phase1 setup.serverKeyId ensureInit
    identityIndex bounds mode adversary runtime outcome supported created output ledger final reached handle
    (PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto codec setup.serverKeyId budget _ handle g
      designatedIn)

/-- Every request of the handler with the ideal registration never lowers the accept counter, and keeps the mark unless it is the raw accept at the selected ordinal. -/
theorem handler_core (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK (IdealBk TableState) 2)
    (result : PqxdhDeploymentInterface.Spec.Range query × XState KemSK (IdealBk TableState) 2)
    (member : result ∈ support ((handlerWith setup codec route (idealReg setup codec route checks t p created)
      query).run x)) :
    x.backend.2.2.accepts ≤ result.2.backend.2.2.accepts ∧
      (x.backend.2.2.accepts ≠ t.accept → result.2.backend.2.2.marks = x.backend.2.2.marks) := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨le_refl _, fun _ => rfl⟩
  · cases command with
    | create pin keyId =>
        have prog := idealReg_support setup codec route checks t p created ⟨.create pin keyId, trivial⟩ x result member
        have backend := (prog_create setup codec route checks t p _ created pin keyId _ _ prog).1
        change result.2.backend.2.2 = x.backend.2.2 at backend
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | bundle k =>
        have prog := idealReg_support setup codec route checks t p created ⟨.bundle k, trivial⟩ x result member
        have backend := (prog_bundle setup codec route checks t p _ created k _ _ prog).1
        change result.2.backend.2.2 = x.backend.2.2 at backend
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | accept raw =>
        have prog := idealReg_support setup codec route checks t p created ⟨.accept raw, trivial⟩ x result member
        obtain ⟨accepts, -, -, marks, -⟩ := prog_accept setup codec route checks t p _ created raw _ _ prog
        change result.2.backend.2.2.accepts = x.backend.2.2.accepts + 1 at accepts
        exact ⟨by rw [accepts]; exact Nat.le_succ _, marks⟩
    | build session payload =>
        have prog := idealReg_support setup codec route checks t p created ⟨.build session payload, trivial⟩ x result
          member
        obtain ⟨accepts, marks, -, -⟩ := prog_build setup codec route checks t p _ created session payload _ _ prog
        exact ⟨le_of_eq accepts.symm, fun _ => marks⟩
    | finish owner raw =>
        have prog := idealReg_support setup codec route checks t p created ⟨.finish owner raw, trivial⟩ x result member
        obtain ⟨accepts, marks, -, -⟩ := prog_finish setup codec route checks t p _ created owner raw _ _ prog
        exact ⟨le_of_eq accepts.symm, fun _ => marks⟩
    | hmac key message =>
        have prog := idealReg_support setup codec route checks t p created ⟨.hmac key message, trivial⟩ x result member
        have backend := (prog_hmac setup codec route checks t p _ created key message _ _ prog).1
        change result.2.backend.2.2 = x.backend.2.2 at backend
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | hash bytes =>
        have backend := (onBase_support _ x result member).1
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | serverSend keyId plaintext =>
        have backend := (onBase_support _ x result member).1
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | serverRaw raw =>
        have backend := (onBase_support _ x result member).1
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | beaconSend owner plaintext =>
        have backend := (onBase_support _ x result member).1
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩
    | beaconRaw owner raw =>
        have backend := (onBase_support _ x result member).1
        exact ⟨by rw [backend], fun _ => by rw [backend]⟩

/-- After the selected ordinal (the accept counter beyond it), no run of the handler with the ideal registration changes the mark. -/
theorem run_settled {α : Type} (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp PqxdhDeploymentInterface.Spec α) (x : XState KemSK (IdealBk TableState) 2)
    (beyond : t.accept < x.backend.2.2.accepts) :
    ∀ result ∈ support ((simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
      work).run x), result.2.backend.2.2.marks = x.backend.2.2.marks := by
  intro result member
  exact (PqxdhDeploymentIdealSlots.simulateQ_keeps _
    (fun state : XState KemSK (IdealBk TableState) 2 => t.accept < state.backend.2.2.accepts ∧
      state.backend.2.2.marks = x.backend.2.2.marks)
    (fun query state good after afterMember => by
      obtain ⟨grows, kept⟩ := handler_core setup codec route checks t p created query state after afterMember
      exact ⟨lt_of_lt_of_le good.1 grows, (kept (Nat.ne_of_gt good.1)).trans good.2⟩)
    work x ⟨beyond, rfl⟩ result member).2

/-- The raw accept at the selected ordinal on bytes whose verification does not yield the selected PQ key is the logged accept: it advances the accept counter and leaves no mark. -/
theorem handler_accept_inactive (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes)
    (inactive : ∀ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
      value.keys.pqKey ≠ p.chosen.1)
    (x : XState KemSK (IdealBk TableState) 2) (selected : x.backend.2.2.accepts = t.accept)
    (result : Option ℕ × XState KemSK (IdealBk TableState) 2)
    (member : result ∈ support ((handlerWith setup codec route (idealReg setup codec route checks t p created)
      (.inr (.accept raw))).run x)) :
    result.2.backend.2.2.accepts = t.accept + 1 ∧ result.2.backend.2.2.marks = none := by
  have prog := idealReg_support setup codec route checks t p created ⟨.accept raw, trivial⟩ x result member
  have accepts := PqxdhDeploymentIdealSteps.acceptStep_accepts setup codec route checks t p created raw _ _ prog
  change result.2.backend.2.2.accepts = x.backend.2.2.accepts + 1 at accepts
  refine ⟨by rw [accepts, selected], ?_⟩
  change (result.1, detach result.2) ∈ support (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created
    raw (detach x)) at prog
  unfold PqxdhDeploymentIdealSteps.acceptStep at prog
  have chosenCounter : (detach x).backend.accepts = t.accept := selected
  simp only [chosenCounter, ↓reduceIte] at prog
  rw [support_map] at prog
  obtain ⟨inner, innerMember, same⟩ := prog
  rw [PqxdhDeploymentIdealSteps.acceptExposed_logged setup codec checks created.seed p.chosen p.challenge raw inactive,
    support_map, support_liftComp] at innerMember
  obtain ⟨logged, -, rfl⟩ := innerMember
  have marks := congrArg (fun state : Option ℕ × XState KemSK IdealCore 2 => state.2.backend.marks) same
  exact marks.symm

end Trace

end BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.poolOwners_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.poolOwners_alike

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.poolOwners_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.poolOwners_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.terminal_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.terminal_kem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.poolOwners_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.poolOwners_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_sessions

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.nativeOwner_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.nativeOwner_kem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_shared_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.reg_shared_owners

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.keeps_any' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.keeps_any

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.tailCE_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.tailCE_client

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.tailCE_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.tailCE_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.program_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.program_marker

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.acceptInactive_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.acceptInactive_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.acceptActive_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.acceptActive_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.acceptExposed_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.acceptExposed_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.realRegAt_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.realRegAt_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.onNative_native' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.onNative_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.createPool_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.createPool_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.buildHidden_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.buildHidden_sessions

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.groupCE_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.groupCE_sessions

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.finishChallenge_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.finishChallenge_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.prog_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.quiet_entry' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.quiet_entry

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.keyTrace_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.keyTrace_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.slotCore_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.slotCore_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.onBase_support' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.onBase_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.idealReg_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.idealReg_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.handler_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.handler_trace

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.coinSend_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.coinSend_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.query_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.query_trace

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.keyTrace_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.keyTrace_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.game_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.game_trace

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.ideal_keymatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.ideal_keymatch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.target_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.target_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.handler_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.handler_core

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.run_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.run_settled

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.handler_accept_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch.handler_accept_inactive
