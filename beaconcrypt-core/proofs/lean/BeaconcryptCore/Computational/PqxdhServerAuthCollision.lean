import BeaconcryptCore.Computational.PqxdhServerAuthAssumptions
import BeaconcryptCore.Computational.PqxdhServerAuthGapDh

/-!
# Server authentication: collisions of actual session root inputs

The collision analysis uses the approved scalar-spread contract at the Server's actual uniform ephemeral draw. Equal 192-byte root inputs have equal DH3 bytes at offset 96. The verified peer supplying that DH3 is fixed before the draw; all later rejection and encapsulation outcomes remain in the original continuation. Every accept attempt is counted, including rejection and unbuilt pending sessions. No draw is conditioned on acceptance, and this module does not prove primitive internals.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCollision
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthAssumptions
open PqxdhServerAuthExperiment

/-- Evaluating a pure state callback returns the original complete state. -/
theorem state_pure {σ α : Type} (value : α) (state : σ) :
    (pure value : StateT σ ProbComp α) state = pure (value, state) := rfl

/-- Evaluating a stateful bind retains the complete intermediate state. -/
theorem state_bind {σ α β : Type} (work : StateT σ ProbComp α)
    (next : α → StateT σ ProbComp β) (state : σ) :
    (work >>= next) state = work state >>= fun result => next result.1 result.2 := rfl

/-- Lifting probabilistic work preserves the complete ambient state. -/
theorem state_lift {σ α : Type} (work : ProbComp α) (state : σ) :
    (StateT.lift work : StateT σ ProbComp α) state =
      work >>= fun value => pure (value, state) := rfl

/-- A fixed nonzero DH output has probability at most 64/2^256 at the actual scalar draw, directly from the approved functional counting contract. -/
theorem spread_probability (c : Pqxdh.Crypto) (spread : X25519ScalarSpread c)
    (peer : PeerEncoding) (value : DhOutput) (nonzero : value ≠ zeroDh) :
    Pr{let scalar ← sampleScalar}[c.x25519 scalar.toList peer.toList = value.toList] ≤
      (64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞) := by
  rw [sampleScalar, SampleableType.prEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast spread peer value nonzero) _

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual verified Server prefix hits any fixed nonzero third coordinate only at the approved scalar-spread rate. Pre-generation rejection is retained, and later rejection is never conditioned away. -/
theorem verified_third_probability (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto)
    (verified : PqxdhServerRootPreparation.Verified Reader) (consumed : List Pqxdh.Bytes)
    (value : DhOutput) (nonzero : value ≠ zeroDh) :
    Pr{let result ← ((simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
        (serverAux setup codec checks) (fun _ => pure ()))
          (PqxdhServerRootPreparation.collectVerified verified)).run consumed)}[∃ input, result.1 = some input ∧
        absBytes input.third = value.toList] ≤
      (64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞) := by
  classical
  -- The event is decided into a Boolean point mass, so the rejection branches end in the point mass of `false`.
  have prPureFalse : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by
    rw [← prEvent_eq_evalDist_singleton _ true, prEvent_pure]
    simp
  -- Reassociation at the event level: a bare `rw [bind_assoc]` would also rewrite the bind that expands `Pr{...}`.
  have prAssoc : ∀ {α β γ : Type} (x : ProbComp α) (f : α → ProbComp β) (g : β → ProbComp γ) (p : γ → Prop),
      Pr{let y ← (x >>= f >>= g)}[p y] = Pr{let y ← (x >>= fun a => f a >>= g)}[p y] := fun x f g p => by
    rw [bind_assoc x f g]
  rw [prEvent_eq_evalDist_decide]
  simp only [PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, PqxdhServerStaticDhSource.prefixImpl,
    serverAux, StateT.run_bind]
  simp only [StateT.run, Option.elim_some, pure_bind]
  by_cases used : PqxdhServerRootPreparation.registrationId verified ∈ consumed
  · simp only [used, ite_true, OptionT.run_failure, simulateQ_pure]
    change 𝒟[(pure (none, consumed) : ProbComp (Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes
        PeerEncoding) × List Pqxdh.Bytes)) >>= fun result =>
          pure (decide (∃ input, result.1 = some input ∧ absBytes input.third = value.toList))] {true} ≤ _
    simp only [pure_bind, reduceCtorEq, false_and, exists_false, decide_false, prPureFalse]
    exact zero_le
  · simp only [used, ite_false, OptionT.run_bind, OptionT.run_monadLift,
      Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
      PqxdhServerStaticDhSource.prefixImpl, serverAux,
      pure_bind, Option.elim_some]
    cases reserved : checks.reserveRegistration <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
        OptionT.run_failure, simulateQ_pure, state_pure, pure_bind,
        reduceCtorEq, false_and, exists_false, decide_false, prPureFalse]
    · exact zero_le
    cases pre : checks.x25519Point (PqxdhRootTableInitialization.rootArray verified.keys.prekey) <;>
      cases one : checks.x25519Point (PqxdhRootTableInitialization.rootArray verified.keys.oneTime) <;>
      simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, OptionT.run_failure,
        Option.elimM, Option.elim_some, bind_map_left, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, PqxdhServerStaticDhSource.prefixImpl, serverAux,
        state_pure, pure_bind, pre, one, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_true, ite_false, reduceCtorEq,
        false_and, exists_false, decide_false, prPureFalse] <;> try exact zero_le
    rw [← prEvent_eq_evalDist_decide]
    simp only [state_bind, state_lift, generateEphemeral, prAssoc, pure_bind,
      Option.elim_some]
    refine (prEvent_bind_le_prEvent_of_support _ _ (fun scalar : ScalarBytes =>
      setup.source.crypto.x25519 scalar.toList verified.keys.prekey.toList = value.toList) _ ?_).trans
        (spread_probability setup.source.crypto spread verified.keys.prekey value nonzero)
    intro scalar _ unequal
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported accepted
    obtain ⟨input, hasInput, third⟩ := accepted
    generalize thirdField : input.third = thirdWord at third
    simp only [
      simulateQ_bind, simulateQ_spec_query,
      PqxdhServerStaticDhSource.prefixImpl, serverAux,
      state_bind, state_pure, pure_bind] at supported
    cases validKem : checks.kemKey verified.keys.pqKey <;>
      simp only [validKem, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
        OptionT.run_failure, simulateQ_pure, state_pure, support_pure,
        Set.mem_singleton_iff] at supported
    · rw [supported] at hasInput
      cases hasInput
    simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, Option.elimM,
      bind_map_left, simulateQ_bind, simulateQ_spec_query,
      PqxdhServerStaticDhSource.prefixImpl, serverAux,
      state_bind, state_lift, bind_assoc, pure_bind, mem_support_bind_iff] at supported
    obtain ⟨encapsulated, _, supported⟩ := supported
    cases encapsulated <;>
      simp only [Option.elim_none, Option.elim_some, simulateQ_pure, state_pure,
        support_pure, Set.mem_singleton_iff] at supported
    · rw [supported] at hasInput
      cases hasInput
    simp only [

      simulateQ_bind, simulateQ_spec_query,
      PqxdhServerStaticDhSource.prefixImpl, serverAux,
      state_bind, state_pure, pure_bind] at supported
    cases converted : (setup.source.crypto.xpkConv verified.identity.toList).bind toWord32 <;>
      simp only [converted, Option.elim_none, Option.elim_some, simulateQ_pure,
        state_pure, support_pure, Set.mem_singleton_iff] at supported
    · rw [supported] at hasInput
      cases hasInput
    simp only [OptionT.run_bind, OptionT.run_mk,
      Option.elimM,
      simulateQ_bind, simulateQ_spec_query,
      PqxdhServerStaticDhSource.prefixImpl, serverAux,
      state_bind, state_pure, pure_bind,
      Bool.not_true, Bool.false_eq_true, ite_false] at supported
    repeat' first
      | (simp only [OptionT.run_pure, Option.elim, Option.map,
          simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
          PqxdhServerStaticDhSource.prefixImpl, serverAux, state_bind, state_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at supported)
      | (split at supported)
    all_goals rw [supported] at hasInput
    all_goals cases hasInput
    have dh3 : (sourceScalarDh setup.source.crypto scalar
        (PqxdhPhase2GapDhSource.peer (PqxdhRootTableInitialization.rootArray verified.keys.prekey))).map
          PqxdhRootTableInitialization.rootArray = some thirdWord := by
      rwa [← thirdField]
    obtain ⟨typed, actual, interpreted⟩ := Option.map_eq_some_iff.mp dh3
    rw [← interpreted, PqxdhRootTableInitialization.rootArray_bytes] at third
    simp only [sourceScalarDh] at actual
    split at actual
    · cases actual
    · apply unequal
      have raw := congrArg List.Vector.toList (Option.some.inj actual)
      simpa only [PqxdhPhase2GapDhSource.peer, PqxdhRootTableInitialization.rootArray_bytes,
        List.Vector.toList_mk] using
        raw.trans third

/-- Arbitrary raw Phase 1 decoding and verification precede the same uniform draw; malformed input and all rejected continuations retain their original probability. -/
theorem prefix_third_probability (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto)
    (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (value : DhOutput) (nonzero : value ≠ zeroDh) :
    Pr{let result ← ((serverPrefix setup codec checks raw).run consumed)}[∃ input, result.1 = some input ∧
        absBytes input.third = value.toList] ≤
      (64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞) := by
  classical
  simp only [serverPrefix, PqxdhServerRootPreparation.collect, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro verified _
  cases verified.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, reduceCtorEq,
        false_and, exists_false, ite_false]
      exact zero_le
  | some input => exact verified_third_probability setup codec checks spread input verified.2 value nonzero

/-- The same actual prefix has the finite-union bound against any previously fixed list of nonzero third coordinates. The list can be chosen from the entire prior adaptive history. -/
theorem prefix_thirds_probability (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto)
    (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (values : List DhOutput) (nonzero : ∀ value ∈ values, value ≠ zeroDh) :
    Pr{let result ← ((serverPrefix setup codec checks raw).run consumed)}[∃ input, result.1 = some input ∧
        ∃ value ∈ values, absBytes input.third = value.toList] ≤
      (values.length : ℝ≥0∞) * ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞)) := by
  induction values with
  | nil =>
      simp only [List.not_mem_nil, false_and, exists_false, and_false, List.length_nil, Nat.cast_zero, zero_mul,
        prEvent_false, le_refl]
  | cons value rest ih =>
      have splitEvent : ∀ result : Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) ×
          List Pqxdh.Bytes, (∃ input, result.1 = some input ∧
            ∃ target ∈ value :: rest, absBytes input.third = target.toList) ↔
          ((∃ input, result.1 = some input ∧ absBytes input.third = value.toList) ∨
            (∃ input, result.1 = some input ∧ ∃ target ∈ rest, absBytes input.third = target.toList)) := by
        intro result
        simp only [List.mem_cons, exists_eq_or_imp, and_or_left, exists_or]
      rw [prEvent_congr _ _ _ splitEvent]
      apply (prEvent_or_le _ _ _).trans
      have headBound := prefix_third_probability setup codec checks spread raw consumed value
        (nonzero value (List.mem_cons_self))
      have tailBound := ih (fun target member => nonzero target (List.mem_cons_of_mem value member))
      calc
        _ ≤ _ + _ := add_le_add headBound tailBound
        _ = _ := by rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]; exact add_comm _ _

/-- The actual chronological session touches with a nonzero known DH3 coordinate, retaining the allocated attempt index. Beacon and public-query touches contribute no entry. -/
def thirds (touches : List Touch) : List (Nat × DhOutput) := touches.filterMap fun touch =>
  match touch with
  | .session index message _ => match message.third with
    | .known value => if value = zeroDh then none else some (index, value)
    | .selected _ => none
  | _ => none

/-- The source history projection respects exact chronological append. -/
theorem thirds_append (left right : List Touch) : thirds (left ++ right) = thirds left ++ thirds right := by
  exact List.filterMap_append

/-- Every retained coordinate is nonzero by the projection's explicit filter. -/
theorem thirds_nonzero (touches : List Touch) (entry : Nat × DhOutput) (member : entry ∈ thirds touches) :
    entry.2 ≠ zeroDh := by
  obtain ⟨touch, touchMember, found⟩ := List.mem_filterMap.mp member
  cases touch with
  | session index message root =>
    cases third : message.third with
    | known value =>
      simp only [third] at found
      split at found
      · cases found
      · cases found
        assumption
    | selected peer =>
      simp only [third] at found
      cases found
  | beacon message => cases found
  | adversary bytes => cases found

/-- Collision of retained nonzero DH3 coordinates belonging to distinct allocated attempts. This is an overapproximation of the target-Beacon same-input event. -/
def Collision (entries : List (Nat × DhOutput)) : Prop :=
  ∃ i j value, i ≠ j ∧ (i, value) ∈ entries ∧ (j, value) ∈ entries

/-- Appending one actual attempt creates a collision only by matching a prior coordinate; both endpoints cannot be the new attempt. -/
theorem collision_append (entries : List (Nat × DhOutput)) (index : Nat) (value : DhOutput)
    (noCollision : ¬ Collision entries) (collision : Collision (entries ++ [(index, value)])) :
    value ∈ entries.map Prod.snd := by
  obtain ⟨i, j, output, different, left, right⟩ := collision
  simp only [List.mem_append, List.mem_singleton] at left right
  rcases left with left | left <;> rcases right with right | right
  · exact (noCollision ⟨i, j, output, different, left, right⟩).elim
  · cases right
    exact List.mem_map_of_mem left
  · cases left
    exact List.mem_map_of_mem right
  · cases left
    cases right
    exact (different rfl).elim

/-- The source local zero test ensures its recorded third coordinate survives the nonzero history projection. -/
theorem input_third_nonzero (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (valid : PqxdhServerRelatedRootInput.localNonzero input) :
    PqxdhPhase2InputBytes.word input.third ≠ zeroDh := by
  intro same
  exact valid.2.1 (congrArg List.Vector.toList same)

/-- A source root request contributes exactly its allocated index and actual nonzero DH3, independent of whether the root endpoint replies successfully. -/
theorem thirds_input (index : Nat) (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (valid : PqxdhServerRelatedRootInput.localNonzero input) (reply : Option PqxdhSecretInputKdf.RootOutput) :
    thirds [.session index (PqxdhServerRelatedRootInput.message input) reply] =
      [(index, PqxdhPhase2InputBytes.word input.third)] := by
  simp only [thirds, List.filterMap_cons, List.filterMap_nil,
    PqxdhServerRelatedRootInput.message, PqxdhJointDhExtractRoot.serverMessage,
    input_third_nonzero input valid, ite_false]

/-- Equality of root-input bytes fixes the actual DH3 coordinate at offset 96. No public-key or KDF-output injectivity is used. -/
theorem root_input_third (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (bytes : Pqxdh.Bytes)
    (found : rootInput setup seed scalar (PqxdhServerRelatedRootInput.message input) = some bytes) :
    readDh 96 bytes = some (PqxdhPhase2InputBytes.word input.third) := by
  unfold rootInput PqxdhServerRelatedRootInput.message at found
  rw [PqxdhJointDhExtractRoot.server_input] at found
  cases actual : setup.joint.staticDh seed
      (PqxdhPhase2GapDhSource.peer (PqxdhRootTableInitialization.rootArray input.verified.keys.prekey)) with
  | none => simp only [actual, Option.map_none] at found; cases found
  | some first =>
      simp only [actual, Option.map_some, Option.some.injEq] at found
      rw [← found]
      exact PqxdhJointGapDh.read_third _ _ _

/-- An actual nonzero source-session touch appears in the projected history with its own attempt index. -/
theorem thirds_mem_input (touches : List Touch) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (valid : PqxdhServerRelatedRootInput.localNonzero input) (reply : Option PqxdhSecretInputKdf.RootOutput)
    (member : Touch.session index (PqxdhServerRelatedRootInput.message input) reply ∈ touches) :
    (index, PqxdhPhase2InputBytes.word input.third) ∈ thirds touches := by
  apply List.mem_filterMap.mpr
  refine ⟨_, member, ?_⟩
  simp only [PqxdhServerRelatedRootInput.message, PqxdhJointDhExtractRoot.serverMessage,
    input_third_nonzero input valid, ite_false]

/-- The original target-Beacon collision event entails a collision of two retained actual DH3 values. Only the already-proved operational session-origin invariant is used. -/
theorem collB_thirds (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (state : GameState KemSK)
    (invariant : GameInv Reader Response setup publicValue state)
    (collided : CollB setup seed scalar state.ghost) : Collision (thirds state.ghost.touches) := by
  obtain ⟨i, j, left, right, ri, rj, bytes, different, leftMem, rightMem, _, leftInput, rightInput⟩ := collided
  obtain ⟨inputI, rfl, _, validI⟩ := invariant.sessionOrigin i left ri leftMem
  obtain ⟨inputJ, rfl, _, validJ⟩ := invariant.sessionOrigin j right rj rightMem
  have same : PqxdhPhase2InputBytes.word inputI.third = PqxdhPhase2InputBytes.word inputJ.third :=
    Option.some.inj ((root_input_third setup seed scalar inputI bytes leftInput).symm.trans
      (root_input_third setup seed scalar inputJ bytes rightInput))
  refine ⟨i, j, PqxdhPhase2InputBytes.word inputI.third, different,
    thirds_mem_input _ i inputI validI ri leftMem, ?_⟩
  rw [same]
  exact thirds_mem_input _ j inputJ validJ rj rightMem

/-- Literal continuation of an accept after the ordered prefix, including token rejection and publication to the pending-token map. -/
noncomputable def acceptTail (index : Nat) (serverBinding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) : Game KemSK (Option Nat) := do
  let returned ← simulateQ (sessionImpl index) (PqxdhServerRelatedRootConsumer.client serverBinding input)
  match returned with
  | .ok (some token) => do
      modify fun current => { current with pending := Function.update current.pending index (some token) }
      pure (some index)
  | _ => pure none

/-- Splitting only at the actual prefix return preserves the entire source accept program and source generator order. -/
theorem accept_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) :
    acceptOracle setup codec checks publicValue raw = (do
      let state ← get
      let collected ← liftCoins ((serverPrefix setup codec checks raw).run state.server.consumed)
      set { state with sessions := state.sessions + 1, server := { state.server with consumed := collected.2 } }
      match collected.1 with
      | none => pure none
      | some input => acceptTail state.sessions (binding setup publicValue) input) := rfl

open Classical in
/-- The original post-prefix tail appends exactly the reached valid source coordinate; failed root replies and token publication do not erase that attempt. -/
theorem acceptTail_thirds (index : Nat) (serverBinding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptTail index serverBinding input).run state)) :
    thirds result.2.ghost.touches = if PqxdhServerRelatedRootInput.localNonzero input then
      thirds state.ghost.touches ++ [(index, PqxdhPhase2InputBytes.word input.third)]
    else thirds state.ghost.touches := by
  classical
  simp only [acceptTail, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨returned, source, supported⟩ := supported
  obtain ⟨consumed, extra, same, shape, _⟩ := client_run index serverBinding input state returned source
  have projection : thirds returned.2.ghost.touches = if PqxdhServerRelatedRootInput.localNonzero input then
      thirds state.ghost.touches ++ [(index, PqxdhPhase2InputBytes.word input.third)]
    else thirds state.ghost.touches := by
    rw [same]
    rcases shape with ⟨invalid, rfl⟩ | ⟨valid, reply, rfl⟩
    · simp only [invalid, ite_false, List.append_nil]
    · rw [ite_eq_left valid, thirds_append, thirds_input index input valid reply]
  rcases returned with ⟨outcome, after⟩
  dsimp only at projection
  rcases outcome with (_ | token) | error | _
  all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  all_goals subst supported
  all_goals exact projection

/-- The same restricted-Extract interpreter used by the original experiment. -/
noncomputable def family (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) :=
  PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
    PqxdhJointDhExtractRoot.reduction

/-- Evaluate the original source program while retaining both full source state and the shared family cache/history. -/
noncomputable def evaluate (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (work : Game KemSK α) :
    StateT (GameState KemSK × PqxdhJointDhExtractFamily.State) ProbComp α :=
  PqxdhSelectedStateInterpreter.evaluate (family setup seed scalar) work

/-- The evaluated source handler is exactly the existing fused adaptive handler. -/
theorem fused_evaluate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) :
    PqxdhServerAuthGapDh.fusedImpl setup codec checks publicValue beaconSeed seed scalar query =
      evaluate setup seed scalar (authHandler setup codec checks publicValue beaconSeed query) := rfl

/-- Answering the actual family services can only reach outcomes supported by the original source program. -/
theorem evaluate_support (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (work : Game KemSK α) (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : α × (GameState KemSK × PqxdhJointDhExtractFamily.State))
    (supported : result ∈ support ((evaluate setup seed scalar work).run state)) :
    (result.1, result.2.1) ∈ support (work.run state.1) := by
  change result ∈ support (PqxdhSelectedStateInterpreter.pair <$>
    (simulateQ (family setup seed scalar) (work.run state.1)).run state.2) at supported
  rw [support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  apply OracleComp.support_simulateQ_run'_subset (family setup seed scalar)
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ reached

/-- The interpreter forwards all source-prefix coins unchanged, without exposing or altering either retained state. -/
theorem evaluate_coins (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α : Type} (work : ProbComp α) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (evaluate setup seed scalar (liftCoins work)).run state = (fun value => (value, state)) <$> work := by
  change PqxdhSelectedStateInterpreter.pair <$>
    (simulateQ (family setup seed scalar) ((liftCoins work : Game KemSK α).run state.1)).run state.2 = _
  simp only [liftCoins, StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, family, rom_coins,
    Functor.map_map, PqxdhSelectedStateInterpreter.pair]

/-- Evaluation commutes with the entire adaptive continuation, not just the sampler's marginal. -/
theorem evaluate_bind (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    {α β : Type} (work : Game KemSK α) (next : α → Game KemSK β) :
    evaluate setup seed scalar (work >>= next) =
      evaluate setup seed scalar work >>= fun reply => evaluate setup seed scalar (next reply) :=
  PqxdhSelectedStateInterpreter.bind_evaluate _ _ _

/-- The fully interpreted accept keeps the literal prefix sampler before its complete continuation and retains both complete states on every branch. -/
theorem evaluate_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    (evaluate setup seed scalar (acceptOracle setup codec checks publicValue raw)).run state = (do
      let collected ← (serverPrefix setup codec checks raw).run state.1.server.consumed
      let after := { state.1 with sessions := state.1.sessions + 1, server := { state.1.server with consumed := collected.2 } }
      match collected.1 with
      | none => pure (none, (after, state.2))
      | some input => (evaluate setup seed scalar
          (acceptTail state.1.sessions (binding setup publicValue) input)).run (after, state.2)) := by
  change PqxdhSelectedStateInterpreter.pair <$>
    (simulateQ (family setup seed scalar) ((acceptOracle setup codec checks publicValue raw).run state.1)).run
      state.2 = _
  rw [accept_split]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set, liftCoins, StateT.run_lift,
    bind_assoc, simulateQ_bind, map_bind]
  simp only [family, rom_coins, bind_map_left]
  apply bind_congr
  intro collected
  cases collected.1
  · simp only [StateT.run_pure, simulateQ_pure, map_pure, PqxdhSelectedStateInterpreter.pair]
  · rfl

/-- One actual accept creates a new distinct-session DH3 collision with probability at most the number of prior retained attempts times the approved scalar-spread rate. Arbitrary preceding public and private state is retained. -/
theorem accept_collision_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto) (publicValue : PublicChallenge)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (clean : ¬ Collision (thirds state.1.ghost.touches)) :
    Pr{let result ← ((evaluate setup seed scalar (acceptOracle setup codec checks publicValue raw)).run state)}[Collision (thirds result.2.1.ghost.touches)] ≤
      ((thirds state.1.ghost.touches).length : ℝ≥0∞) *
        ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞)) := by
  rw [evaluate_accept]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun collected : Option (PqxdhServerRootPreparation.Inputs Reader
      ScalarBytes PeerEncoding) × List Pqxdh.Bytes => ∃ input, collected.1 = some input ∧
      ∃ value ∈ (thirds state.1.ghost.touches).map Prod.snd, absBytes input.third = value.toList) _ ?_).trans ?_
  · intro collected _ missing
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported collided
    rcases collected with ⟨input, consumed⟩
    cases input with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact clean collided
    | some input =>
        have actual := evaluate_support setup seed scalar
          (acceptTail state.1.sessions (binding setup publicValue) input) _ result supported
        have projected := acceptTail_thirds state.1.sessions (binding setup publicValue) input _ _ actual
        by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
        · rw [ite_eq_left valid] at projected
          rw [projected] at collided
          have member := collision_append (thirds state.1.ghost.touches) state.1.sessions
            (PqxdhPhase2InputBytes.word input.third) clean collided
          exact missing ⟨input, rfl, _, member, rfl⟩
        · rw [ite_eq_right valid] at projected
          rw [projected] at collided
          exact clean collided
  · simpa only [List.length_map] using prefix_thirds_probability setup codec checks spread raw
      state.1.server.consumed ((thirds state.1.ghost.touches).map Prod.snd) (by
        intro value member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact thirds_nonzero _ entry entryMember)

/-- Beacon finishing can record its own root touch but cannot add a Server session coordinate. This retains the original complete finish, optional opening and publication. -/
theorem finish_thirds (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Pqxdh.Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    thirds result.2.ghost.touches = thirds state.ghost.touches := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [hphase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, stageRun, supported⟩ := supported
      obtain ⟨cache, extra, stagedEq, shape⟩ := stage_run setup codec beaconSeed
        publicValue control state.beacon.beacon.identity oneTime kem raw state staged stageRun
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
      rw [Ghost.accept_touches, stagedEq]
      rcases shape with ⟨rfl, _, _⟩ | ⟨pending, _, rfl⟩ <;> simp only [
        thirds, List.filterMap_append, List.filterMap_nil, List.filterMap_cons, List.append_nil]
  | _ =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- Every actual oracle class other than accept leaves the complete ordered Server-DH3 projection unchanged. -/
theorem handler_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (quiet : ¬ IsAcceptQuery query) (state : GameState KemSK)
    (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    thirds result.2.ghost.touches = thirds state.ghost.touches := by
  rcases query with coin | query
  · rw [forward_support _ _ _ supported]
  cases query with
  | accept raw => exact (quiet trivial).elim
  | build session payload => rw [PqxdhServerAuthGapDh.build_touches setup codec checks session payload state result supported]
  | finish raw => exact finish_thirds setup codec publicValue beaconSeed raw state result supported
  | hmac key message =>
      change result ∈ support ((hmacOracle key message).run state) at supported
      simp only [hmacOracle] at supported
      split_ifs at supported with inside
      · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
        rw [record_run, support_pure, Set.mem_singleton_iff] at first
        subst first
        rw [forward_support _ _ _ rest, thirds_append]
        simp only [thirds, List.filterMap_cons, List.filterMap_nil, List.append_nil]
      · rw [forward_support _ _ _ supported]
  | hash bytes =>
      obtain ⟨cache, eq⟩ := hashOracle_step bytes state result supported
      rw [eq]
  | reveal keyId =>
      change result ∈ support (pure _ : OracleComp PqxdhJointDhExtractRoot.RootSpec _) at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- One fully evaluated accept retains the old session list and adds at most one entry, regardless of rejection or later token use. -/
theorem accept_thirds_length (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : Option Nat × (GameState KemSK × PqxdhJointDhExtractFamily.State))
    (supported : result ∈ support ((evaluate setup seed scalar
      (acceptOracle setup codec checks publicValue raw)).run state)) :
    (thirds result.2.1.ghost.touches).length ≤ (thirds state.1.ghost.touches).length + 1 := by
  rw [evaluate_accept, mem_support_bind_iff] at supported
  obtain ⟨⟨collected, consumed⟩, _, supported⟩ := supported
  cases collected with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Nat.le_succ _
  | some input =>
      have actual := evaluate_support setup seed scalar
        (acceptTail state.1.sessions (binding setup publicValue) input) _ result supported
      rw [acceptTail_thirds state.1.sessions (binding setup publicValue) input _ _ actual]
      split
      · simp only [List.length_append, List.length_singleton, le_refl]
      · exact Nat.le_succ _

/-- All non-accept classes preserve the session projection even after the shared family interpreter answers every adaptive query. -/
theorem fused_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) (quiet : ¬ IsAcceptQuery query)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : ServerAuthSpec.Range query × (GameState KemSK × PqxdhJointDhExtractFamily.State))
    (supported : result ∈ support ((PqxdhServerAuthGapDh.fusedImpl setup codec checks publicValue beaconSeed
      seed scalar query).run state)) : thirds result.2.1.ghost.touches = thirds state.1.ghost.touches := by
  rw [fused_evaluate] at supported
  exact handler_quiet setup codec checks publicValue beaconSeed query quiet _ _
    (evaluate_support setup seed scalar _ state result supported)

/-- The complete adaptive interface grows the session list only at actual accept attempts, by at most one each. -/
theorem fused_thirds_length (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : ServerAuthSpec.Range query × (GameState KemSK × PqxdhJointDhExtractFamily.State))
    (supported : result ∈ support ((PqxdhServerAuthGapDh.fusedImpl setup codec checks publicValue beaconSeed
      seed scalar query).run state)) :
    (thirds result.2.1.ghost.touches).length ≤ (thirds state.1.ghost.touches).length +
      if IsAcceptQuery query then 1 else 0 := by
  by_cases accept : IsAcceptQuery query
  · rcases query with coin | query
    · cases accept
    cases query with
    | accept raw =>
      rw [fused_evaluate] at supported
      exact accept_thirds_length setup codec checks publicValue seed scalar raw state result supported
    | _ => cases accept
  · rw [ite_eq_right accept, Nat.add_zero, fused_quiet setup codec checks publicValue beaconSeed seed scalar
      query accept state result supported]

/-- The actual complete oracle step has collision hazard only for accepts; all other adaptive replies preserve the session history. -/
theorem fused_collision_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto) (publicValue : PublicChallenge)
    (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes) (query : ServerAuthSpec.Domain)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (clean : ¬ Collision (thirds state.1.ghost.touches)) :
    Pr{let result ← ((PqxdhServerAuthGapDh.fusedImpl setup codec checks publicValue beaconSeed seed scalar query).run state)}[Collision (thirds result.2.1.ghost.touches)] ≤
      if IsAcceptQuery query then ((thirds state.1.ghost.touches).length : ℝ≥0∞) *
        ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞)) else 0 := by
  by_cases accept : IsAcceptQuery query
  · rcases query with coin | query
    · cases accept
    cases query with
    | accept raw =>
      rw [fused_evaluate]
      exact accept_collision_probability setup codec checks spread publicValue seed scalar raw state clean
    | _ => cases accept
  · rw [ite_eq_right accept]
    apply le_of_eq
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported collided
    rw [fused_quiet setup codec checks publicValue beaconSeed seed scalar query accept state result supported] at collided
    exact clean collided

/-- Number of ordered earlier/later pairs remaining with `n` previous entries and `q` future accept attempts. -/
def allowance : Nat → Nat → Nat
  | _, 0 => 0
  | n, q + 1 => n + allowance (n + 1) q

/-- Fewer previous entries never increase the remaining pair count. -/
theorem allowance_mono (n m q : Nat) (within : n ≤ m) : allowance n q ≤ allowance m q := by
  induction q generalizing n m with
  | zero => exact Nat.le_refl 0
  | succ q ih => exact Nat.add_le_add within (ih _ _ (Nat.add_le_add_right within 1))

/-- The ordered attempt accounting is the ordinary pair count, including every rejected attempt. -/
theorem allowance_eq (n q : Nat) : allowance n q = q * n + q.choose 2 := by
  induction q generalizing n with
  | zero => simp only [allowance, Nat.zero_mul, Nat.choose_zero_succ, Nat.add_zero]
  | succ q ih =>
      rw [allowance, ih, Nat.choose_succ_succ, Nat.choose_one_right]
      ring

/-- The complete adaptive schedule accumulates the actual per-accept hazard over ordered attempt pairs. Arbitrary interleaving, stopping and every oracle reply remain in the original fused experiment. -/
theorem run_collision_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto) (publicValue : PublicChallenge)
    (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes) {α : Type}
    (work : OracleComp ServerAuthSpec α) (q : Nat) (bounded : work.IsQueryBoundP IsAcceptQuery q)
    (state : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (clean : ¬ Collision (thirds state.1.ghost.touches)) :
    Pr{let result ← ((simulateQ (PqxdhServerAuthGapDh.fusedImpl setup codec checks publicValue beaconSeed seed scalar) work).run state)}[Collision (thirds result.2.1.ghost.touches)] ≤
      (allowance (thirds state.1.ghost.touches).length q : ℝ≥0∞) *
        ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞)) := by
  classical
  induction work using OracleComp.inductionOn generalizing q state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, clean, ite_false]
      exact zero_le
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      by_cases accept : IsAcceptQuery query
      · cases q with
        | zero => have positive := bounded.1.resolve_left (not_not.mpr accept); omega
        | succ q =>
          have nextBound : ∀ reply, (next reply).IsQueryBoundP IsAcceptQuery q := by
            intro reply
            simpa only [accept, ite_true, Nat.add_sub_cancel] using bounded.2 reply
          have hazard := fused_collision_probability setup codec checks spread publicValue beaconSeed seed scalar
            query state clean
          rw [ite_eq_left accept] at hazard
          refine (prEvent_bind_le_prEvent_add_of_support _ _
            (fun result : _ × GameState KemSK × PqxdhJointDhExtractFamily.State =>
              Collision (thirds result.2.1.ghost.touches)) _
            (ε := (allowance ((thirds state.1.ghost.touches).length + 1) q : ℝ≥0∞) *
              ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞))) ?_).trans ?_
          · intro result supported safe
            have tailBound := ih result.1 q (nextBound result.1) result.2 safe
            have growth := fused_thirds_length setup codec checks publicValue beaconSeed seed scalar
              query state result supported
            rw [ite_eq_left accept] at growth
            apply tailBound.trans
            gcongr
            exact_mod_cast allowance_mono _ _ q growth
          · rw [allowance, Nat.cast_add, add_mul]
            exact add_le_add hazard le_rfl
      · apply prEvent_bind_le_of_forall_le_of_support
        intro result supported
        have same := fused_quiet setup codec checks publicValue beaconSeed seed scalar query accept state result supported
        have tailBound := ih result.1 q (by simpa only [accept, ite_false, Nat.sub_zero] using bounded.2 result.1)
          result.2 (by rw [same]; exact clean)
        simpa only [same] using tailBound

/-- The actual Phase 1 generation precedes the complete adaptive schedule. Its empty session history discharges the initial collision condition, for every supported source outcome and public challenge. -/
theorem body_collision_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto) (adversary : Adversary)
    (Q : Nat) (accept : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (revealed : Option IdentitySeed) (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes)
    (state : PqxdhJointDhExtractFamily.State) :
    Pr{let result ← ((simulateQ (family setup seed scalar) (body setup codec checks adversary revealed publicValue)).run state)}[Collision (thirds result.1.ghost.touches)] ≤
      (Q.choose 2 : ℝ≥0∞) * ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞)) := by
  simp only [body, simulateQ_bind, StateT.run_bind, family, rom_coins, bind_map_left]
  apply prEvent_bind_le_of_forall_le_of_support
  intro beaconSeed _
  apply prEvent_bind_le_of_forall_le_of_support
  intro oneTime _
  apply prEvent_bind_le_of_forall_le_of_support
  intro keys _
  apply prEvent_bind_le_of_forall_le_of_support
  intro published _
  rw [simulateQ_map, StateT.run_map, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    Functor.map_map, prEvent_map]
  have bound := run_collision_probability setup codec checks spread publicValue beaconSeed seed scalar
    (adversary ⟨publicValue.identity, setup.serverKeyId, published.1, revealed⟩) Q (accept _)
    (initialGameState setup publicValue published.2, state) (by simp [initialGameState, Ghost.empty, thirds, Collision])
  simpa only [initialGameState, Ghost.empty, thirds, List.filterMap_nil, List.length_nil,
    allowance_eq, Nat.mul_zero, Nat.zero_add, Function.comp_def, PqxdhServerAuthGapDh.fusedImpl] using bound

/-- Sampling the original joint challenge first preserves the same adaptive pair bound. The result also holds for the seed-reveal negative control, because this is only the session-collision event. -/
theorem gameState_collision_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto) (adversary : Adversary)
    (Q : Nat) (accept : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q) (revealSeed : Bool) :
    Pr{let result ← gameState setup codec checks revealSeed adversary}[Collision (thirds result.2.2.1.ghost.touches)] ≤
      (Q.choose 2 : ℝ≥0∞) * ((64 : ℝ≥0∞) / (Fintype.card ScalarBytes : ℝ≥0∞)) := by
  have pureMap : ∀ {α β : Type} (mx : ProbComp α) (f : α → β) (p : β → Prop),
      Pr{let y ← (mx >>= fun a => pure (f a))}[p y] = Pr{let a ← mx}[p (f a)] := fun mx f p => by
    rw [bind_pure_comp f mx, prEvent_map]
  unfold gameState
  apply prEvent_bind_le_of_forall_le_of_support
  intro seed _
  apply prEvent_bind_le_of_forall_le_of_support
  intro scalar _
  rw [pureMap]
  exact body_collision_probability setup codec checks spread adversary Q accept _ _ seed scalar _

/-- The actual raw ephemeral draw has exactly the 256-bit width stated by the approved spread contract. -/
theorem scalar_card : Fintype.card ScalarBytes = 2 ^ 256 := by
  rw [card_vector]
  have byteCard : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in rfl
  rw [byteCard]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- B7: in the original adaptive experiment, two distinct Server attempts derive the target Beacon's same 192-byte input with probability at most choose(Q,2)·64/2^256. Q counts all accept attempts, including rejection; no extra session guess, conditioned success, KEM-security assumption or input-independence premise occurs. -/
theorem collB_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (spread : X25519ScalarSpread setup.source.crypto) (adversary : Adversary)
    (Q : Nat) (accept : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q) (revealSeed : Bool) :
    Pr{let result ← gameState setup codec checks revealSeed adversary}[CollB setup result.1 result.2.1 result.2.2.1.ghost] ≤
      (Q.choose 2 : ℝ≥0∞) * 64 / (2 ^ 256 : ℝ≥0∞) := by
  have inclusion := prEvent_mono_of_support (gameState setup codec checks revealSeed adversary)
    (fun result => CollB setup result.1 result.2.1 result.2.2.1.ghost)
    (fun result => Collision (thirds result.2.2.1.ghost.touches)) (fun result supported collided =>
      collB_thirds setup result.1 result.2.1 _ result.2.2.1
        (gameState_reachable setup codec checks revealSeed adversary result supported).1 collided)
  apply inclusion.trans
  simpa only [scalar_card, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc] using
    gameState_collision_probability setup codec checks spread adversary Q accept revealSeed

end BeaconcryptCore.Computational.PqxdhServerAuthCollision

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.state_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.state_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.state_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.state_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.state_lift' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.state_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.spread_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.spread_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.verified_third_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.verified_third_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.prefix_third_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.prefix_third_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.prefix_thirds_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.prefix_thirds_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_append

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_nonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.collision_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.collision_append

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.input_third_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.input_third_nonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.root_input_third' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.root_input_third

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_mem_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.thirds_mem_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.collB_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.collB_thirds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.accept_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.accept_split

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.acceptTail_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.acceptTail_thirds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.evaluate_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.accept_collision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.accept_collision_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.finish_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.finish_thirds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.handler_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.handler_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.accept_thirds_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.accept_thirds_length

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_thirds_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_thirds_length

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_collision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.fused_collision_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.allowance_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.allowance_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.allowance_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.allowance_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.run_collision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.run_collision_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.body_collision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.body_collision_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.gameState_collision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.gameState_collision_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.scalar_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.scalar_card

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCollision.collB_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCollision.collB_probability

