-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-!
# The pin lift, control side: the record control of the CTX worlds (CE-12 P4 step 2, AG lift R1)

Facts of the compiled client's record control (`PqxdhRecordLiftProtocol.Control`) for every private service reply, used by the lift of the b2s Server-pin row of design-v2 section 7.6 (R1):

- `ServerIs identity okPeer`: the control holds a Server with that identity and every installed peer's complete AD is admitted by `okPeer` at its key ID (`PeersOk`; design §13: a per-key predicate, since every peer carries its own transcript AD `PqxdhTranscriptAd.adOf` of its own digest; it replaces the identity-derived `LegacyPeers` of the old 281-byte layout). Constructor imports are admitted when every constructor peer's metadata is (`peersOk_imported`). `ShellsOk ok`: every established owner's installed shell has associated data that `ok` admits at its owner index. `ControlOk` is both.
- Every capability whose Beacon install fits `ok` and whose Server install fits `okPeer` (`InstallFits`), every environment effect, the Server initializer and the Server and Beacon record steps keep these facts (`capability_ok`, `effects_ok`, `initialize_ok`, `serverStep_ok`, `beaconStep_ok`, `handler_ok`). An environment program whose reachable requests all fit keeps them (`effects_program_ok`, through the generic `keep_bounded`).
- On the flattened CTX world (`PqxdhRecordLiftFlat.nativeImpl`, any key modes): a native command that is not an environment command (`Quiet`: a coin, a BLAKE2b query or a record command) keeps the environment state and both facts (`nativeImpl_quiet`); an environment command is an outcome of the environment's step and keeps both facts when the step's reachable requests fit (`nativeImpl_env`).

No assumption or contract; no security claim. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordLiftWorldCompiler (Phase)
open PqxdhDeploymentInterface (Spec)
variable {n : ℕ}

/-! ### The control facts -/

/-- Every installed peer's complete AD is admitted by `okPeer` at its key ID (design §13: a per-key AD predicate, never one AD for all peers; it replaces the identity-derived `LegacyPeers` of the old 281-byte AD layout). -/
def PeersOk (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop) (server : PqxdhRecordLiftWorldCompiler.Server n) :
    Prop :=
  ∀ keyId peer, server.peers keyId = some peer → okPeer keyId peer.binding.associatedData

/-- The source constructor import fills each known peer's binding with the peer's supplied metadata, so the imported Server's peers are admitted when every constructor peer's metadata is. -/
theorem peersOk_imported (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (fits : ∀ keyId peer, created.server.server.peers keyId = some peer → okPeer keyId peer.metadata) :
    PeersOk okPeer (PqxdhRecordLiftWorldCompiler.Server.fromKnown (n := n)
      (PqxdhRecordLiftWorld.importedServer created)) := by
  intro keyId peer found
  simp only [PqxdhRecordLiftWorldCompiler.Server.fromKnown, PqxdhRecordLiftWorld.importedServer,
    Option.map_map, Option.map_eq_some_iff] at found
  obtain ⟨original, originalFound, rfl⟩ := found
  exact fits keyId original originalFound

/-- Replacing one peer keeps every peer admitted when the replacement's AD is admitted at its key ID. -/
theorem peersOk_store (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
    (server : PqxdhRecordLiftWorldCompiler.Server n)
    (holds : PeersOk okPeer server) (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n)
    (fits : okPeer keyId peer.binding.associatedData) :
    PeersOk okPeer { server with peers := Function.update server.peers keyId (some peer) } := by
  intro other current found
  by_cases same : other = keyId
  · subst other
    simp only [Function.update_self, Option.some.injEq] at found
    subst current
    exact fits
  · simp only [Function.update_of_ne same] at found
    exact holds other current found

/-- The record control holds a Server with the given identity whose installed peers' ADs are admitted by `okPeer` at their key IDs. -/
def ServerIs (identity : RawCtxServerRouting.Identity) (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
    (control : PqxdhRecordLiftProtocol.Control n) : Prop :=
  ∃ server, control.server = some server ∧ server.identity = identity ∧ PeersOk okPeer server

/-- Every established owner's installed shell has associated data admitted by `ok` at its owner index. -/
def ShellsOk (ok : ℕ → Std.Array Std.U8 151#usize → Prop) (control : PqxdhRecordLiftProtocol.Control n) : Prop :=
  ∀ (owner : ℕ) shell kernel, control.owners[owner]? = some (Phase.established shell kernel) →
    ok owner shell.associatedData

/-- Both control facts. -/
def ControlOk (identity : RawCtxServerRouting.Identity) (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
    (ok : ℕ → Std.Array Std.U8 151#usize → Prop) (control : PqxdhRecordLiftProtocol.Control n) : Prop :=
  ServerIs identity okPeer control ∧ ShellsOk ok control

/-- A Beacon install carries AD admitted by `ok` at its owner index; a Server install carries AD admitted by `okPeer` at its key ID; other effects fit. -/
def InstallFits (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop) (ok : ℕ → Std.Array Std.U8 151#usize → Prop) :
    (EnvEffects n).Domain → Prop
  | .inr (.installServer keyId binding _) => okPeer keyId binding.associatedData
  | .inr (.installBeacon owner shell _) => ok owner shell.associatedData
  | _ => True

/-- An owner list extended by an inactive owner keeps every established shell. -/
theorem shellsOk_append (ok : ℕ → Std.Array Std.U8 151#usize → Prop) (control : PqxdhRecordLiftProtocol.Control n)
    (holds : ShellsOk ok control) (phase : InactivePhase) :
    ShellsOk ok { control with owners := control.owners ++ [Phase.inactive phase] } := by
  intro owner shell kernel found
  by_cases below : owner < control.owners.length
  · rw [List.getElem?_append_left below] at found
    exact holds owner shell kernel found
  · rw [List.getElem?_append_right (Nat.le_of_not_lt below)] at found
    rcases equal : owner - control.owners.length with _ | k
    · rw [equal] at found
      simp at found
    · rw [equal] at found
      simp at found

/-- Replacing an owner by an inactive phase keeps every established shell. -/
theorem shellsOk_setInactive (ok : ℕ → Std.Array Std.U8 151#usize → Prop)
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ShellsOk ok control) (index : ℕ) (phase : InactivePhase) :
    ShellsOk ok { control with owners := control.owners.set index (Phase.inactive phase) } := by
  intro owner shell kernel found
  by_cases same : owner = index
  · subst same
    simp only [List.getElem?_set_self'] at found
    cases hget : control.owners[owner]? <;> simp_all
  · simp only [List.getElem?_set_ne (Ne.symm same)] at found
    exact holds owner shell kernel found

/-- Replacing an owner by an established phase with an admitted shell keeps every established shell. -/
theorem shellsOk_setEstablished (ok : ℕ → Std.Array Std.U8 151#usize → Prop)
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ShellsOk ok control) (index : ℕ) (shell : BeaconShell)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n) (fits : ok index shell.associatedData) :
    ShellsOk ok { control with owners := control.owners.set index (Phase.established shell stored) } := by
  intro owner shell' kernel found
  by_cases same : owner = index
  · subst same
    simp only [List.getElem?_set_self'] at found
    cases hget : control.owners[owner]? <;> simp_all
  · simp only [List.getElem?_set_ne (Ne.symm same)] at found
    exact holds owner shell' kernel found


/-! ### The compiled client's requests -/

section Requests
variable (identity : RawCtxServerRouting.Identity) (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
  (ok : ℕ → Std.Array Std.U8 151#usize → Prop)

/-- A lifted private request keeps the control. -/
theorem lift_ok (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (holds : ControlOk identity okPeer ok control)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((StateT.lift ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) :
      PqxdhRecordLiftProtocol.Client n _).run control)) : ControlOk identity okPeer ok result.2 := by
  rw [PqxdhRecordLiftProtocolHistory.lift_control query control result supported]
  exact holds

/-- Every capability that fits `ok` keeps both control facts. -/
theorem capability_ok (query : (CapabilitySpec n).Domain) (fits : InstallFits okPeer ok (n := n) (.inr query))
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ControlOk identity okPeer ok control)
    (result : (CapabilitySpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.capability query control)) : ControlOk identity okPeer ok result.2 := by
  cases query with
  | peerPresent keyId =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact holds
  | ownerPresent owner =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact holds
  | appendOwner sender pin phase =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨holds.1, shellsOk_append ok control holds.2 phase⟩
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability] at supported
      split at supported
      · split_ifs at supported
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact ⟨holds.1, shellsOk_setInactive ok control holds.2 owner phase⟩
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact holds
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact holds
  | installServer keyId peerIdentity ref =>
      simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installServer] at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact holds
      · rename_i server existing
        split_ifs at supported
        · simp only [bind_pure_comp, support_map] at supported
          obtain ⟨stored, _, rfl⟩ := supported
          obtain ⟨current, found, same, legacy⟩ := holds.1
          rw [existing, Option.some.injEq] at found
          subst found
          refine ⟨⟨_, rfl, same, ?_⟩, fun owner shell kernel present => ?_⟩
          · exact peersOk_store okPeer server legacy keyId ⟨peerIdentity, stored⟩ fits
          · rw [markUsed_owners] at present
            exact holds.2 owner shell kernel present
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact holds
  | installBeacon owner shell ref =>
      simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installBeacon] at supported
      split_ifs at supported
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨stored, _, rfl⟩ := supported
        obtain ⟨current, found, same, legacy⟩ := holds.1
        refine ⟨⟨current, by rw [markUsed_server]; exact found, same, legacy⟩, ?_⟩
        exact shellsOk_setEstablished ok control holds.2 owner shell stored fits
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact holds
  | hash bytes => exact lift_ok identity okPeer ok (.hash bytes) control holds result supported

/-- Charging and every effect that fits `ok` keep both control facts. -/
theorem effects_ok (query : (EnvEffects n).Domain) (fits : InstallFits okPeer ok query)
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ControlOk identity okPeer ok control)
    (result : (EnvEffects n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.effects query).run control)) :
    ControlOk identity okPeer ok result.2 := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨charged, member, continued⟩ := supported
  have same := PqxdhRecordLiftProtocolHistory.lift_control (.charge (effectKind query)) control charged member
  rw [same] at continued
  cases query with
  | inl coin => exact lift_ok identity okPeer ok (.coin coin) control holds result continued
  | inr request => exact capability_ok identity okPeer ok request fits control holds result continued

/-- A Server initialization keeps both control facts: a present Server is not reset. -/
theorem initialize_ok (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (control : PqxdhRecordLiftProtocol.Control n)
    (holds : ControlOk identity okPeer ok control) (result : Unit × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.initializeServer created control)) :
    ControlOk identity okPeer ok result.2 := by
  obtain ⟨server, existing, _, _⟩ := holds.1
  simp only [PqxdhRecordLiftProtocol.initializeServer, existing, support_pure, Set.mem_singleton_iff] at supported
  subst result
  exact holds

/-- Every Server record step keeps both control facts. -/
theorem serverStep_ok (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (holds : ControlOk identity okPeer ok control)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.serverStep decode route query control)) :
    ControlOk identity okPeer ok result.2 := by
  obtain ⟨current, existing, same, legacy⟩ := holds.1
  simp only [PqxdhRecordLiftProtocol.serverStep, existing] at supported
  cases query with
  | inl request =>
      obtain ⟨plaintext, keyId⟩ := request
      dsimp only at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact holds
      · simp only [bind_pure_comp, support_map] at supported
        rename_i peer selected
        obtain ⟨inner, _, rfl⟩ := supported
        exact ⟨⟨_, rfl, same, peersOk_store okPeer current legacy keyId
          { peer with kernel := inner.2.kernel } (legacy keyId peer selected)⟩, holds.2⟩
  | inr raw =>
      dsimp only at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨⟨_, rfl, same, legacy⟩, holds.2⟩
      · split at supported
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact ⟨⟨_, rfl, same, legacy⟩, holds.2⟩
        · simp only [bind_pure_comp, support_map] at supported
          rename_i peer selected
          obtain ⟨inner, _, rfl⟩ := supported
          exact ⟨⟨_, rfl, same, peersOk_store okPeer current legacy _
            { peer with kernel := inner.2.kernel } (legacy _ peer selected)⟩, holds.2⟩

/-- Every Beacon record step keeps both control facts: an established owner keeps its shell. -/
theorem beaconStep_ok (decode : RawCtxReceive.FrameDecoder) (owner : ℕ) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ControlOk identity okPeer ok control)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.beaconStep decode owner query control)) :
    ControlOk identity okPeer ok result.2 := by
  unfold PqxdhRecordLiftProtocol.beaconStep at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact holds
  · cases query <;> simp only [support_pure, Set.mem_singleton_iff] at supported <;> subst result <;> exact holds
  · rename_i shell kernel selected
    simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    refine ⟨holds.1, ?_⟩
    exact shellsOk_setEstablished ok
      { control with ownerRaw := Function.update control.ownerRaw owner inner.2.rawAttempts }
      holds.2 owner shell inner.2.kernel (holds.2 owner shell kernel selected)

/-- Every compiled-client request whose environment effect fits `ok` keeps both control facts. -/
theorem handler_ok (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (fits : ∀ effect, query = .inr (.inl effect) → InstallFits okPeer ok effect)
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ControlOk identity okPeer ok control)
    (result : (WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control)) :
    ControlOk identity okPeer ok result.2 := by
  rcases query with created | (effect | ((send | raw) | ⟨owner, request⟩))
  · exact initialize_ok identity okPeer ok created control holds result supported
  · exact effects_ok identity okPeer ok effect (fits effect rfl) control holds result supported
  · exact serverStep_ok identity okPeer ok decode route (.inl send) control holds result supported
  · exact serverStep_ok identity okPeer ok decode route (.inr raw) control holds result supported
  · rcases request with plaintext | raw
    · exact beaconStep_ok identity okPeer ok decode owner (.inl plaintext) control holds result supported
    · exact beaconStep_ok identity okPeer ok decode owner (.inr raw) control holds result supported

end Requests

/-! ### Programs -/

section Programs
variable (identity : RawCtxServerRouting.Identity) (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
  (ok : ℕ → Std.Array Std.U8 151#usize → Prop)

/-- An invariant kept by every step of a stateful handler at the requests a program may issue (those that are not bad) is kept by the program's simulation. -/
theorem keep_bounded {ι₁ ι₂ σ α : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (bad : spec₁.Domain → Bool) (inv : σ → Prop)
    (step : ∀ query state, bad query = false → inv state → ∀ result ∈ support ((impl query).run state), inv result.2)
    (work : OracleComp spec₁ α) (bounded : work.IsQueryBoundP (fun query => bad query = true) 0) (state : σ)
    (holds : inv state) : ∀ result ∈ support ((simulateQ impl work).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact holds
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have good : bad query = false := by
        cases found : bad query
        · rfl
        · exact absurd (bounded.1.resolve_right (lt_irrefl 0)) (by simp [found])
      intro result supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, final⟩ := supported
      exact ih middle.1 (by simpa [good] using bounded.2 middle.1) middle.2 (step query state good holds middle first)
        result final

/-- An environment program whose every reachable request is admitted keeps both control facts, for every private reply. -/
theorem effects_program_ok {α : Type} (bad : (EnvEffects n).Domain → Bool)
    (fitting : ∀ query, bad query = false → InstallFits okPeer ok query) (work : OracleComp (EnvEffects n) α)
    (bounded : work.IsQueryBoundP (fun query => bad query = true) 0) (control : PqxdhRecordLiftProtocol.Control n)
    (holds : ControlOk identity okPeer ok control) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftProtocol.effects work).run control), ControlOk identity okPeer ok result.2 :=
  keep_bounded _ bad _ (fun query state good held result member =>
    effects_ok identity okPeer ok query (fitting query good) state held result member) work bounded control holds

end Programs



/-! ### Native commands of the CTX worlds -/

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E : Type}
  (identity : RawCtxServerRouting.Identity) (okPeer : Std.U64 → Std.Array Std.U8 151#usize → Prop)
  (ok : ℕ → Std.Array Std.U8 151#usize → Prop)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)

/-- A native command that is not an environment command: a coin, a BLAKE2b query or a record command. -/
def Quiet : Spec.Domain → Prop
  | .inl _ => True
  | .inr command => ¬ IsEnvironment command

/-- The value of a simulated run is a reachable value of the simulated program. -/
theorem run_value {ι₁ ι₂ σ α : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (work : OracleComp spec₁ α) (state : σ)
    (result : α × σ) (supported : result ∈ support ((simulateQ impl work).run state)) : result.1 ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset impl work state
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- A lifted world request of the native dispatch is the compiled client's request, with the environment state kept. -/
theorem lift_world_run (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (request : (WorldSpec n).Domain) (e : E) (control : PqxdhRecordLiftProtocol.Control n) :
    (simulateQ (PqxdhRecordLiftProtocol.handler decode route)
      ((StateT.lift (liftM ((WorldSpec n).query request)) : StateT E (OracleComp (WorldSpec n)) _).run e)).run control =
      (fun p => ((p.1, e), p.2)) <$> (PqxdhRecordLiftProtocol.handler decode route request).run control := by
  rw [StateT.run_lift, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- A lifted world request whose environment effect fits `ok` keeps the environment state and both control facts. -/
theorem lift_request_ok (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (request : (WorldSpec n).Domain) (fits : ∀ effect, request = .inr (.inl effect) → InstallFits okPeer ok effect) (e : E)
    (control : PqxdhRecordLiftProtocol.Control n) (holds : ControlOk identity okPeer ok control) :
    ∀ inner ∈ support ((simulateQ (PqxdhRecordLiftProtocol.handler decode route)
      ((StateT.lift (liftM ((WorldSpec n).query request)) : StateT E (OracleComp (WorldSpec n)) _).run e)).run control),
      inner.1.2 = e ∧ ControlOk identity okPeer ok inner.2 := by
  intro inner member
  rw [lift_world_run, support_map] at member
  obtain ⟨p, pMember, rfl⟩ := member
  exact ⟨rfl, handler_ok identity okPeer ok decode route request fits control holds p pMember⟩

/-- Every native command that is not an environment command keeps the environment state and both control facts. -/
theorem nativeImpl_quiet (modes : Label n → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (quiet : Quiet query) (state : NativeState n E)
    (holds : ControlOk identity okPeer ok state.1.2) :
    ∀ result ∈ support ((nativeImpl modes replace setup codec route env query).run state),
      result.2.1.1 = state.1.1 ∧ ControlOk identity okPeer ok result.2.1.2 := by
  intro result member
  rw [nativeImpl_run, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  have client := run_value (ctxInterpreter modes replace setup codec) _ state.2 inner reached
  rcases query with coin | command
  · exact lift_request_ok identity okPeer ok codec.frameRead route (.inr (.inl (.inl coin)))
      (fun effect same => by cases same; trivial) state.1.1 state.1.2 holds inner.1 client
  · cases command with
    | hash bytes =>
        exact lift_request_ok identity okPeer ok codec.frameRead route (.inr (.inl (.inr (.hash bytes))))
          (fun effect same => by cases same; trivial) state.1.1 state.1.2 holds inner.1 client
    | serverSend keyId plaintext =>
        exact lift_request_ok identity okPeer ok codec.frameRead route (.inr (.inr (.inl (.inl (plaintext, keyId)))))
          (fun _ same => (by cases same)) state.1.1 state.1.2 holds inner.1 client
    | serverRaw raw =>
        exact lift_request_ok identity okPeer ok codec.frameRead route (.inr (.inr (.inl (.inr raw))))
          (fun _ same => (by cases same)) state.1.1 state.1.2 holds inner.1 client
    | beaconSend owner plaintext =>
        exact lift_request_ok identity okPeer ok codec.frameRead route (.inr (.inr (.inr (owner, .inl plaintext))))
          (fun _ same => (by cases same)) state.1.1 state.1.2 holds inner.1 client
    | beaconRaw owner raw =>
        exact lift_request_ok identity okPeer ok codec.frameRead route (.inr (.inr (.inr (owner, .inr raw))))
          (fun _ same => (by cases same)) state.1.1 state.1.2 holds inner.1 client
    | _ => exact absurd trivial quiet

/-- An environment command of the native dispatch is the environment's step with its effects lifted. -/
theorem native_env_run (env : Environment n E) (command : PqxdhDeploymentInterface.Command)
    (allowed : IsEnvironment command) (e : E) :
    (native env (.inr command)).run e = simulateQ effectLift ((env.step ⟨command, allowed⟩).run e) := by
  cases command <;> first | rfl | exact absurd allowed id

/-- The compiled client answers lifted environment effects with its effect handler. -/
theorem handler_effectLift (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder) :
    (PqxdhRecordLiftProtocol.handler (n := n) decode route) ∘ₛ effectLift = PqxdhRecordLiftProtocol.effects := by
  funext request
  simp only [QueryImpl.apply_compose, effectLift, simulateQ_spec_query]
  rfl

/-- Every environment command of a CTX world is an outcome of the environment's step, and it keeps both control facts when the step's reachable effects are admitted. -/
theorem nativeImpl_env (modes : Label n → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (command : PqxdhDeploymentInterface.Command) (allowed : IsEnvironment command)
    (state : NativeState n E) :
    ∀ result ∈ support ((nativeImpl modes replace setup codec route env (.inr command)).run state),
      ((result.1, result.2.1.1) : EnvSpec.Range ⟨command, allowed⟩ × E) ∈
          support ((env.step ⟨command, allowed⟩).run state.1.1) ∧
        ∀ bad : (EnvEffects n).Domain → Bool, (∀ query, bad query = false → InstallFits okPeer ok query) →
          ((env.step ⟨command, allowed⟩).run state.1.1).IsQueryBoundP (fun query => bad query = true) 0 →
          ControlOk identity okPeer ok state.1.2 → ControlOk identity okPeer ok result.2.1.2 := by
  intro result member
  rw [nativeImpl_run, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  have client := run_value (ctxInterpreter modes replace setup codec) _ state.2 inner reached
  rw [native_env_run env command allowed, ← QueryImpl.simulateQ_compose, handler_effectLift] at client
  exact ⟨run_value _ _ _ _ client, fun bad fitting bounded holds =>
    effects_program_ok identity okPeer ok bad fitting _ bounded state.1.2 holds inner.1 client⟩

end Native

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.shellsOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.shellsOk_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.shellsOk_setInactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.shellsOk_setInactive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.shellsOk_setEstablished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.shellsOk_setEstablished

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.lift_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.lift_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.capability_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.capability_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.effects_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.effects_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.initialize_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.initialize_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.serverStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.serverStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.beaconStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.beaconStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.handler_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.handler_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.keep_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.keep_bounded

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.effects_program_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.effects_program_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.run_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.run_value

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.lift_world_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.lift_world_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.lift_request_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.lift_request_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.nativeImpl_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.nativeImpl_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.native_env_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.native_env_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.handler_effectLift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.handler_effectLift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.nativeImpl_env' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.nativeImpl_env
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.peersOk_imported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.peersOk_imported
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.peersOk_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl.peersOk_store
