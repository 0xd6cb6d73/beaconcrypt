-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal

/-!
# AG, seal side: the seal-context invariant of the ideal CTX worlds (CE-12 P2b, design-v2 section 7.7)

The first of the three ingredients that design-v2 section 7.7 lists for AG, the agreement of an accepted hidden receive with a counterpart production of its frame: every replay-dictionary seal of an ideal CTX world (`PqxdhRecordLiftIdeal.ctxRun` in any assignment of the replay and random modes, in particular `idealAuth`) was made with the associated data of a handle that owns its label, read at the current source control.

- `handleAd control handle` is the associated data of a handle's installed record owner, exactly as the source program builds it: a Server peer's `PqxdhRecordLiftWorldCompiler.serverOwner` AD, `RawCtxServerRouting.associatedBytes` of the Server identity and the peer identity (Server first; the extracted `build_associated_data` of Rust `beaconcrypt-core/src/pqxdh.rs`, `associatedBytes_exact`), and an established Beacon owner's `PqxdhRecordLiftWorldCompiler.beaconOwner` AD, the 153 bytes of its installed shell. Absent and inactive handles have none (`handleAd_peer`, `handleAd_owner`).
- `AdKept before after`: every handle AD present before is present unchanged after. Every source dispatcher request keeps it for every private service reply (`handler_adKept`, from the Server initializer, the capabilities, which install only vacant peers and init-sent owners, and the Server and Beacon record dispatchers, which change only kernels and counters), hence every adaptive schedule (`schedule_adKept`), every private interpreter (`interpreted_adKept`), every native command and continuation (`native_adKept`, `native_program_adKept`) and every secrecy-ledger command (`full_adKept`).
- `SealsBy control handle ad before after`: every new dictionary entry is a seal by `handle` at a label it owns, with record AD bytes `ad`. The exact hidden sealing service adds only its own selected input, whose record AD bytes are the sealing context's AD (`sealing_sealsBy`, from `PqxdhRecordFactsOriginServices.sealing_trace` and `RawCtxSelectedMessageSealing.selectedInput`); the hidden kernel send seals its current sending coordinate with its own context (`kernelSend_sealsBy`, from `PqxdhRecordLiftChainState.send_begin_tracked`); the owner send seals with the owner's AD and owner receives add no seal (`ownerSend_sealsBy`, `ownerReceive_keys`, `ownerRun_sealsBy`).
- `NewSealsAd`, the per-request form with the handle's `handleAd` (`serverStep_newSealsAd`, `beaconStep_newSealsAd`, `handler_newSealsAd`), and the invariant `SealAd control secret`: every dictionary entry has a handle that owns its label and whose `handleAd` is the entry's record AD bytes. It holds initially (`initial_sealAd`), is kept by every request (`handler_sealAd`, with `PqxdhRecordLiftProtocolHistory.handler` for label ownership and `handler_adKept`) and every schedule (`schedule_sealAd`), and holds at every supported outcome of every ideal CTX world (`ctxRun_sealAd`).

The proofs follow the structure of the frozen origin facts (`PqxdhRecordFactsOriginInvariant`, `PqxdhRecordFactsOriginSend`, `PqxdhRecordLiftProtocolHistory`) and add no assumption or contract; they read only the source control, the private CTX dictionaries and the literal source requests. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle FrameTag Spec FullSpec FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The associated data of a handle's installed record owner in the source control: a Server peer's `serverOwner` AD (`associatedBytes` of the Server identity and the peer identity, Server first) and an established Beacon owner's `beaconOwner` AD (its shell's 153 bytes); absent Server peers, absent owners and inactive owners have none. -/
noncomputable def handleAd (control : PqxdhRecordLiftProtocol.Control n) : Handle → Option Pqxdh.Bytes
  | .peer keyId => control.server.bind fun server => (server.peers keyId).map fun peer =>
      RawCtxServerRouting.associatedBytes server.identity peer.identity
  | .owner owner => (control.owners[owner]?).bind fun phase => match phase with
      | .inactive _ => none
      | .established shell _ => some (PqxdhRefinement.absBytes shell.associatedData)

/-- A present Server peer's AD is the AD of its selected source owner `serverOwner`. -/
theorem handleAd_peer (control : PqxdhRecordLiftProtocol.Control n)
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n) (found : server.peers keyId = some peer) :
    handleAd control (.peer keyId) = some (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData := by
  simp only [handleAd, existing, Option.bind_some, found, Option.map_some, PqxdhRecordLiftWorldCompiler.serverOwner]

/-- An established Beacon owner's AD is the AD of its selected source owner `beaconOwner`. -/
theorem handleAd_owner (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat)
    (shell : BeaconShell) (kernel : StoredKernel n)
    (found : control.owners[owner]? = some (.established shell kernel)) (rawAttempts : Nat) :
    handleAd control (.owner owner) =
      some (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel rawAttempts).associatedData := by
  simp only [handleAd, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

/-- Every handle AD present before a transition is present and unchanged after it. -/
def AdKept (before after : PqxdhRecordLiftProtocol.Control n) : Prop :=
  ∀ handle ad, handleAd before handle = some ad → handleAd after handle = some ad

/-- Reflexivity of AD retention. -/
theorem adKept_refl (control : PqxdhRecordLiftProtocol.Control n) : AdKept control control :=
  fun _ _ present => present

/-- AD retention composes across an intervening control. -/
theorem adKept_trans (first middle last : PqxdhRecordLiftProtocol.Control n)
    (left : AdKept first middle) (right : AdKept middle last) : AdKept first last :=
  fun handle ad present => right handle ad (left handle ad present)

/-- AD retention from its Server-peer and Beacon-owner halves. -/
theorem adKept_of (before after : PqxdhRecordLiftProtocol.Control n)
    (peers : ∀ keyId ad, handleAd before (.peer keyId) = some ad → handleAd after (.peer keyId) = some ad)
    (owners : ∀ owner ad, handleAd before (.owner owner) = some ad → handleAd after (.owner owner) = some ad) :
    AdKept before after := by
  intro handle ad present
  cases handle with
  | peer keyId => exact peers keyId ad present
  | owner owner => exact owners owner ad present

/-- The Server initializer keeps every AD: a present Server is not reset, and before the first initialization no Server peer has an AD. -/
theorem initialize_adKept (created : PqxdhLiveServerConstruction.Created Unit)
    (control : PqxdhRecordLiftProtocol.Control n) (result : Unit × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.initializeServer created control)) :
    AdKept control result.2 := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.initializeServer, existing, support_pure, Set.mem_singleton_iff] at supported
    subst result
    apply adKept_of
    · intro keyId ad present
      simp [handleAd, existing] at present
    · intro owner ad present
      exact present
  | some server =>
    simp only [PqxdhRecordLiftProtocol.initializeServer, existing, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact adKept_refl control

/-- A lifted private request leaves the control, hence every AD, unchanged. -/
theorem lift_adKept (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((StateT.lift ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) :
      PqxdhRecordLiftProtocol.Client n _).run control)) : AdKept control result.2 := by
  rw [PqxdhRecordLiftProtocolHistory.lift_control query control result supported]
  exact adKept_refl control

/-- A Server install sets only a vacant peer key ID and changes neither the Server identity nor any present peer, so every present AD is kept. -/
theorem installServer_adKept (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (result : Bool × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.installServer keyId identity ref control)) :
    AdKept control result.2 := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.installServer, existing, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact adKept_refl control
  | some server =>
    simp only [PqxdhRecordLiftProtocol.installServer, existing] at supported
    split_ifs at supported with admitted
    · simp only [bind_pure_comp, support_map] at supported
      obtain ⟨stored, _, rfl⟩ := supported
      apply adKept_of
      · intro other ad present
        by_cases same : other = keyId
        · subst other
          simp [handleAd, existing, admitted.1] at present
        · simp only [handleAd, existing, Option.bind_some] at present
          simp only [handleAd, Option.bind_some, Function.update_of_ne same]
          exact present
      · intro owner ad present
        cases ref <;> exact present
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact adKept_refl control

/-- A Beacon install establishes only an inactive init-sent owner and changes no other owner or Server peer, so every present AD is kept. -/
theorem installBeacon_adKept (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (result : Bool × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.installBeacon owner shell ref control)) :
    AdKept control result.2 := by
  simp only [PqxdhRecordLiftProtocol.installBeacon] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨stored, _, rfl⟩ := supported
    apply adKept_of
    · intro keyId ad present
      cases ref <;> exact present
    · intro other ad present
      by_cases same : other = owner
      · subst other
        have ready : control.owners[owner]? = some (PqxdhRecordLiftWorldCompiler.Phase.inactive .initSent) := admitted.1
        simp [handleAd, ready] at present
      · simp only [handleAd] at present ⊢
        rw [List.getElem?_set_ne (Ne.symm same)]
        exact present
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact adKept_refl control

/-- Every frozen environment capability keeps every AD for every private reply. -/
theorem capability_adKept (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (result : (CapabilitySpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.capability query control)) : AdKept control result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_adKept keyId identity ref control result supported
  | installBeacon owner shell ref => exact installBeacon_adKept owner shell ref control result supported
  | hash bytes => exact lift_adKept (.hash bytes) control result supported
  | peerPresent keyId =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact adKept_refl control
  | ownerPresent owner =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact adKept_refl control
  | appendOwner sender pin phase =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      apply adKept_of
      · intro keyId ad present
        exact present
      · intro owner ad present
        simp only [handleAd, Option.bind_eq_some_iff] at present ⊢
        obtain ⟨phase', found, rest⟩ := present
        exact ⟨phase', by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]; exact found, rest⟩
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability] at supported
      cases found : control.owners[owner]? with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact adKept_refl control
      | some prior =>
          cases prior with
          | established shell kernel =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact adKept_refl control
          | inactive before =>
              simp only [found] at supported
              split_ifs at supported with legal
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst result
                apply adKept_of
                · intro keyId ad present
                  exact present
                · intro other ad present
                  by_cases same : other = owner
                  · subst other
                    simp [handleAd, found] at present
                  · simp only [handleAd] at present ⊢
                    rw [List.getElem?_set_ne (Ne.symm same)]
                    exact present
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst result
                exact adKept_refl control

/-- Charging, environment coins and every capability keep every AD. -/
theorem effects_adKept (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (result : (EnvEffects n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.effects query).run control)) : AdKept control result.2 := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨charged, member, continued⟩ := supported
  have same := PqxdhRecordLiftProtocolHistory.lift_control (.charge (effectKind query)) control charged member
  rw [same] at continued
  cases query with
  | inl coin => exact lift_adKept (.coin coin) control result continued
  | inr request => exact capability_adKept request control result continued

/-- Storing a selected Server peer's advanced kernel and the raw counter keeps every AD: the peer identity and the Server identity are unchanged. -/
theorem server_store_adKept (control : PqxdhRecordLiftProtocol.Control n)
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n) (present : server.peers keyId = some peer)
    (next : StoredKernel n) (rawAttempts : Nat) :
    AdKept control { control with server := some { server with
      peers := Function.update server.peers keyId (some { peer with kernel := next }), rawAttempts := rawAttempts } } := by
  apply adKept_of
  · intro other ad before
    by_cases same : other = keyId
    · subst other
      simp only [handleAd, existing, Option.bind_some, present, Option.map_some, Option.some.injEq] at before
      simp only [handleAd, Option.bind_some, Function.update_self, Option.map_some, before]
    · simp only [handleAd, existing, Option.bind_some] at before
      simp only [handleAd, Option.bind_some, Function.update_of_ne same]
      exact before
  · intro owner ad before
    exact before

/-- Changing only the Server raw-attempt counter keeps every AD. -/
theorem server_raw_adKept (control : PqxdhRecordLiftProtocol.Control n)
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server) (rawAttempts : Nat) :
    AdKept control { control with server := some { server with rawAttempts := rawAttempts } } := by
  apply adKept_of
  · intro keyId ad before
    simp only [handleAd, existing, Option.bind_some] at before
    simpa only [handleAd, Option.bind_some] using before
  · intro owner ad before
    exact before

/-- Storing an established owner's advanced kernel under the same shell keeps every AD. -/
theorem beacon_store_adKept (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat)
    (shell : BeaconShell) (stored next : StoredKernel n)
    (present : control.owners[owner]? = some (.established shell stored)) (rawAttempts : Nat) :
    AdKept control { control with owners := control.owners.set owner (.established shell next), ownerRaw := Function.update control.ownerRaw owner rawAttempts } := by
  apply adKept_of
  · intro keyId ad before
    exact before
  · intro other ad before
    by_cases same : other = owner
    · subst other
      simp only [handleAd, present, Option.bind_some] at before
      simp only [handleAd, List.getElem?_set_self (List.getElem?_eq_some_iff.mp present).1, Option.bind_some, before]
    · simp only [handleAd] at before ⊢
      rw [List.getElem?_set_ne (Ne.symm same)]
      exact before

/-- Every literal Server routing, parser and selected-owner path keeps every AD for every private reply. -/
theorem serverStep_adKept (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.serverStep decode route query control)) :
    AdKept control result.2 := by
  cases existing : control.server with
  | none =>
      cases query <;>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact adKept_refl control
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact adKept_refl control
          | some peer =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, bind_pure_comp, support_map] at supported
              obtain ⟨inner, _, rfl⟩ := supported
              exact server_store_adKept control server existing keyId peer selected inner.2.kernel inner.2.rawAttempts
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact server_raw_adKept control server existing _
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact server_raw_adKept control server existing _
              | some peer =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, bind_pure_comp, support_map] at supported
                  obtain ⟨inner, _, rfl⟩ := supported
                  exact server_store_adKept control server existing keyId peer selected inner.2.kernel inner.2.rawAttempts

/-- Every literal Beacon phase, parser and selected-owner path keeps every AD for every private reply. -/
theorem beaconStep_adKept (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.beaconStep decode owner query control)) :
    AdKept control result.2 := by
  cases selected : control.owners[owner]? with
  | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact adKept_refl control
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [PqxdhRecordLiftProtocol.beaconStep, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact adKept_refl _
      | established shell kernel =>
          simp only [PqxdhRecordLiftProtocol.beaconStep, selected, bind_pure_comp, support_map] at supported
          obtain ⟨inner, _, rfl⟩ := supported
          exact beacon_store_adKept control owner shell kernel inner.2.kernel selected inner.2.rawAttempts

/-- The source dispatcher keeps every AD for every request and every private service reply. -/
theorem handler_adKept (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (result : (WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control)) :
    AdKept control result.2 := by
  cases query with
  | inl created => exact initialize_adKept created control result supported
  | inr outer =>
      cases outer with
      | inl effect => exact effects_adKept effect control result supported
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_adKept decode route (.inl send) control result supported
              | inr raw => exact serverStep_adKept decode route (.inr raw) control result supported
          | inr ownerQuery =>
              obtain ⟨owner, request⟩ := ownerQuery
              cases request with
              | inl plaintext => exact beaconStep_adKept decode owner (.inl plaintext) control result supported
              | inr raw => exact beaconStep_adKept decode owner (.inr raw) control result supported

/-- Every adaptive source schedule keeps every AD for every permitted private reply path. -/
theorem schedule_adKept {Result : Type} (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (result : Result × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.schedule decode route client control)) :
    AdKept control result.2 := by
  induction client using OracleComp.inductionOn generalizing control result with
  | pure value =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact adKept_refl control
  | query_bind query next ih =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact adKept_trans _ _ _ (handler_adKept decode route query control inner member) (ih inner.1 inner.2 result continued)

/-- An arbitrary private interpreter selects one permitted reply path, so every interpreted schedule keeps every AD. -/
theorem interpreted_adKept {ι' : Type} {spec : OracleSpec ι'} {P Result : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp spec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (privateState : P) (result : (Result × PqxdhRecordLiftProtocol.Control n) × P)
    (supported : result ∈ support ((simulateQ service
      (PqxdhRecordLiftProtocol.schedule decode route client control)).run privateState)) :
    AdKept control result.1.2 := by
  apply schedule_adKept decode route client control result.1
  apply support_simulateQ_run'_subset service _ privateState
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- Every native command of an ideal CTX world keeps every AD. -/
theorem native_adKept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    AdKept before.1.2 result.2.1.2 := by
  rw [nativeImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact interpreted_adKept (ctxInterpreter modes replace setup codec) codec.frameRead route
    ((native env query).run before.1.1) before.1.2 before.2 inner reached

/-- Every adaptive native continuation keeps every AD. -/
theorem native_program_adKept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : NativeState n E)
    (result : X × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env) client).run before)) :
    AdKept before.1.2 result.2.1.2 :=
  support_keep_oracle (nativeImpl modes replace setup codec route env)
    (fun state => AdKept before.1.2 state.1.2)
    (fun query state kept next reached => adKept_trans _ _ _ kept
      (native_adKept modes replace setup codec route env query state next reached))
    client before (adKept_refl before.1.2) result supported

/-- Every secrecy-ledger command keeps every AD, including experiment-generated sends. -/
theorem full_adKept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    AdKept before.2.1.2 result.2.2.1.2 := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program_adKept modes replace setup codec route env _ before.2 inner reached

/-! ### The seal-context invariant -/

/-- Every new dictionary entry of a step is a seal by `handle` at a label that `handle` owns, with record AD bytes `ad`. -/
def SealsBy (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) (ad : Pqxdh.Bytes)
    (before after : CtxPrivate n) : Prop :=
  ∀ label entry, entry ∈ (after.keys label).1.successfulSeals →
    entry ∈ (before.keys label).1.successfulSeals ∨
      (OwnsLabel control label handle ∧ entry.input.context.ad.bytes = ad)

/-- A step that keeps every seal list adds no seal. -/
theorem sealsBy_keys (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) (ad : Pqxdh.Bytes)
    (before after : CtxPrivate n)
    (keys : ∀ label, (after.keys label).1.successfulSeals = (before.keys label).1.successfulSeals) :
    SealsBy control handle ad before after := by
  intro label entry member
  rw [keys label] at member
  exact Or.inl member

/-- New seals by one handle with one AD compose across an intervening state. -/
theorem sealsBy_trans (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) (ad : Pqxdh.Bytes)
    (first middle last : CtxPrivate n) (left : SealsBy control handle ad first middle)
    (right : SealsBy control handle ad middle last) : SealsBy control handle ad first last := by
  intro label entry member
  rcases right label entry member with prior | fresh
  · exact left label entry prior
  · exact Or.inr fresh

/-- The exact hidden sealing service adds only its own selected input at its material coordinate, whose record AD bytes are the sealing context's AD; a refused seal adds nothing. -/
theorem sealing_sealsBy (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (owned : OwnsLabel control pending.material handle)
    (before : CtxPrivate n) (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.sealing pending)).run before)) :
    SealsBy control handle pending.context.associatedData before result.2 := by
  obtain ⟨_, unchanged | ⟨width, record, inserted, _, _⟩⟩ :=
    PqxdhRecordFactsOriginServices.sealing_trace modes ideal replace setup codec pending before result supported
  · exact sealsBy_keys control handle _ before result.2 unchanged.2.2
  · intro label entry member
    by_cases same : label = pending.material
    · subst label
      rw [inserted, List.mem_cons] at member
      rcases member with rfl | prior
      · exact Or.inr ⟨owned, rfl⟩
      · exact Or.inl prior
    · rw [PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending before result supported label same] at member
      exact Or.inl member

/-- A hidden kernel send seals only at its current sending coordinate and with its own context, through exhaustion, lookup and every writer result. -/
theorem kernelSend_sealsBy (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (slot : Slot n) (entry : LabeledKernel n) (owned : OwnsLabel control entry.send_chain handle)
    (context : RawCtxSourceSend.SealContext) (before : CtxPrivate n)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run before)) :
    SealsBy control handle context.associatedData before result.2 := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  cases admitted : RawCtxChainSend.normalBegin entry context with
  | exhausted original prior =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact sealsBy_keys control handle _ before before (fun _ => rfl)
  | requested pending =>
    rw [admitted] at tracked
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨looked, lookupSupported, continued⟩ := supported
    rw [mem_support_bind_iff] at continued
    obtain ⟨sealed, sealSupported, finished⟩ := continued
    simp only [support_pure, Set.mem_singleton_iff] at finished
    subst result
    have lookup := PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec pending.request before looked
      lookupSupported
    apply sealsBy_trans control handle _ before looked.2 sealed.2
    · exact sealsBy_keys control handle _ before looked.2
        (fun label => congrArg (fun keys => (keys label).1.successfulSeals) lookup.1)
    · have sealing := sealing_sealsBy modes ideal replace setup codec control handle _
        (by simpa only [RawCtxChainSend.ready, tracked.2.2.1] using owned) looked.2 sealed sealSupported
      simpa only [RawCtxChainSend.ready, tracked.2.1] using sealing

/-- A caller-known send changes no seal dictionary. -/
theorem knownSend_keys (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (before : CtxPrivate n)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.knownSend kernel context)).run before)) :
    result.2.keys = before.keys := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rfl

/-- A caller-known receive changes no seal dictionary. -/
theorem knownReceive_keys (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (before : CtxPrivate n)
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.knownReceive kernel target context)).run before)) :
    result.2.keys = before.keys := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rfl

/-- The owner send seals only with the owner's AD at a label that the sending handle owns, including empty and caller-known sends. -/
theorem ownerSend_sealsBy (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)).run before)) :
    SealsBy control handle owner.associatedData before result.2 := by
  unfold PqxdhRecordLiftProtocol.ownerSend at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact sealsBy_keys control handle _ before before (fun _ => rfl)
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases kind : owner.kernel with
    | hidden slot kernel =>
      rw [kind] at stored reached
      obtain ⟨claimed, same, owned⟩ := PqxdhRecordFactsOriginSend.sending_claim control safe handle slot kernel stored
      rw [← Option.some.inj same] at owned
      exact kernelSend_sealsBy modes ideal replace setup codec control handle slot kernel owned _ before inner reached
    | known kernel =>
      rw [kind] at reached
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, support_map] at reached
      obtain ⟨native, nativeReached, rfl⟩ := reached
      exact sealsBy_keys control handle _ before native.2 (fun label => by
        rw [knownSend_keys modes replace setup codec before kernel _ native nativeReached])

/-- Every owner receive outcome keeps every seal list, through parser refusals, caller-known and hidden kernels. -/
theorem ownerReceive_keys (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (before : CtxPrivate n)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (raw : Pqxdh.Bytes)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases kind : owner.kernel with
    | known kernel =>
      rw [kind] at reached
      simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, support_map] at reached
      obtain ⟨native, nativeReached, rfl⟩ := reached
      intro label
      rw [knownReceive_keys modes replace setup codec before kernel _ _ native nativeReached]
    | hidden slot kernel =>
      rw [kind] at reached
      simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
        StateT.run_map, support_map] at reached
      obtain ⟨native, nativeReached, rfl⟩ := reached
      exact (PqxdhRecordFactsOriginReceive.receive_retained modes ideal replace setup codec _ before native
        nativeReached).seals
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact fun _ => rfl

/-- The complete owner command, including its publication callback, seals only with the owner's AD at labels the handle owns. -/
theorem ownerRun_sealsBy (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (tag : FrameTag) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (before : CtxPrivate n)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead query owner)).run before)) :
    SealsBy control handle owner.associatedData before result.2 := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
  obtain ⟨stepped, stepSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  apply sealsBy_trans control handle _ before stepped.2 _ _ (sealsBy_keys control handle _ _ _ (fun _ => rfl))
  cases query with
  | inl plaintext =>
    exact ownerSend_sealsBy modes ideal replace setup codec control safe handle owner stored sender plaintext
      before stepped stepSupported
  | inr raw =>
    exact sealsBy_keys control handle _ before stepped.2
      (ownerReceive_keys modes ideal replace setup codec before owner raw stepped stepSupported)

/-- Every new dictionary entry of a step carries the AD of a handle that owns its label. -/
def NewSealsAd (control : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n) : Prop :=
  ∀ label entry, entry ∈ (after.keys label).1.successfulSeals →
    entry ∈ (before.keys label).1.successfulSeals ∨
      ∃ handle, OwnsLabel control label handle ∧ handleAd control handle = some entry.input.context.ad.bytes

/-- Seals by a handle with its own AD are new seals with a handle AD. -/
theorem newSealsAd_of_sealsBy (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) (ad : Pqxdh.Bytes)
    (present : handleAd control handle = some ad) (before after : CtxPrivate n)
    (sealed : SealsBy control handle ad before after) : NewSealsAd control before after := by
  intro label entry member
  rcases sealed label entry member with prior | ⟨owned, same⟩
  · exact Or.inl prior
  · exact Or.inr ⟨handle, owned, same ▸ present⟩

/-- A step that keeps every dictionary adds no seal. -/
theorem newSealsAd_keys (control : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (keys : after.keys = before.keys) : NewSealsAd control before after := by
  intro label entry member
  rw [keys] at member
  exact Or.inl member

/-- Every literal Server dispatcher path adds only seals with the selected peer's AD at labels the peer owns. -/
theorem serverStep_newSealsAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : CtxPrivate n)
    (result : (RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route query control)).run before)) :
    NewSealsAd control before result.2 := by
  cases existing : control.server with
  | none =>
    cases query <;> simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported <;> subst result <;> exact newSealsAd_keys control before before rfl
  | some server =>
    have common : ∀ (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n), server.peers keyId = some peer →
        ∀ (request' : RawCtxMixedOwner.SourceSpec.Domain)
          (inner : (RawCtxMixedOwner.SourceSpec.Range request' × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n),
        inner ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
          (PqxdhRecordLiftProtocol.ownerRun (PqxdhDeploymentNative.serverTag query) server.sender codec.frameRead request'
            (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer))).run before) →
        NewSealsAd control before inner.2 := by
      intro keyId peer found request' inner reached
      apply newSealsAd_of_sealsBy control (.peer keyId) _ (handleAd_peer control server existing keyId peer found)
      exact ownerRun_sealsBy modes ideal replace setup codec control safe (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer)
        (by simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
          PqxdhRecordLiftWorldCompiler.serverOwner]) _ _ request' before inner reached
    cases query with
    | inl request =>
      obtain ⟨plaintext, keyId⟩ := request
      cases found : server.peers keyId with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact newSealsAd_keys control before before rfl
      | some peer =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact common keyId peer found (.inl plaintext) inner reached
    | inr raw =>
      cases routed : route raw with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact newSealsAd_keys control before before rfl
      | some keyId =>
        cases found : server.peers keyId with
        | none =>
          simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact newSealsAd_keys control before before rfl
        | some peer =>
          simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
            simulateQ_map, StateT.run_map, support_map] at supported
          obtain ⟨inner, reached, rfl⟩ := supported
          exact common keyId peer found (.inr raw) inner reached

/-- Every literal Beacon dispatcher path adds only seals with the established owner's AD at labels the owner owns. -/
theorem beaconStep_newSealsAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (before : CtxPrivate n)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner query control)).run before)) :
    NewSealsAd control before result.2 := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact newSealsAd_keys control before before rfl
  · cases query <;> simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported <;> subst result <;> exact newSealsAd_keys control before before rfl
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply newSealsAd_of_sealsBy control (.owner owner) _ (handleAd_owner control owner shell kernel found (control.ownerRaw owner))
    exact ownerRun_sealsBy modes ideal replace setup codec control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      (by simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]) _ _ query
      before inner reached

/-- The seal-context invariant (design-v2 section 7.7): every replay-dictionary seal has a handle that owns its label and whose AD is the seal's record AD bytes. -/
def SealAd (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) : Prop :=
  ∀ label entry, entry ∈ (secret.keys label).1.successfulSeals →
    ∃ handle, OwnsLabel control label handle ∧ handleAd control handle = some entry.input.context.ad.bytes

/-- The seal-context invariant is kept by a step with new seals carrying handle ADs, label ownership that persists and ADs that persist. -/
theorem sealAd_step (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (good : SealAd control before) (fresh : NewSealsAd control before after) (progress : Step control next)
    (kept : AdKept control next) : SealAd next after := by
  intro label entry member
  rcases fresh label entry member with prior | ⟨handle, owned, present⟩
  · obtain ⟨handle, owned, present⟩ := good label entry prior
    exact ⟨handle, ownsLabel_step control next progress label handle owned, kept handle _ present⟩
  · exact ⟨handle, ownsLabel_step control next progress label handle owned, kept handle _ present⟩

/-- Every source dispatcher request of an ideal CTX world adds only seals with handle ADs, including the Server initializer and every environment effect. -/
theorem handler_newSealsAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (before : CtxPrivate n)
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run control)).run before)) :
    NewSealsAd control before result.2 := by
  cases query with
  | inl created =>
    exact newSealsAd_keys control before result.2
      (PqxdhRecordFactsOriginAmbient.initialize_kept modes replace setup codec created control before result supported).keys
  | inr outer =>
    cases outer with
    | inl effect =>
      exact newSealsAd_keys control before result.2
        (PqxdhRecordFactsOriginAmbient.effects_kept modes replace setup codec effect control before result supported).keys
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send =>
          exact serverStep_newSealsAd modes ideal replace setup codec route control safe (.inl send) before result supported
        | inr raw =>
          exact serverStep_newSealsAd modes ideal replace setup codec route control safe (.inr raw) before result supported
      | inr beaconQuery =>
        rcases beaconQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext =>
          exact beaconStep_newSealsAd modes ideal replace setup codec control safe owner (.inl plaintext) before result supported
        | inr raw =>
          exact beaconStep_newSealsAd modes ideal replace setup codec control safe owner (.inr raw) before result supported

/-- Every source dispatcher request of an ideal CTX world keeps the seal-context invariant. -/
theorem handler_sealAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (before : CtxPrivate n) (good : SealAd control before)
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run control)).run before)) :
    SealAd result.1.2 result.2 := by
  have reached := support_run_fst (ctxInterpreter modes replace setup codec) _ before result supported
  exact sealAd_step control result.1.2 before result.2 good
    (handler_newSealsAd modes ideal replace setup codec route query control safe before result supported)
    (PqxdhRecordLiftProtocolHistory.handler codec.frameRead route query control safe result.1 reached)
    (handler_adKept codec.frameRead route query control result.1 reached)

/-- Every adaptive source schedule of an ideal CTX world keeps the seal-context invariant. -/
theorem schedule_sealAd {Result : Type} (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (before : CtxPrivate n) (good : SealAd control before)
    (result : (Result × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route client control)).run before)) :
    SealAd result.1.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing control before result with
  | pure value =>
    simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact good
  | query_bind query next ih =>
    simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨inner, reached, continued⟩ := supported
    have progress := PqxdhRecordLiftProtocolHistory.handler codec.frameRead route query control safe inner.1
      (support_run_fst (ctxInterpreter modes replace setup codec) _ before inner reached)
    exact ih inner.1.1 inner.1.2 progress.1 inner.2
      (handler_sealAd modes ideal replace setup codec route query control safe before good inner reached) result continued

/-- The initial control and empty dictionaries satisfy the seal-context invariant. -/
theorem initial_sealAd : SealAd (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n)
    CtxPrivate.initial := by
  intro label entry member
  exact False.elim (List.not_mem_nil member)

/-- Every supported outcome of every ideal CTX world (replay or random mode at every coordinate, any environment and adversary) satisfies the seal-context invariant. -/
theorem ctxRun_sealAd (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    SealAd result.1.2 result.2 :=
  schedule_sealAd modes ideal replace setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftProtocolHistory.initial_safe CtxPrivate.initial
    initial_sealAd result supported

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handleAd_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handleAd_peer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handleAd_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handleAd_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.adKept_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.adKept_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.adKept_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.adKept_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.adKept_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.adKept_of

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.initialize_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.initialize_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.lift_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.lift_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.installServer_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.installServer_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.installBeacon_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.installBeacon_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.capability_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.capability_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.effects_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.effects_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.server_store_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.server_store_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.server_raw_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.server_raw_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.beacon_store_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.beacon_store_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.serverStep_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.serverStep_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.beaconStep_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.beaconStep_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handler_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handler_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.schedule_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.schedule_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.interpreted_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.interpreted_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.native_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.native_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.native_program_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.native_program_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.full_adKept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.full_adKept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealsBy_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealsBy_keys

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealsBy_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealsBy_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealing_sealsBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealing_sealsBy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.kernelSend_sealsBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.kernelSend_sealsBy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.knownSend_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.knownSend_keys

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.knownReceive_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.knownReceive_keys

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ownerSend_sealsBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ownerSend_sealsBy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ownerReceive_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ownerReceive_keys

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ownerRun_sealsBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ownerRun_sealsBy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.newSealsAd_of_sealsBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.newSealsAd_of_sealsBy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.newSealsAd_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.newSealsAd_keys

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.serverStep_newSealsAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.serverStep_newSealsAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.beaconStep_newSealsAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.beaconStep_newSealsAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealAd_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.sealAd_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handler_newSealsAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handler_newSealsAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handler_sealAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.handler_sealAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.schedule_sealAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.schedule_sealAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.initial_sealAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.initial_sealAd

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ctxRun_sealAd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeSeal.ctxRun_sealAd
