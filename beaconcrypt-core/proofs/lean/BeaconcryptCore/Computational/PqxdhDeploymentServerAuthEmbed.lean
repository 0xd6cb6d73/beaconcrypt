-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent
import BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication

/-! The embedding `R_c` of the common deployment experiment into the Server-authentication game (CE-8). For a creation index `c`, `embed` answers every query of a source14 program with field reads, as a ServerAuth adversary started on the target's public input: coins, accepts, builds, public HMAC, BLAKE2b and Server kernel reveals are forwarded unchanged (restriction 5: Server records are the program's own local work on revealed kernels); the `c`-th create, when its pin and key ID are the protected Server binding of the input, becomes the ServerAuth target, whose first bundle is answered with the target's published Phase 1 from the input, whose later bundles answer nothing, whose finish answers nothing before that first bundle and is the ServerAuth finish after it, and whose field reads answer nothing; every other create makes a local Beacon, drawn with the game's coins exactly as the native constructor draws it, whose bundles and kernel reads are local and whose finish runs the literal native owner program with local callbacks: preparation, KEM decapsulation and DH locally, the root as one public HMAC on the zero-salt Extract slice followed by real Expand, record HKDF and AEAD locally and BLAKE2b through the public hash. `freezeImpl` journals every query of a program and, once a stop predicate holds on the journal, answers every later query with a fixed default without issuing it. `adversary` is `R_c`: the frozen program under the embedding, with the stop of `c` (`PqxdhDeploymentServerAuthEvent.Stop`) on the journal's registration view. The section "Routing" shows that a coin computation and the local root, run through the singleton route and the source14 handler, are the native computations up to the analysis histories. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhSecretInputKdf
open PqxdhDeploymentServerAuthEvent (SourceEntry regsOfSource Stop)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointGapDh (ScalarBytes sampleScalar)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The source14 interface with explicit Beacon field reads. -/
abbrev SourceSpec (KemSK : Type) := PqxdhRegistrationJointRevealSchedule.Spec KemSK

/-- A source14 owner. -/
abbrev Owner (KemSK : Type) := PqxdhRegistrationSchedule.Owner KemSK

/-! ## Journal and freeze -/

/-- Journal every query; once the stop predicate holds on the journal, answer every query with the default and issue nothing. -/
def freezeImpl {κ : Type} {spec : OracleSpec κ} (dflt : (query : spec.Domain) → spec.Range query)
    (stop : List ((query : spec.Domain) × spec.Range query) → Prop) [DecidablePred stop] :
    QueryImpl spec (StateT (List ((query : spec.Domain) × spec.Range query)) (OracleComp spec)) := fun query journal =>
  if stop journal then pure (dflt query, journal)
  else (fun reply => (reply, journal ++ [⟨query, reply⟩])) <$> (spec.query query : OracleComp spec _)

/-- A program frozen at the stop, returning its result and its journal. -/
def freeze {κ : Type} {spec : OracleSpec κ} (dflt : (query : spec.Domain) → spec.Range query)
    (stop : List ((query : spec.Domain) × spec.Range query) → Prop) [DecidablePred stop] {α : Type}
    (program : OracleComp spec α) : OracleComp spec (α × List ((query : spec.Domain) × spec.Range query)) :=
  (simulateQ (freezeImpl dflt stop) program).run []

/-- Default replies of the source14 interface, used only after the stop. -/
def dflt : (query : (SourceSpec KemSK).Domain) → (SourceSpec KemSK).Range query
  | .inl (.inl coin) => (0 : Fin (coin + 1))
  | .inl (.inr (.create _ _)) => (0 : Nat)
  | .inl (.inr (.bundle _)) => none
  | .inl (.inr (.accept _)) => none
  | .inl (.inr (.build _ _)) => none
  | .inl (.inr (.finish _ _)) => none
  | .inl (.inr (.hmac _ _)) => zeroSalt
  | .inl (.inr (.hash _)) => List.Vector.replicate 64 0
  | .inl (.inr (.reveal _)) => none
  | .inr _ => none

/-- The stop of creation index `c` on a source14 journal. -/
def stopAt (c : Nat) (journal : List (SourceEntry KemSK)) : Prop := Stop c (regsOfSource journal)

instance (c : Nat) : DecidablePred (stopAt (KemSK := KemSK) c) := fun journal => by
  unfold stopAt
  infer_instance

/-! ## Local Beacons -/

/-- Uniform coins of a probabilistic computation, as ServerAuth coin queries. -/
def coins {α : Type} (work : ProbComp α) : OracleComp ServerAuthSpec α :=
  simulateQ (fun query => (ServerAuthSpec.query (.inl query) : OracleComp ServerAuthSpec _)) work

/-- A ServerAuth query other than a coin. -/
def forward (query : ServerAuthQuery) : OracleComp ServerAuthSpec (QuerySpec query) :=
  (ServerAuthSpec.query (.inr query) : OracleComp ServerAuthSpec _)

/-- A local Beacon: the native constructor's identity, prekey and KEM draws in production order, and the fresh owner they give. -/
noncomputable def localCreate (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) : ProbComp (Owner KemSK) := do
  let identity ← sampleSeed
  let prekey ← sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  pure ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩

/-- A local bundle: the native bundle program of the owner with its own signing callbacks. -/
def localBundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (owner : Owner KemSK) :
    ProbComp (Option Pqxdh.Bytes × Owner KemSK) :=
  simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
    (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner)

/-- The root of a local Beacon: one public HMAC on the zero-salt Extract slice, then real Expand. -/
def localRoot (setup : Setup baseSpec KemSK) (input : pqxdh.RootKeyInput) : OracleComp ServerAuthSpec (Option Word32) :=
  (fun prk => some (PqxdhRootTableInitialization.rootArray (expandRoot setup.hmac prk))) <$>
    forward (.hmac zeroSalt (absBytes input.bytes))

/-- The callbacks of a local Beacon's finish: preparation, decapsulation and DH locally with the game's coins, the root through `localRoot`, record HKDF, AEAD opening and the initial KDF locally, BLAKE2b through the public hash. -/
noncomputable def localCallbacks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) (OracleComp ServerAuthSpec)
  | .inl query => coins (PqxdhRegistrationSchedule.preparation setup codec query)
  | .inr (.inl (.inl request)) => pure (RawCtxSourceHkdf.response setup.source.crypto request)
  | .inr (.inl (.inr (.inl bytes))) => (fun digest => some digest.toList) <$> forward (.hash bytes)
  | .inr (.inl (.inr (.inr input))) => pure (RawCtxSourceOpen.baseOpen setup.source.crypto input)
  | .inr (.inr (.root input)) => localRoot setup input
  | .inr (.inr (.initial request)) => pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request)
  | .inr (.inr (.application response)) => pure (codec.application response)

/-! ## The embedding -/

/-- The embedding's view of creation index `c`: not yet created; created as the ServerAuth target and not yet bundled; bundled with the target's published Phase 1; first bundle rejected; or created with another binding and simulated locally. -/
inductive Slot where
  | waiting
  | fresh
  | bundled
  | failed
  | released
  deriving DecidableEq

/-- The embedding's state: one entry per created owner in creation order, a local owner or the target's placeholder, and the slot of `c`. -/
structure Emb (KemSK : Type) where
  owners : List (Option (Owner KemSK))
  slot : Slot

/-- The initial state: no owner, `c` not yet created. -/
def Emb.empty : Emb KemSK := ⟨[], .waiting⟩

/-- The protected Server binding of a ServerAuth input. -/
def inputBinding (input : AuthInput) : Word32 × Std.U64 :=
  (PqxdhRootTableInitialization.rootArray input.server.ed25519, input.serverKeyId)

open Classical in
/-- The embedding of a source14 program at creation index `c`, as a ServerAuth adversary on `input`. -/
noncomputable def embed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput) :
    QueryImpl (SourceSpec KemSK) (StateT (Emb KemSK) (OracleComp ServerAuthSpec))
  | .inl (.inl coin) => StateT.lift (ServerAuthSpec.query (.inl coin) : OracleComp ServerAuthSpec _)
  | .inl (.inr (.create pin keyId)) => fun emb =>
      if emb.owners.length = c ∧ emb.slot = .waiting ∧ (pin, keyId) = inputBinding input then
        pure (c, { emb with owners := emb.owners ++ [none], slot := .fresh })
      else
        (fun owner => (emb.owners.length, { emb with
          owners := emb.owners ++ [some owner]
          slot := if emb.owners.length = c ∧ emb.slot = .waiting then .released else emb.slot })) <$>
          coins (localCreate setup pin keyId)
  | .inl (.inr (.bundle index)) => fun emb =>
      match emb.owners[index]? with
      | none => pure (none, emb)
      | some none =>
          if emb.slot = .fresh then
            pure (input.phase1, { emb with slot := if input.phase1.isSome then .bundled else .failed })
          else pure (none, emb)
      | some (some owner) =>
          (fun result => (result.1, { emb with owners := emb.owners.set index (some result.2) })) <$>
            coins (localBundle setup codec index owner)
  | .inl (.inr (.accept raw)) => StateT.lift (forward (.accept raw))
  | .inl (.inr (.build session payload)) => StateT.lift (forward (.build session payload))
  | .inl (.inr (.finish index raw)) => fun emb =>
      match emb.owners[index]? with
      | none => pure (none, emb)
      | some none =>
          if emb.slot = .bundled then (fun reply => (reply, emb)) <$> forward (.finish raw)
          else pure (none, emb)
      | some (some owner) =>
          (fun result => (result.1, { emb with owners := emb.owners.set index (some result.2) })) <$>
            simulateQ (localCallbacks setup codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)
  | .inl (.inr (.hmac key message)) => StateT.lift (forward (.hmac key message))
  | .inl (.inr (.hash bytes)) => StateT.lift (forward (.hash bytes))
  | .inl (.inr (.reveal keyId)) => StateT.lift (forward (.reveal keyId))
  | .inr (index, field) => fun emb =>
      pure ((emb.owners[index]?).bind fun slot => slot.bind (PqxdhRegistrationJointLiveRead.value field), emb)

/-- `R_c` before journaling its own ServerAuth queries: the frozen program under the embedding, from the empty embedding state. -/
noncomputable def embedded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (program : OracleComp (SourceSpec KemSK) Result) (input : AuthInput) :
    OracleComp ServerAuthSpec ((Result × List (SourceEntry KemSK)) × Emb KemSK) :=
  (simulateQ (embed setup codec c input) (freeze dflt (stopAt c) program)).run Emb.empty

/-- The ServerAuth adversary `R_c`: the embedded frozen program together with the journal of its own ServerAuth queries. -/
noncomputable def adversary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (program : OracleComp (SourceSpec KemSK) Result) (input : AuthInput) :
    OracleComp ServerAuthSpec (((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) :=
  PqxdhServerAuthApiJournal.record (embedded setup codec c program input)

/-! ## Routing -/

/-- A coin computation through the singleton route and the source14 handler is the computation itself, with the state unchanged. -/
theorem coins_route {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (work : ProbComp α) (state : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
      (simulateQ PqxdhRegistrationR1Restriction.route (coins work))).run state =
      (fun value => (value, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp [coins]
  | query_bind query next ih =>
      simp only [coins, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind] at ih ⊢
      simp only [PqxdhRegistrationR1Restriction.route, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, PqxdhRegistrationSchedule.handler, StateT.run_lift, bind_assoc, pure_bind, map_bind]
      exact bind_congr fun reply => ih reply state

/-- The local root through the singleton route and the source14 handler is the native root callback on the shared table, up to the analysis histories. -/
theorem localRoot_route (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (input : pqxdh.RootKeyInput) (state : PqxdhRegistrationSchedule.State KemSK) :
    Prod.map id PqxdhRegistrationR1Restriction.eraseShared <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ PqxdhRegistrationR1Restriction.route (localRoot setup input))).run state =
      (fun result => (result.1, PqxdhRegistrationR1Restriction.eraseShared { state with shared := result.2 })) <$>
        (sourceRoot setup.hmac input).run state.shared := by
  have slice : zeroSalt = zeroSalt ∧ (absBytes input.bytes).length = 192 := ⟨rfl, by simp⟩
  simp only [localRoot, forward, simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    PqxdhRegistrationR1Restriction.route, PqxdhRegistrationSchedule.handler, StateT.run_map,
    PqxdhRegistrationSchedule.onShared_run, nativeHmac, slice, and_self, ite_true]
  rw [nativeTouch_bind]
  simp only [PqxdhServerRelatedRootConsumer.familyImpl, QueryImpl.compose, PqxdhJointDhExtractRoot.reduction,
    simulateQ_spec_query, PqxdhExtractRomFamily.romImpl, slice, and_self, ite_true, StateT.run, sourceRoot,
    PqxdhRegistrationR1Restriction.eraseShared, eraseObservers, Functor.map_map, map_bind, map_pure]
  rw [bind_pure_comp]
  rfl

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed.coins_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed.coins_route

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed.localRoot_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed.localRoot_route
