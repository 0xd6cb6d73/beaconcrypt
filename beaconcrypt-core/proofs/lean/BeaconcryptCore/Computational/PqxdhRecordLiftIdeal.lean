-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxModeBounds

/-!
# Record-lift ideal worlds and target statements (items 4 and 5, stage S1)

Definitions only: the ideal worlds of handoff items 4 and 5 and the H-5 target statements as `Prop`-valued definitions. No target statement is proved here. The sanity theorems show that the definitions are well-formed: the all-real chain world is the frozen `PqxdhRecordLiftWorld.run` on the CE-12 analysis projection and game (`realChains_analysis`, `realChains_game`), the depth range is the frozen `Caps.derivations` (`positions_derivations`), mode-O records are `idealAuth` and mode-P records the random-ciphertext world (`idealRecords_O`, `idealRecords_P`), the per-key modes are the endpoints of the existing CTX component bounds (`keyImpl_modes`, `randomImpl_other`), the hidden material is the native material (`materialAt_native`), every non-record service of the CTX world is the chain world's (`ctxInterpreter_base`), malformed and narrow hidden records make no keyed request (`hiddenOpening_malformed`, `hiddenSealing_narrow`), every Boolean form implies its event form (`*_of_bool`), the record lift follows from its three parts (`recordLiftBool_of_parts`), the integrity record lift from the chain lift and the integrity half (`recordAuthLiftBool_of_parts`), `ctx_lift` from its two halves (`ctxLiftBool_of_parts`), the origin's commitment-guessing term is at most the earlier tag-guessing term (`guessTerm_le`), the public hiding projection is the hiding view with the test bit and the fresh messages erased (`publicHiding_hidingView`), the ledger's test admission depends only on the mode-P view (`admittedTest_view`), and the hiding target gives advantage zero (`hiding_advantage`, `hiding_event`).

**Worlds.** All worlds run the same key-free compiled client `PqxdhRecordLiftProtocol.program` (the frozen interface program with the CE ledger wrapper) and differ only in the private interpreter. `chains ideal` interprets it with the mixed lookup policy `PqxdhRecordLiftMixedWorld.policy setup.source ideal`: real HKDF at unselected coordinates and the persistent lazy full76 table at selected ones. `realChains` (all false) is the frozen record world; `idealChains` (all true) is H-4's chain-ideal world. `ctxRun modes replace` keeps `idealChains`' interpreter for every service except the two hidden-record services: an opening or sealing at a hidden material coordinate `c` becomes one keyed CTX request `(c, request)` with the exact request of the existing selected-key consumers (`RawCtxUniversalOpening.call`, `PqxdhRecordLiftCtxServices.sealCall`), answered by the one-key CTX local state of `c` in mode `modes c` with the key and nonce of the table entry of `c`, the world's shared BLAKE2b cache and its counted coins. Mode `real` is `AdaptiveCtxSharedModes.localImpl true`; `replay` is `AdaptiveCtxSharedModes.localImpl false` (real AEAD ciphertexts, private-suffix commitments, replay-dictionary acceptance: the replay endpoint of `PqxdhRecordLiftCtxModeBounds.selected_integrity`); `random` is the replay mode with a uniformly random body of the plaintext's length and a uniformly random tag (the random-seal semantics of the ordinary IND$ random experiment behind `AdaptiveCtxPrivacyGuard.randomView`). A repeated-nonce hidden seal is refused (reply none, no frame): the explicit refusal the refusal terms charge. `idealAuth` is every hidden coordinate in replay mode; `idealRecords` is replay in mode O and random in mode P, with mode-projected replies through the unchanged `asModeO`; `randomRecords` is every hidden coordinate random in either mode. `replace` maps hidden seal plaintexts and is the identity in every world except the hiding comparison.

**Views.** `View` is the permitted record-analysis view: the adversary's output, the world-owned ledger (transcript, test session, fresh messages), the environment's own final state, the tagged produced-frame log, the raw-attempt counters and the public handle-to-slot map of installed hidden kernels. It has no seed, table, label, kernel byte, CTX dictionary, primitive counter or shared cache. The CE-12 analysis projection (`PqxdhRecordLiftWorld.analysis`, consumed through `PqxdhDeploymentEnvironmentJoin.join_analysis`) factors through it (`analysis_chainView`). Chain decisions may additionally read the final shared BLAKE2b cache; CTX decisions may not (decision D4: commitment preimages contain message keys).

**Targets (decisions D1-D4 of the takeover plan).** `ChainLiftStatement` (item 5), `CtxAuthLiftStatement` and `CtxPrivLiftStatement` (item 4 split into integrity and privacy, decision D1) with their composition `CtxLiftStatement` (the brief's `ctx_lift`), `RecordAuthLiftStatement` (the integrity record lift to `idealAuth`, which CE-OR and CE-UKS consume before the privacy half exists), `RecordLiftStatement`, the world-level facts `OriginStatement` and `BindingStatement`, and the hiding facts `HidingStatement` (replacement invariance), `FreshGuessStatement` and `LorStatement` (the final-world secrecy facts of CE-APP and CE-LOR). Each lift is two-sided, has a `boolDistAdvantage` form and an event form, is quantified over every environment with `Frame` and every adversary with `Budget.Respects` (the premises CE-11 discharges as C2a and the adversary budget), takes its reductions as explicit parameters (one per ordered hybrid index of `PqxdhRecordLiftChainOrder`, `positions budget * (n * 2)` of them), bills them in functions of `BillInput` (budget fields, the environment's `Frame` data, fresh bounds, slot count, decision cost), and has explicit alias and refusal term parameters; the `...Target` abbreviations fix those terms to zero (decision D3) and the cross-handle term to `bindingTerm`. The origin target carries the publication-versus-production term of decision D2 (`publicationTerm`, the purely statistical commitment-guessing term `guessTerm` in every ideal CTX world and both modes). A target with free reduction parameters is a statement shape: it is meaningful only with the explicit simulator-built reductions and bills of the theorem that delivers it. The only contracts named are those of brief H-7: `SourceFullCorrect` (chain, record lifts), `FrameReadBack` and `DecoderAgreement` (origin) and `FrameReadBack` (binding); IND$, INT-CTXT, HMAC-PRF and Extract-on-`uniform32` enter only as advantage terms of explicit reductions, and the BLAKE2b ROM is the world's model. No assumption or contract is added. Design notes: `doc/impl/record-lift-ideal.md`.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftIdeal
open PqxdhRecordLiftInterface
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds FrameTag Budget Handle Receiver)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The permitted view -/

/-- The completed client result of the compiled program: the constructed Server's public data, the adversary's output with the world-owned ledger and the environment's own state, and the key-free record control. -/
abbrev Client (n : Nat) (E X : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E) ×
    PqxdhRecordLiftProtocol.Control n

/-- The slot of the hidden kernel installed on a Server peer key ID, read from the actual stored record object. -/
def peerSlot (control : PqxdhRecordLiftProtocol.Control n) (keyId : Std.U64) : Option (Slot n) :=
  control.server.bind fun server => (server.peers keyId).bind fun peer => peer.kernel.origin

/-- The slot of the hidden kernel established on a Beacon owner handle. -/
def ownerSlot (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat) : Option (Slot n) :=
  (control.owners[owner]?).bind PqxdhRecordLiftWorldCompiler.Phase.origin

/-- The public handle-to-slot map of installed hidden kernels; known kernels and absent handles map to none. -/
def handleSlot (control : PqxdhRecordLiftProtocol.Control n) : Handle → Option (Slot n)
  | .peer keyId => peerSlot control keyId
  | .owner owner => ownerSlot control owner

/-- The permitted record-analysis view: output, ledger (transcript, test session, fresh messages) and the environment's final state; tagged produced frames; raw-attempt counters; the handle-to-slot map. No seed, chain table, coordinate label, kernel byte, CTX dictionary, primitive counter or shared cache. -/
structure View (n : Nat) (E X : Type) where
  result : Option (X × PqxdhDeploymentSecrecy.Ledger × E)
  produced : List (FrameTag × PqxdhDeploymentNative.Frame)
  raw : PqxdhRecordLiftWorld.RawCounters
  slots : Handle → Option (Slot n)

/-- Read the view of a completed client with its produced-frame log. -/
def viewOf (client : Client n E X) (produced : List (FrameTag × PqxdhDeploymentNative.Frame)) : View n E X :=
  ⟨client.1.map fun value => (value.2.1.1, value.2.1.2, value.2.2), produced,
    PqxdhRecordLiftProtocol.rawCounters client.2, handleSlot client.2⟩

/-- The CE-12 analysis projection of a view (the shape of `PqxdhRecordLiftWorld.analysis`). -/
def View.analysis (view : View n E X) :
    Option (X × PqxdhDeploymentSecrecy.Ledger × List (FrameTag × PqxdhDeploymentNative.Frame) ×
      PqxdhRecordLiftWorld.RawCounters) :=
  view.result.map fun value => (value.1, value.2.1, view.produced, view.raw)

/-! ### Chain worlds (item 5) -/

/-- The ordered chain hybrid with selector `ideal`: the compiled key-free protocol under the mixed lookup policy. Unselected coordinates call the actual native HKDF; selected coordinates read the persistent lazy full76 table, consistently across rollback and re-derivation. -/
noncomputable def chains (ideal : Label n → Bool) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ProbComp (PqxdhRecordLiftProtocol.RunResult n E X) :=
  PqxdhRecordLiftProtocol.run (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec route env serverKid
    bounds mode adversary

/-- The real record world as a chain hybrid: every coordinate real. -/
noncomputable def realChains (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  chains (fun _ => false) setup codec route env serverKid bounds mode adversary

/-- H-4 `idealChains`: every hidden coordinate's key, nonce and next chain come from the persistent lazy uniform full76 table. -/
noncomputable def idealChains (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  chains (fun _ => true) setup codec route env serverKid bounds mode adversary

/-- The view of a chain-world run. -/
def chainView (result : PqxdhRecordLiftProtocol.RunResult n E X) : View n E X :=
  viewOf result.1 result.2.produced

/-- The final shared BLAKE2b cache of a chain-world run (readable by chain decisions only). -/
def chainCache (result : PqxdhRecordLiftProtocol.RunResult n E X) : CtxRO.QueryCache :=
  result.2.primitive.2

/-! ### CTX key modes (item 4) -/

/-- The per-key CTX mode of a hidden material coordinate. -/
inductive KeyMode where
  | real
  | replay
  | random
  deriving DecidableEq

/-- `idealRecords` keeps real ciphertexts with replay acceptance in mode O and uses random ciphertexts in mode P. -/
def recordMode : Mode → KeyMode
  | .O => .replay
  | .P => .random

abbrev KeyEntry := AdaptiveCtxSharedModes.Entry
abbrev HashSpec := AdaptiveCtxSharedHash.HashSpec

/-- Random-ciphertext sealing: nonce reuse is refused as in every CTX mode; otherwise the body (the plaintext's length) and the 16-byte tag are fresh uniform bytes, the commitment is the private suffix lookup of the replay mode, and the seal is recorded in the replay dictionary. No key and no plaintext byte is read. -/
noncomputable def randomSeal (input : CtxSealInput) (entry : KeyEntry) :
    OracleComp HashSpec (Option CtxRomRecord × KeyEntry) :=
  if input.nonce ∈ entry.1.usedNonces then pure (none, entry)
  else do
    let body ← OracleComp.liftComp ($ᵗ (FixedBytes input.plaintext.length)) HashSpec
    let tag ← OracleComp.liftComp ($ᵗ (FixedBytes 16)) HashSpec
    let commitment ← AdaptiveCtxSharedReplay.localPrivate
      (CtxSplitCache.outerSuffix input.nonce input.context tag.toList) entry
    let record : CtxRomRecord := ⟨body.toList, tag.toList, tag.toList_length, commitment.1⟩
    pure (some record, { commitment.2.1 with
      usedNonces := input.nonce :: commitment.2.1.usedNonces
      successfulSeals := ⟨input, record⟩ :: commitment.2.1.successfulSeals }, commitment.2.2)

/-- The random-ciphertext one-key CTX local state: the replay mode's coins, public hashing and replay-dictionary raw opening, with `randomSeal`. -/
noncomputable def randomImpl (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT KeyEntry (OracleComp HashSpec)) := fun query entry =>
  match query with
  | .inl (.inl coin) => do
      let answer ← HashSpec.query (.inl coin)
      pure (answer, entry)
  | .inl (.inr (.inl hash)) => do
      let answer ← HashSpec.query (.inr hash)
      pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2)
  | .inl (.inr (.inr input)) => randomSeal input entry
  | .inr raw => AdaptiveCtxSharedReplay.localRaw decode raw entry

/-- One-key CTX local state of a mode, with the key of its coordinate. -/
noncomputable def keyImpl (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    KeyMode → QueryImpl ReceiveSpec (StateT KeyEntry (OracleComp HashSpec))
  | .real => AdaptiveCtxSharedModes.localImpl true decode crypto key
  | .replay => AdaptiveCtxSharedModes.localImpl false decode crypto key
  | .random => randomImpl decode

/-- A private keyed CTX request: a hidden material coordinate (a label, never a key or table byte) and an ordinary one-key CTX request. -/
abbrev KeyedSpec (n : Nat) : OracleSpec (Label n × ReceiveSpec.Domain) := fun query => ReceiveSpec.Range query.2

/-- The total fallback of `PqxdhRecordLiftMaterialTable.material`; availability excludes its use at every reached opening or sealing. -/
def fallbackOutput : PqxdhFullSecretInputKdf.FullOutput := ⟨List.replicate 76 0, by simp⟩

/-- The message key and nonce of a table entry, the same projection as the native material. -/
def materialAt (table : PqxdhRecordLiftChainTable.Table (Slot n)) (label : Label n) :
    PqxdhOrderedChainHybrids.Material :=
  PqxdhOrderedChainHybrids.material ((table label).getD fallbackOutput)

/-- The hidden opening service: the source payload-parser rejection, the actual total getters (on chains read from the table) and the AD-width check, then one keyed raw request at the material coordinate with the universal envelope of `RawCtxUniversalOpening.call`, and the source API reply. -/
noncomputable def hiddenOpening (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (pending : PqxdhRecordLiftProtocol.Opening n) :
    OracleComp (KeyedSpec n) (core.option.Option RawCtxWholeOwner.Decrypted) :=
  match RawCtxFrameDecoding.fromPayload pending.context.frame.payload with
  | none => pure .None
  | some _ =>
    match RawCtxInterpretedArguments.openArguments
        (RawCtxChainInterpretation.mapOpeningChains (PqxdhRecordLiftChainTable.chain seeds table)
          (PqxdhRecordLiftChainTable.chain seeds table) pending) with
    | none => pure .None
    | some input =>
      if width : input.context.associatedData.length = 153 then
        RawCtxSharedOpeningConsumer.apiReply input.sequence input.context <$>
          ((KeyedSpec n).query (input.material, .inr (RawCtxUniversalDecoder.pack
            (RawCtxUniversalDecoder.envelope (materialAt table input.material).2 input.context width))) :
            OracleComp (KeyedSpec n) (Option Pqxdh.Bytes))
      else pure .None

/-- Hidden seal plaintext replacement (the identity except in the hiding comparison). -/
def replaceContext (replace : Pqxdh.Bytes → Pqxdh.Bytes) (context : RawCtxSourceSend.SealContext) :
    RawCtxSourceSend.SealContext :=
  { context with plaintext := replace context.plaintext }

/-- The hidden sealing service: the AD-width check, one keyed seal request at the material coordinate with the selected input of `PqxdhRecordLiftCtxServices.sealCall`, then the literal frame log before the writer result and the source API reply. A refused (repeated-nonce) seal returns none and logs nothing: the explicit refusal that the refusal terms charge. -/
noncomputable def hiddenSealing (writer : RawCtxMixedShared.Writer) (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n) :
    StateT PqxdhRecordLiftLoggedAdapters.Frames (OracleComp (KeyedSpec n)) (Option RawCtxSourceSend.Encrypted) :=
  fun frames =>
  if width : (replaceContext replace pending.context).associatedData.length = 153 then do
    let reply ← ((KeyedSpec n).query (pending.material, .inl (.inr (.inr
      (RawCtxSelectedMessageSealing.selectedInput (materialAt table pending.material).2 pending.sequence
        (replaceContext replace pending.context) width)))) : OracleComp (KeyedSpec n) (Option CtxRomRecord))
    match reply with
    | none => pure (none, frames)
    | some record =>
        let frame : RawCtxReceive.DecodedFrame :=
          ⟨pending.sequence, pending.context.senderId, record.encode⟩
        pure ((writer frame).map fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩,
          frames ++ [frame])
  else pure (none, frames)

/-- The CTX world's private state: `idealChains`' private state and one CTX local state per hidden material coordinate. -/
structure CtxPrivate (n : Nat) where
  base : PqxdhRecordLiftProtocol.Private n
  keys : Label n → KeyEntry

def CtxPrivate.initial : CtxPrivate n :=
  ⟨PqxdhRecordLiftProtocol.initialPrivate, fun _ => AdaptiveCtxSharedModes.initialEntry⟩

/-- Answer a keyed request by the coordinate's CTX local state in its mode, with the key of the coordinate's table entry, the world's shared BLAKE2b cache and the world's counted coins. -/
noncomputable def keyed (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp) := fun query state => do
  let result ← (PqxdhRecordLiftProtocol.sampled ((simulateQ AdaptiveCtxSharedHash.hashImpl
    ((keyImpl decode crypto (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
      (state.keys query.1))).run state.base.primitive.2)).run state.base
  pure (result.1.1.1, ⟨{ result.2 with primitive := (result.2.primitive.1, result.1.2) },
    Function.update state.keys query.1 result.1.1.2⟩)

/-- Run a service of the chain world on the base private state. -/
def onBase {α : Type} (work : StateT (PqxdhRecordLiftProtocol.Private n) ProbComp α) :
    StateT (CtxPrivate n) ProbComp α := fun state =>
  (fun result => (result.1, { state with base := result.2 })) <$> work.run state.base

/-- The all-ideal lookup policy of `idealChains`. -/
noncomputable def idealPolicy (setup : Setup baseSpec KemSK) : PqxdhRecordLiftWorldCompiler.LookupPolicy n :=
  PqxdhRecordLiftMixedWorld.policy setup.source (fun _ => true)

/-- The CTX-mode private interpreter: hidden openings and sealings go through their coordinate's CTX mode; every other service (allocation, coins, hashes, charges, lookups, known-kernel sends and receives, publication) is `idealChains`' service on the base state. -/
noncomputable def ctxInterpreter (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .opening pending => fun state =>
      (simulateQ (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run
          state
  | .sealing pending => fun state => do
      let result ← (simulateQ (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        ((hiddenSealing codec.frameWrite state.base.chain replace pending).run state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })
  | query => onBase (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec query)

/-- The CTX-mode world: the same compiled client under `ctxInterpreter`. -/
noncomputable def ctxRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : ProbComp (Client n E X × CtxPrivate n) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      CtxPrivate.initial

/-- The view of a CTX-world run. -/
def ctxView (result : Client n E X × CtxPrivate n) : View n E X :=
  viewOf result.1 result.2.base.produced

/-- H-4 integrity ideal world: every hidden coordinate's CTX in replay mode (real ciphertexts, replay-dictionary acceptance). -/
noncomputable def idealAuth (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  ctxRun (fun _ => .replay) id setup codec route env serverKid bounds mode adversary

/-- H-4 `idealRecords`: `idealAuth` plus random ciphertexts in mode P; replies are mode-projected by the program's unchanged `asModeO`. -/
noncomputable def idealRecords (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  ctxRun (fun _ => recordMode mode) id setup codec route env serverKid bounds mode adversary

/-- Every hidden coordinate with random ciphertexts, in either observation mode: `idealRecords` in mode P and the right world of the privacy half. The mode-O instance is kept but no target consumer needs it (decision D2 has no IND$ step). -/
noncomputable def randomRecords (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  ctxRun (fun _ => .random) id setup codec route env serverKid bounds mode adversary

/-! ### Losses, reductions and bills -/

/-- The ordered-hybrid depth range `P = S + 51 R` (`Caps.derivations`). -/
def positions (budget : Budget) : Nat := budget.sends + 51 * budget.receives

/-- The ordered hybrid indices of `PqxdhRecordLiftChainOrder` (depth-major cells of `positions budget` depths, `n` slots and two directions); the same index set enumerates target keys. -/
def hops (n : Nat) (budget : Budget) : Nat := positions budget * (n * 2)

/-- Everything a bill may depend on: the outer command budget, the environment's startup coins and per-class allowance (its `Frame`), the fresh-message bounds, the slot count and the decision's own coin cost. -/
structure BillInput where
  budget : Budget
  startup : Nat
  allowance : Fin 14 → EffectKind → Nat
  fresh : FreshBounds
  slots : Nat
  decision : Nat

/-- One chain hop's loss for its full76 observer: Extract on `uniform32` plus HMAC-PRF, each with coefficient one (the right side of `PqxdhRecordLiftGlobalCut.observed_bound` and `PqxdhRecordLiftGlobalSeedCut.observed_bound`). -/
noncomputable def hopLoss (hmac : PqxdhSecretInputKdf.HmacSha512)
    (observer : PqxdhFullSecretInputKdf.FullObserver Unit) : ℝ≥0∞ :=
  ENNReal.ofReal ((PqxdhSecretInputKdf.extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (PqxdhFullSecretInputKdf.fullExtractReduction hmac .ratchet observer)).boolDistAdvantage
    (PqxdhSecretInputKdf.extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (PqxdhFullSecretInputKdf.fullExtractReduction hmac .ratchet observer))) +
  ENNReal.ofReal ((PqxdhSecretInputKdf.hmacPrfRealGame hmac
      (PqxdhFullSecretInputKdf.fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32 observer)).boolDistAdvantage
    (PqxdhSecretInputKdf.hmacPrfRandomGame
      (PqxdhFullSecretInputKdf.fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32 observer)))

/-- One target key's integrity loss for its ordinary one-key CTX adversary with hash cap `qHash` and raw cap `qRaw`: the terms of `PqxdhRecordLiftCtxModeBounds.selected_integrity` (IND$ validation, `qHash/2^128`, twice the attempt-indexed INT-CTXT sum, `qRaw/2^512`). -/
noncomputable def integrityLoss (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (client : OracleComp ReceiveSpec Bool)
    (qHash qRaw : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage crypto
    (AdaptiveCtxPrefixValidation.validationReduction decode crypto client qHash)) +
  (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
  2 * ∑ index ∈ Finset.range qRaw, CtxNonceAeadIntCtxt.modifiedNonceAeadINTCTXTAdvantage crypto
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode client) index) +
  (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat)

/-- One target key's replay-to-random privacy loss: exactly the ordinary IND$ advantage of the view reduction (`AdaptiveCtxPrivacyGuard.replay_random_advantage`). -/
noncomputable def privacyLoss (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (client : OracleComp ReceiveSpec Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage crypto
    (AdaptiveCtxPrivacyGuard.viewReduction decode client))

/-- Decision D2, every ideal CTX world and both modes: guessing an unpublished hidden record, `2 · R · S / 2^512`. In replay and random mode the commitment of a hidden seal is a uniform 64-byte value of the coordinate's private suffix dictionary (`AdaptiveCtxSharedReplay.localPrivate`), never written to the shared cache, and replay acceptance needs the full record including it. A produced but unpublished seal (its writer failed) leaks at most the writer's success bit (the factor 2); each of the at most `R` raw attempts is tested against at most `S` hidden seals. The commitments of distinct seals are independent, so a published commitment gives no information about an unpublished one. The bound does not rest on the 16-byte tag: once the writer's success bit leaks information about a frame, a tag-guessing argument fails, while the 64-byte commitment absorbs that bit in the factor 2. `guessTerm_le` shows the term is at most the tag-guessing term `R · S / 2^128` of the first S1 draft. -/
noncomputable def guessTerm (budget : Budget) : ℝ≥0∞ :=
  ((2 * budget.receives * budget.sends : Nat) : ℝ≥0∞) * (((2 ^ 512 : Nat) : ℝ≥0∞))⁻¹

/-- The shared-hash total of `PqxdhRecordLiftWorldBudget.run_hash`: public BLAKE2b queries, one commitment query per send and per raw receive, and the environment's hash allowance. -/
def sharedHashTotal (input : BillInput) : Nat :=
  input.budget.hash + input.budget.sends + input.budget.receives + Caps.envTotal ⟨input.budget, 0⟩ input.allowance .hash

/-- The intended cross-handle term of `BindingStatement`, `(R + S + H) · S / 2^512` with `H = sharedHashTotal`: a frame crossing to a non-partner handle needs a shared-cache output (at most `R + S + H` of them) or a second private commitment to equal one of at most `S` private uniform 64-byte commitments. -/
noncomputable def bindingTerm (input : BillInput) : ℝ≥0∞ :=
  (((input.budget.receives + input.budget.sends + sharedHashTotal input) * input.budget.sends : Nat) : ℝ≥0∞) *
    (((2 ^ 512 : Nat) : ℝ≥0∞))⁻¹

/-- A chain reduction family: for every environment, adversary, chain decision and budget, one explicit full76 observer per ordered hybrid index. -/
abbrev ChainReduction (n : Nat) :=
  ∀ {E X : Type}, Environment n E → (mode : Mode) → OracleComp (ModeSpec mode) X →
    (View n E X → CtxRO.QueryCache → ProbComp Bool) → (budget : Budget) → Fin (hops n budget) →
      PqxdhFullSecretInputKdf.FullObserver Unit

/-- A CTX reduction family: for every environment, adversary, cache-free decision and budget, one explicit ordinary one-key CTX adversary per target key index. -/
abbrev CtxReduction (n : Nat) :=
  ∀ {E X : Type}, Environment n E → (mode : Mode) → OracleComp (ModeSpec mode) X →
    (View n E X → ProbComp Bool) → (budget : Budget) → Fin (hops n budget) → OracleComp ReceiveSpec Bool

/-- Chain bills: the uniform coins of each hop's observer (its HMAC queries are the two of `fullExpandReduction`). -/
structure ChainBills where
  observer : BillInput → Nat

/-- CTX bills: explicit uniform, shared-hash, seal and raw caps of each per-key adversary. -/
structure CtxBills where
  uniform : BillInput → Nat
  hash : BillInput → Nat
  seals : BillInput → Nat
  raw : BillInput → Nat

/-- A per-key CTX adversary respects its bills. -/
def CtxBounded (client : OracleComp ReceiveSpec Bool) (bills : CtxBills) (input : BillInput) : Prop :=
  client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform (bills.uniform input) ∧
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash (bills.hash input) ∧
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal (bills.seals input) ∧
    client.IsQueryBoundP IsRawQuery (bills.raw input)

/-- The zero term: the intended instantiation of the aliasing and refusal parameters (decision D3). -/
def noTerm : BillInput → ℝ≥0∞ := fun _ => 0

/-! ### Origin events (CE-OR, CE-UKS) -/

/-- The receiving handle of a raw record attempt: a Server raw receive is routed by the public header decoder. -/
def receivingHandle (route : RawCtxServerRouting.SenderDecoder) : Receiver → Pqxdh.Bytes → Option Handle
  | .server, raw => (route raw).map Handle.peer
  | .owner owner, _ => some (.owner owner)

/-- The counterpart of a receiving handle of `slot`: the opposite role's handle holding the same slot. -/
def Counterpart (slots : Handle → Option (Slot n)) (slot : Slot n) : Handle → Handle → Prop
  | .peer _, .owner owner => slots (.owner owner) = some slot
  | .owner _, .peer keyId => slots (.peer keyId) = some slot
  | _, _ => False

/-- `frame` is the frame of a ciphertext returned on `handle` in the transcript prefix `before`. -/
def PublishedBefore (codec : Codec Reader Response) (before : List PqxdhDeploymentInterface.Entry)
    (handle : Handle) (frame : PqxdhDeploymentNative.Frame) : Prop :=
  ∃ encrypted, (handle, encrypted) ∈ before.filterMap PqxdhDeploymentInterface.Entry.published ∧
    codec.frameRead encrypted.ciphertext = some frame

/-- A transcript entry is an accepted raw receive on a hidden handle of some slot, whose frame no counterpart handle of that slot published earlier. -/
def ForgedAt (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (slots : Handle → Option (Slot n)) (before : List PqxdhDeploymentInterface.Entry)
    (entry : PqxdhDeploymentInterface.Entry) : Prop :=
  ∃ receiver raw decrypted handle slot frame,
    entry.received = some (receiver, raw, .Some decrypted) ∧ receivingHandle route receiver raw = some handle ∧
      slots handle = some slot ∧ codec.frameRead raw = some frame ∧
      ∀ other, Counterpart slots slot handle other → ¬PublishedBefore codec before other frame

/-- CE-OR's public event on the record world: some accepted target receive was not published by its counterpart before. -/
def UnpublishedAccept (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (view : View n E X) : Prop :=
  ∃ value ∈ view.result, ∃ before entry after, value.2.1.transcript = before ++ entry :: after ∧
    ForgedAt codec route view.slots before entry

/-- The structural event: some accepted target receive carries a frame that no counterpart handle ever produced (published or not). -/
def UnproducedAccept (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (view : View n E X) : Prop :=
  ∃ value ∈ view.result, ∃ entry ∈ value.2.1.transcript, ∃ receiver raw decrypted handle slot frame,
    entry.received = some (receiver, raw, .Some decrypted) ∧ receivingHandle route receiver raw = some handle ∧
      view.slots handle = some slot ∧ codec.frameRead raw = some frame ∧
      ∀ other, Counterpart view.slots slot handle other → (some other, frame) ∉ view.produced

open Classical in
/-- The CE-OR event as a Boolean of the view. -/
noncomputable def unpublishedEvent (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (view : View n E X) : Bool :=
  decide (UnpublishedAccept codec route view)

open Classical in
/-- The structural origin event as a Boolean of the view. -/
noncomputable def unproducedEvent (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (view : View n E X) : Bool :=
  decide (UnproducedAccept codec route view)

/-- Two handles are partners: they have opposite roles and hold the same hidden slot. -/
def Partners (slots : Handle → Option (Slot n)) (first second : Handle) : Prop :=
  ∃ slot, slots first = some slot ∧ Counterpart slots slot first second

/-- CE-UKS's public event on the record world: an accepted raw receive on handle `first` whose frame some handle `second` returned anywhere in the transcript, where one of the two handles holds a hidden slot and they are not partners. The frame is compared after `codec.frameRead`, never as raw bytes. Every Server peer seals with the same sender (the Server identity key ID) and a Beacon's sender is its adversary-delivered assigned ID, so frames of different handles need not differ in their sender field; the event is bounded by the private commitments of the ideal CTX worlds, not by sender binding. Because `second` may have returned the frame before or after the receive, either choice of the designated handle in CE-UKS is contained. -/
def CrossAccept (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (view : View n E X) : Prop :=
  ∃ value ∈ view.result, ∃ entry ∈ value.2.1.transcript, ∃ receiver raw decrypted first second frame,
    entry.received = some (receiver, raw, .Some decrypted) ∧ receivingHandle route receiver raw = some first ∧
      codec.frameRead raw = some frame ∧ PublishedBefore codec value.2.1.transcript second frame ∧
      ((view.slots first).isSome ∨ (view.slots second).isSome) ∧ ¬Partners view.slots first second

open Classical in
/-- The CE-UKS event as a Boolean of the view. -/
noncomputable def crossEvent (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (view : View n E X) : Bool :=
  decide (CrossAccept codec route view)

/-! ### Hiding view (CE-APP, CE-LOR) -/

/-- The type of the hiding projection. -/
abbrev HidingView (n : Nat) (E X : Type) :=
  Option (X × List (PqxdhDeploymentInterface.PublicEntry .P) × Option PqxdhDeploymentSecrecy.TestState ×
      List PqxdhDeploymentSecrecy.FreshEntry × E) ×
    List (FrameTag × PqxdhDeploymentNative.Frame) × PqxdhRecordLiftWorld.RawCounters × (Handle → Option (Slot n))

/-- The mode-P public projection with the secrecy ground truth kept: output, the mode-P view of the transcript, the test session (bit, handle, count), the fresh messages with their replies, the environment state, produced frames, raw counters and the handle-to-slot map. Only the mode-O plaintexts of raw receives are dropped. -/
def hidingView (view : View n E X) : HidingView n E X :=
  (view.result.map fun value => (value.1, value.2.1.transcript.map (PqxdhDeploymentInterface.Entry.view .P),
    value.2.1.test, value.2.1.fresh, value.2.2), view.produced, view.raw, view.slots)

/-- The type of the public hiding projection: the hiding view without the test bit and the fresh messages. -/
abbrev PublicHiding (n : Nat) (E X : Type) :=
  Option (X × List (PqxdhDeploymentInterface.PublicEntry .P) × Option (Handle × Nat) ×
      List (Handle × Option RawCtxSourceSend.Encrypted) × E) ×
    List (FrameTag × PqxdhDeploymentNative.Frame) × PqxdhRecordLiftWorld.RawCounters × (Handle → Option (Slot n))

/-- Erase the secrecy ground truth of a hiding view: the test session keeps its first handle and count, a fresh entry its handle and reply. -/
def eraseSecrets (projection : HidingView n E X) : PublicHiding n E X :=
  (projection.1.map fun value => (value.1, value.2.1, value.2.2.1.map (fun test => (test.first, test.count)),
    value.2.2.2.1.map (fun entry => (entry.handle, entry.reply)), value.2.2.2.2), projection.2)

/-- The public hiding projection of a view (`publicHiding_hidingView`). -/
def publicHiding (view : View n E X) : PublicHiding n E X :=
  (view.result.map fun value => (value.1, value.2.1.transcript.map (PqxdhDeploymentInterface.Entry.view .P),
    value.2.1.test.map (fun test => (test.first, test.count)),
    value.2.1.fresh.map (fun entry => (entry.handle, entry.reply)), value.2.2), view.produced, view.raw, view.slots)

/-- The test bit of the ledger, if a test was admitted. -/
def testBit (view : View n E X) : Option Bool :=
  view.result.bind fun value => value.2.1.test.map PqxdhDeploymentSecrecy.TestState.bit

open Classical in
/-- The handle of a test entry with admissible messages. -/
noncomputable def admissibleTest (entry : PqxdhDeploymentInterface.Entry) : Option Handle :=
  match entry.query with
  | .inr (.test handle left right) => if PqxdhDeploymentSecrecy.Admissible left right then some handle else none
  | _ => none

/-- The handle of the ledger's first admitted test: the first test entry with admissible messages (`PqxdhDeploymentSecrecy.ledgerImpl` admits it and fixes the test session). -/
noncomputable def firstTest (transcript : List PqxdhDeploymentInterface.Entry) : Option Handle :=
  transcript.findSome? admissibleTest

/-- The ledger admits a test after the transcript prefix `before` exactly when its messages are admissible and, if a test was admitted before, the handle has the first test's session (`PqxdhDeploymentSecrecy.ledgerImpl`). -/
def AdmittedTest (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (before : List PqxdhDeploymentInterface.Entry) (handle : Handle) (left right : Pqxdh.Bytes) : Prop :=
  PqxdhDeploymentSecrecy.Admissible left right ∧
    ∀ first, firstTest before = some first → PqxdhDeploymentSecrecy.SameSession crypto codec serverKid before first handle

/-- A test session exists and every test the ledger admitted named a handle holding a hidden slot. Admission is recomputed from the transcript and depends only on its mode-P view (`admittedTest_view`). The slot map is the final one; by the interpreter's installation rules (a vacant peer key ID, an owner in `initSent`) a handle that holds a slot at the end held it at every earlier send or had no installed kernel then. -/
def TestsHidden (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (view : View n E X) :
    Prop :=
  ∃ value ∈ view.result, value.2.1.test.isSome ∧
    ∀ before entry after handle left right, value.2.1.transcript = before ++ entry :: after →
      entry.query = .inr (.test handle left right) → AdmittedTest crypto codec serverKid before handle left right →
      (view.slots handle).isSome

/-- CE-APP's event on the record world: the adversary's output claims index `index` and guess `guess`, the `index`-th admitted fresh message was sent on a handle holding a hidden slot, and the guess is that message. -/
def FreshHit (claim : X → Option (Nat × Pqxdh.Bytes)) (view : View n E X) : Prop :=
  ∃ value ∈ view.result, ∃ index guess entry, claim value.1 = some (index, guess) ∧
    value.2.1.fresh[index]? = some entry ∧ (view.slots entry.handle).isSome ∧ entry.message = guess

open Classical in
/-- The CE-APP event as a Boolean of the view. -/
noncomputable def freshEvent (claim : X → Option (Nat × Pqxdh.Bytes)) (view : View n E X) : Bool :=
  decide (FreshHit claim view)

open Classical in
/-- CE-LOR's eligibility on the record world: a public eligibility predicate holds and every admitted test was on a hidden handle. -/
noncomputable def lorEligible (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (eligible : PublicHiding n E X → Bool) (view : View n E X) : Bool :=
  decide (eligible (publicHiding view) = true ∧ TestsHidden crypto codec serverKid view)

open Classical in
/-- CE-LOR's winning event on the record world: eligible, and a public decision equals the test bit. -/
noncomputable def lorGuess (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (decision eligible : PublicHiding n E X → Bool) (view : View n E X) : Bool :=
  decide (eligible (publicHiding view) = true ∧ TestsHidden crypto codec serverKid view ∧
    testBit view = some (decision (publicHiding view)))

/-! ### Target statements -/

section Targets
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- `chain_lift`, Boolean form: for every environment with `Frame`, adversary with `Budget.Respects` and decision on the view and the final shared cache, the real and chain-ideal worlds differ by at most the sum over the ordered hybrid indices of the hop losses of the supplied observers, plus the aliasing and refusal terms; every observer respects its bill. Contract: `SourceFullCorrect`. -/
def ChainLiftBool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : ChainReduction n)
    (bills : ChainBills) (aliasing refusal : BillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → CtxRO.QueryCache → ProbComp Bool) (cost : Nat),
    (∀ view cache, (decision view cache).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((realChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (chainView result) (chainCache result)).boolDistAdvantage
        (idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (chainView result) (chainCache result))) ≤
      (∑ step, hopLoss hmac (reduction env mode adversary decision budget step)) +
        aliasing ⟨budget, startup, allowance, bounds, n, cost⟩ + refusal ⟨budget, startup, allowance, bounds, n, cost⟩ ∧
    ∀ step context output, (reduction env mode adversary decision budget step context output).IsTotalQueryBound
      (bills.observer ⟨budget, startup, allowance, bounds, n, cost⟩)

/-- `chain_lift`, event form: the same for every Boolean event of the view and the final shared cache. -/
def ChainLiftEvent (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : ChainReduction n)
    (bills : ChainBills) (aliasing refusal : BillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ event : View n E X → CtxRO.QueryCache → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result) (chainCache result)) <$>
        realChains setup codec route env serverKid bounds mode adversary] {true}).toReal -
      (𝒟[(fun result => event (chainView result) (chainCache result)) <$>
        idealChains setup codec route env serverKid bounds mode adversary] {true}).toReal| ≤
      (∑ step, hopLoss hmac (reduction env mode adversary (fun view cache => pure (event view cache)) budget step)) +
        aliasing ⟨budget, startup, allowance, bounds, n, 0⟩ + refusal ⟨budget, startup, allowance, bounds, n, 0⟩ ∧
    ∀ step context output, (reduction env mode adversary (fun view cache => pure (event view cache)) budget step
      context output).IsTotalQueryBound (bills.observer ⟨budget, startup, allowance, bounds, n, 0⟩)

/-- `chain_lift` (H-5, item 5), both forms. -/
def ChainLiftStatement (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : ChainReduction n)
    (bills : ChainBills) (aliasing refusal : BillInput → ℝ≥0∞) : Prop :=
  ChainLiftBool setup codec route serverKid bounds n hmac reduction bills aliasing refusal ∧
    ChainLiftEvent setup codec route serverKid bounds n hmac reduction bills aliasing refusal

/-- `ctx_lift`, integrity half (decision D1), Boolean form: in either mode, the chain-ideal and integrity-ideal worlds differ, for every cache-free decision, by at most the exact sum over target key indices of the per-key integrity losses of the supplied one-key adversaries at their hash and raw bills, plus the refusal term; every adversary respects its bills. -/
def CtxAuthLiftBool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (reduction : CtxReduction n)
    (bills : CtxBills) (refusal : BillInput → ℝ≥0∞) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (idealAuth setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (ctxView result))) ≤
      (∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
        (reduction env mode adversary decision budget step)
        (bills.hash ⟨budget, startup, allowance, bounds, n, cost⟩)
        (bills.raw ⟨budget, startup, allowance, bounds, n, cost⟩)) +
        refusal ⟨budget, startup, allowance, bounds, n, cost⟩ ∧
    ∀ step, CtxBounded (reduction env mode adversary decision budget step) bills
      ⟨budget, startup, allowance, bounds, n, cost⟩

/-- `ctx_lift`, integrity half, event form. -/
def CtxAuthLiftEvent (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (reduction : CtxReduction n)
    (bills : CtxBills) (refusal : BillInput → ℝ≥0∞) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ event : View n E X → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        idealChains setup codec route env serverKid bounds mode adversary] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        idealAuth setup codec route env serverKid bounds mode adversary] {true}).toReal| ≤
      (∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
        (reduction env mode adversary (fun view => pure (event view)) budget step)
        (bills.hash ⟨budget, startup, allowance, bounds, n, 0⟩) (bills.raw ⟨budget, startup, allowance, bounds, n, 0⟩)) +
        refusal ⟨budget, startup, allowance, bounds, n, 0⟩ ∧
    ∀ step, CtxBounded (reduction env mode adversary (fun view => pure (event view)) budget step) bills
      ⟨budget, startup, allowance, bounds, n, 0⟩

/-- `ctx_lift`, integrity half (H-5, item 4), both forms. -/
def CtxAuthLiftStatement (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : CtxReduction n) (bills : CtxBills) (refusal : BillInput → ℝ≥0∞) : Prop :=
  CtxAuthLiftBool setup codec route serverKid bounds n fallback reduction bills refusal ∧
    CtxAuthLiftEvent setup codec route serverKid bounds n fallback reduction bills refusal

/-- `ctx_lift`, privacy half (decision D1), Boolean form: in either mode, the integrity-ideal world and the random-ciphertext world differ, for every cache-free decision, by at most the exact sum over target key indices of the per-key IND$ losses of the supplied view reductions. In mode P the right world is `idealRecords` (`idealRecords_P`). The mode-O instance has no target consumer (the origin target needs no IND$ step); it is kept because the per-key privacy hop is uniform in the observation mode. -/
def CtxPrivLiftBool (n : Nat) (reduction : CtxReduction n) (bills : CtxBills) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((idealAuth setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (ctxView result)).boolDistAdvantage
        (randomRecords setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (ctxView result))) ≤
      (∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (reduction env mode adversary decision budget step)) ∧
    ∀ step, CtxBounded (reduction env mode adversary decision budget step) bills
      ⟨budget, startup, allowance, bounds, n, cost⟩

/-- `ctx_lift`, privacy half, event form. -/
def CtxPrivLiftEvent (n : Nat) (reduction : CtxReduction n) (bills : CtxBills) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ event : View n E X → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (ctxView result)) <$>
        idealAuth setup codec route env serverKid bounds mode adversary] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        randomRecords setup codec route env serverKid bounds mode adversary] {true}).toReal| ≤
      (∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (reduction env mode adversary (fun view => pure (event view)) budget step)) ∧
    ∀ step, CtxBounded (reduction env mode adversary (fun view => pure (event view)) budget step) bills
      ⟨budget, startup, allowance, bounds, n, 0⟩

/-- `ctx_lift`, privacy half (H-5, item 4), both forms. -/
def CtxPrivLiftStatement (n : Nat) (reduction : CtxReduction n) (bills : CtxBills) : Prop :=
  CtxPrivLiftBool setup codec route serverKid bounds n reduction bills ∧
    CtxPrivLiftEvent setup codec route serverKid bounds n reduction bills

/-- The `ctx_lift` loss: the integrity loss and the refusal term and, in mode P, the privacy loss. -/
noncomputable def ctxLoss (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : CtxReduction n) (authBills : CtxBills) (refusal : BillInput → ℝ≥0∞) (env : Environment n E)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (decision : View n E X → ProbComp Bool) (budget : Budget)
    (input : BillInput) : ℝ≥0∞ :=
  ((∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (auth env mode adversary decision budget step) (authBills.hash input) (authBills.raw input)) +
    refusal input) +
  (if mode = .P then ∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (privacy env mode adversary decision budget step) else 0)

/-- The bills of `ctx_lift`: the integrity adversaries and, in mode P, the privacy adversaries. -/
def CtxLiftBounded (n : Nat) (auth privacy : CtxReduction n) (authBills privacyBills : CtxBills)
    (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (input : BillInput) : Prop :=
  (∀ step, CtxBounded (auth env mode adversary decision budget step) authBills input) ∧
    (mode = .P → ∀ step, CtxBounded (privacy env mode adversary decision budget step) privacyBills input)

/-- `ctx_lift` (H-5), Boolean form: the chain-ideal world and `idealRecords` differ, for every cache-free decision, by at most `ctxLoss`; all reductions respect their bills. -/
def CtxLiftBool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (auth privacy : CtxReduction n)
    (authBills privacyBills : CtxBills) (refusal : BillInput → ℝ≥0∞) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (idealRecords setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (ctxView result))) ≤
      ctxLoss setup codec n fallback auth privacy authBills refusal env mode adversary decision budget
        ⟨budget, startup, allowance, bounds, n, cost⟩ ∧
    CtxLiftBounded n auth privacy authBills privacyBills env mode adversary decision budget
      ⟨budget, startup, allowance, bounds, n, cost⟩

/-- `ctx_lift`, event form. -/
def CtxLiftEvent (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (auth privacy : CtxReduction n)
    (authBills privacyBills : CtxBills) (refusal : BillInput → ℝ≥0∞) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ event : View n E X → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        idealChains setup codec route env serverKid bounds mode adversary] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        idealRecords setup codec route env serverKid bounds mode adversary] {true}).toReal| ≤
      ctxLoss setup codec n fallback auth privacy authBills refusal env mode adversary (fun view => pure (event view))
        budget ⟨budget, startup, allowance, bounds, n, 0⟩ ∧
    CtxLiftBounded n auth privacy authBills privacyBills env mode adversary (fun view => pure (event view)) budget
      ⟨budget, startup, allowance, bounds, n, 0⟩

/-- `ctx_lift` (H-5, item 4), both forms: the brief's `|Pr[E | idealChains] - Pr[E | idealRecords]| ≤ ε_ctx`, composed from the integrity and privacy halves by `ctxLiftBool_of_parts`. -/
def CtxLiftStatement (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (auth privacy : CtxReduction n)
    (authBills privacyBills : CtxBills) (refusal : BillInput → ℝ≥0∞) : Prop :=
  CtxLiftBool setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal ∧
    CtxLiftEvent setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal

/-- The record-lift loss: the chain loss at the cache-free decision, the aliasing and both refusal terms, the integrity loss and, in mode P, the privacy loss. -/
noncomputable def recordLoss (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n)
    (auth privacy : CtxReduction n) (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞)
    (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (input : BillInput) : ℝ≥0∞ :=
  ((∑ step, hopLoss hmac (chain env mode adversary (fun view _ => decision view) budget step)) +
    aliasing input + chainRefusal input) +
  ((∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (auth env mode adversary decision budget step) (authBills.hash input) (authBills.raw input)) +
    ctxRefusal input) +
  (if mode = .P then ∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (privacy env mode adversary decision budget step) else 0)

/-- The bills of the record lift: the chain observers, the integrity adversaries and, in mode P, the privacy adversaries. -/
def RecordBounded (n : Nat) (chain : ChainReduction n) (auth privacy : CtxReduction n) (chainBills : ChainBills)
    (authBills privacyBills : CtxBills) (env : Environment n E) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (decision : View n E X → ProbComp Bool) (budget : Budget)
    (input : BillInput) : Prop :=
  (∀ step context output, (chain env mode adversary (fun view _ => decision view) budget step context output).IsTotalQueryBound
      (chainBills.observer input)) ∧
    (∀ step, CtxBounded (auth env mode adversary decision budget step) authBills input) ∧
    (mode = .P → ∀ step, CtxBounded (privacy env mode adversary decision budget step) privacyBills input)

/-- `record_lift`, Boolean form: the real world and `idealRecords` differ, for every cache-free decision, by at most `recordLoss`; all reductions respect their bills. Contract: `SourceFullCorrect`. -/
def RecordLiftBool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth privacy : CtxReduction n)
    (chainBills : ChainBills) (authBills privacyBills : CtxBills)
    (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((realChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (idealRecords setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (ctxView result))) ≤
      recordLoss setup codec n hmac fallback chain auth privacy authBills aliasing chainRefusal ctxRefusal env mode
        adversary decision budget ⟨budget, startup, allowance, bounds, n, cost⟩ ∧
    RecordBounded n chain auth privacy chainBills authBills privacyBills env mode adversary decision budget
      ⟨budget, startup, allowance, bounds, n, cost⟩

/-- `record_lift`, event form. -/
def RecordLiftEvent (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth privacy : CtxReduction n)
    (chainBills : ChainBills) (authBills privacyBills : CtxBills)
    (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ event : View n E X → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        realChains setup codec route env serverKid bounds mode adversary] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        idealRecords setup codec route env serverKid bounds mode adversary] {true}).toReal| ≤
      recordLoss setup codec n hmac fallback chain auth privacy authBills aliasing chainRefusal ctxRefusal env mode
        adversary (fun view => pure (event view)) budget ⟨budget, startup, allowance, bounds, n, 0⟩ ∧
    RecordBounded n chain auth privacy chainBills authBills privacyBills env mode adversary
      (fun view => pure (event view)) budget ⟨budget, startup, allowance, bounds, n, 0⟩

/-- `record_lift` (H-5), both forms. -/
def RecordLiftStatement (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth privacy : CtxReduction n)
    (chainBills : ChainBills) (authBills privacyBills : CtxBills)
    (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) : Prop :=
  RecordLiftBool setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills privacyBills
      aliasing chainRefusal ctxRefusal ∧
    RecordLiftEvent setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal

/-- The integrity record-lift loss: the chain loss at the cache-free decision, the aliasing and both refusal terms, and the integrity loss. -/
noncomputable def recordAuthLoss (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) (env : Environment n E)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (decision : View n E X → ProbComp Bool) (budget : Budget)
    (input : BillInput) : ℝ≥0∞ :=
  ((∑ step, hopLoss hmac (chain env mode adversary (fun view _ => decision view) budget step)) +
    aliasing input + chainRefusal input) +
  ((∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (auth env mode adversary decision budget step) (authBills.hash input) (authBills.raw input)) +
    ctxRefusal input)

/-- The bills of the integrity record lift: the chain observers and the integrity adversaries. -/
def RecordAuthBounded (n : Nat) (chain : ChainReduction n) (auth : CtxReduction n) (chainBills : ChainBills)
    (authBills : CtxBills) (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) (budget : Budget) (input : BillInput) : Prop :=
  (∀ step context output, (chain env mode adversary (fun view _ => decision view) budget step context output).IsTotalQueryBound
      (chainBills.observer input)) ∧
    ∀ step, CtxBounded (auth env mode adversary decision budget step) authBills input

/-- The integrity record lift (decision D1), Boolean form: in either mode, the real world and `idealAuth` differ, for every cache-free decision, by at most `recordAuthLoss`; all reductions respect their bills. It needs no privacy reduction, so CE-OR and CE-UKS consume it before the privacy half exists. Contract: `SourceFullCorrect`. -/
def RecordAuthLiftBool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (chainBills : ChainBills) (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ (decision : View n E X → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((realChains setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (idealAuth setup codec route env serverKid bounds mode adversary >>= fun result =>
          decision (ctxView result))) ≤
      recordAuthLoss setup codec n hmac fallback chain auth authBills aliasing chainRefusal ctxRefusal env mode
        adversary decision budget ⟨budget, startup, allowance, bounds, n, cost⟩ ∧
    RecordAuthBounded n chain auth chainBills authBills env mode adversary decision budget
      ⟨budget, startup, allowance, bounds, n, cost⟩

/-- The integrity record lift, event form. -/
def RecordAuthLiftEvent (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (chainBills : ChainBills) (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  ∀ event : View n E X → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        realChains setup codec route env serverKid bounds mode adversary] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        idealAuth setup codec route env serverKid bounds mode adversary] {true}).toReal| ≤
      recordAuthLoss setup codec n hmac fallback chain auth authBills aliasing chainRefusal ctxRefusal env mode
        adversary (fun view => pure (event view)) budget ⟨budget, startup, allowance, bounds, n, 0⟩ ∧
    RecordAuthBounded n chain auth chainBills authBills env mode adversary (fun view => pure (event view)) budget
      ⟨budget, startup, allowance, bounds, n, 0⟩

/-- The integrity record lift (H-5 `record_lift` to `idealAuth`), both forms. -/
def RecordAuthLiftStatement (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (chainBills : ChainBills) (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞) : Prop :=
  RecordAuthLiftBool setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal ∧
    RecordAuthLiftEvent setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal

/-- The publication-versus-production term of decision D2 (owner input 9), in both observation modes: the commitment-guessing term. No IND$ step and no reduction enter it. -/
noncomputable def publicationTerm (budget : Budget) : ℝ≥0∞ := guessTerm budget

/-- `idealRecords_origin` (H-5): in both ideal CTX worlds and both modes no target receive accepts a frame that its counterpart never produced (probability zero, the replay-dictionary invariant); the CE-OR event (a frame that its counterpart did not publish before) has probability at most the publication term in `idealAuth`, `idealRecords` and `randomRecords`, in both modes. Contracts: `FrameReadBack`, `DecoderAgreement`. -/
def OriginStatement (n : Nat) : Prop :=
  PqxdhServerAuthNegativeControl.FrameReadBack codec → RawCtxServerRouting.DecoderAgreement route codec.frameRead →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      idealAuth setup codec route env serverKid bounds mode adversary] {true} = 0 ∧
    𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds mode adversary] {true} = 0 ∧
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      idealAuth setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget ∧
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget ∧
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      randomRecords setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget

/-- `idealRecords_binding` (H-5 origin, CE-UKS part): in both ideal CTX worlds and both modes, the CE-UKS event `CrossAccept` (a frame accepted on one handle and returned on a non-partner handle, one of them hidden) has probability at most the explicit cross-handle term; `BindingTarget` fixes it to `bindingTerm`. Contract: `FrameReadBack`. -/
def BindingStatement (n : Nat) (crossTerm : BillInput → ℝ≥0∞) : Prop :=
  PqxdhServerAuthNegativeControl.FrameReadBack codec →
  ∀ {E X : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget), budget.Respects adversary →
  𝒟[(fun result => crossEvent codec route (ctxView result)) <$>
      idealAuth setup codec route env serverKid bounds mode adversary] {true} ≤
      crossTerm ⟨budget, startup, allowance, bounds, n, 0⟩ ∧
    𝒟[(fun result => crossEvent codec route (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds mode adversary] {true} ≤
      crossTerm ⟨budget, startup, allowance, bounds, n, 0⟩

/-- `idealRecords_hiding` (H-5), mode P: replacing every hidden seal plaintext by one of equal length leaves the law of the public projection with the secrecy ground truth (`hidingView`) unchanged. No contract. This is the intermediate form; CE-APP and CE-LOR consume the final-world facts `FreshGuessStatement` and `LorStatement`. -/
def HidingStatement (n : Nat) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (adversary : OracleComp (ModeSpec .P) X)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes), (∀ message, (replace message).length = message.length) →
  (fun result => hidingView (ctxView result)) <$>
      ctxRun (fun _ => .random) replace setup codec route env serverKid bounds .P adversary =
    (fun result => hidingView (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds .P adversary

/-- `idealRecords_hiding`, fresh-message form for CE-APP (mode P, every environment and adversary, no `Frame` or budget): for every claim read from the adversary's output, the probability in `idealRecords` that the claimed fresh message was sent on a hidden handle and equals the guess is at most `2^{-min}`. No contract. -/
def FreshGuessStatement (n : Nat) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (adversary : OracleComp (ModeSpec .P) X)
    (claim : X → Option (Nat × Pqxdh.Bytes)),
  𝒟[(fun result => freshEvent claim (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds .P adversary] {true} ≤
    ((2 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹

/-- `idealRecords_hiding`, left-or-right form for CE-LOR (mode P, every environment and adversary, no `Frame` or budget): for every public decision and public eligibility on `PublicHiding`, the probability in `idealRecords` that the run is eligible, every admitted test was on a hidden handle and the decision equals the test bit is half the probability that the run is eligible and every admitted test was on a hidden handle. No contract. -/
def LorStatement (n : Nat) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (adversary : OracleComp (ModeSpec .P) X)
    (decision eligible : PublicHiding n E X → Bool),
  𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds .P adversary] {true} =
    2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds .P adversary] {true}

/-- The intended item 5 target (decision D3): `chain_lift` with zero alias and refusal terms. -/
def ChainLiftTarget (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : ChainReduction n)
    (bills : ChainBills) : Prop :=
  ChainLiftStatement setup codec route serverKid bounds n hmac reduction bills noTerm noTerm

/-- The intended item 4 integrity target (decision D3): zero refusal term. -/
def CtxAuthLiftTarget (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : CtxReduction n) (bills : CtxBills) : Prop :=
  CtxAuthLiftStatement setup codec route serverKid bounds n fallback reduction bills noTerm

/-- The intended `record_lift` target (decision D3): zero alias and refusal terms. -/
def RecordLiftTarget (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth privacy : CtxReduction n)
    (chainBills : ChainBills) (authBills privacyBills : CtxBills) : Prop :=
  RecordLiftStatement setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
    privacyBills noTerm noTerm noTerm

/-- The intended `ctx_lift` target (decision D3): zero refusal term. -/
def CtxLiftTarget (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (auth privacy : CtxReduction n)
    (authBills privacyBills : CtxBills) : Prop :=
  CtxLiftStatement setup codec route serverKid bounds n fallback auth privacy authBills privacyBills noTerm

/-- The intended integrity record-lift target (decision D3): zero alias and refusal terms. -/
def RecordAuthLiftTarget (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (chainBills : ChainBills) (authBills : CtxBills) : Prop :=
  RecordAuthLiftStatement setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills noTerm
    noTerm noTerm

/-- The intended binding target: the cross-handle term `(R + S + H) · S / 2^512`. -/
def BindingTarget (n : Nat) : Prop :=
  BindingStatement setup codec route serverKid bounds n bindingTerm

end Targets

/-! ### Sanity theorems: the definitions are well-formed -/

/-- The ordered-hybrid depth range is the frozen interface's derivation allowance `Caps.derivations` (`sends + 51 * receives`). -/
theorem positions_derivations (caps : Caps) : positions caps.outer = caps.derivations := rfl

/-- The CE-12 analysis projection of the compiled protocol factors through the view. -/
theorem analysis_chainView (result : PqxdhRecordLiftProtocol.RunResult n E X) :
    PqxdhRecordLiftProtocol.analysis result = (chainView result).analysis := by
  rcases result with ⟨⟨_ | value, control⟩, secret⟩ <;> rfl

/-- The all-real chain hybrid is the frozen record world on the CE-12 analysis projection, so `PqxdhDeploymentEnvironmentJoin.join_analysis` composes with every lift stated on the view. -/
theorem realChains_analysis (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    (fun result => (chainView result).analysis) <$> realChains setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary := by
  rw [← PqxdhRecordLiftProtocol.analysis_run_source setup codec route env serverKid bounds mode adversary,
    realChains, chains, PqxdhRecordLiftMixedWorld.policy_real]
  congr 1
  funext result
  exact (analysis_chainView result).symm

/-- The ordered chain hybrid at index zero (`PqxdhRecordLiftChainOrder.selected` with cut zero) is the real chain world. -/
theorem chains_selected_zero (depth : Nat) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    chains (PqxdhRecordLiftChainOrder.selected depth 0) setup codec route env serverKid bounds mode adversary =
      realChains setup codec route env serverKid bounds mode adversary := by
  have same : (PqxdhRecordLiftChainOrder.selected depth 0 : Label n → Bool) = fun _ => false :=
    funext PqxdhRecordLiftChainOrder.selected_zero
  rw [realChains, same]

/-- The all-real chain hybrid is the frozen record world's CE-shaped game (`PqxdhRecordLiftWorld.game`). -/
theorem realChains_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftProtocol.observed <$> realChains setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.game setup codec route env serverKid bounds mode adversary := by
  rw [realChains, chains, PqxdhRecordLiftMixedWorld.policy_real]
  exact PqxdhRecordLiftProtocol.observed_run_source setup codec route env serverKid bounds mode adversary

/-- In mode O the record-ideal world is the integrity-ideal world. -/
theorem idealRecords_O (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .O) X) :
    idealRecords setup codec route env serverKid bounds .O adversary =
      idealAuth setup codec route env serverKid bounds .O adversary := rfl

/-- In mode P the record-ideal world is the random-ciphertext world: every hidden coordinate random, no plaintext replacement. -/
theorem idealRecords_P (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) :
    idealRecords setup codec route env serverKid bounds .P adversary =
      randomRecords setup codec route env serverKid bounds .P adversary := rfl

/-- Real and replay modes are exactly the two endpoints of `PqxdhRecordLiftCtxModeBounds.selected_integrity` (`sourceGame true` and `sourceGame false`). -/
theorem keyImpl_modes (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    keyImpl decode crypto key .real = AdaptiveCtxSharedModes.localImpl true decode crypto key ∧
      keyImpl decode crypto key .replay = AdaptiveCtxSharedModes.localImpl false decode crypto key :=
  ⟨rfl, rfl⟩

/-- Random mode differs from replay mode only on sealing: coins, public hashes and replay-dictionary raw openings are the replay mode's, whatever the key. -/
theorem randomImpl_other (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (query : ReceiveSpec.Domain)
    (notSeal : ¬AdaptiveCtxQueryBounds.SourceSeal query) :
    randomImpl decode query = AdaptiveCtxSharedModes.localImpl false decode crypto key query := by
  rcases query with (coin | (hash | input)) | raw
  · rfl
  · rfl
  · exact absurd trivial notSeal
  · rfl

/-- A coordinate's key and nonce are exactly the native material of the same table entry. -/
theorem materialAt_native (table : PqxdhRecordLiftChainTable.Table (Slot n)) (label : Label n) :
    PqxdhRecordLiftMaterialTable.material table label =
      RawCtxFreshChainCut.concreteMaterial (materialAt table label) := rfl

/-- Every service other than a hidden opening or sealing is `idealChains`' service on the base private state: allocation, coins, hashes, charges, lookups (the persistent lazy table), known-kernel sends and receives, and publication. -/
theorem ctxInterpreter_base (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (notOpening : ∀ pending, query ≠ .opening pending) (notSealing : ∀ pending, query ≠ .sealing pending)
    (state : CtxPrivate n) :
    (ctxInterpreter modes replace setup codec query).run state =
      (fun result => (result.1, { state with base := result.2 })) <$>
        (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec query).run state.base := by
  cases query with
  | opening pending => exact absurd rfl (notOpening pending)
  | sealing pending => exact absurd rfl (notSealing pending)
  | _ => rfl

/-- A hidden opening of a malformed protected payload makes no keyed request and rejects, as the source opening does. -/
theorem hiddenOpening_malformed (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (pending : PqxdhRecordLiftProtocol.Opening n)
    (malformed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = none) :
    hiddenOpening seeds table pending = pure .None := by
  unfold hiddenOpening
  rw [malformed]

/-- A hidden sealing with an associated datum of the wrong width makes no keyed request, logs no frame and returns none, as the source sealing does. -/
theorem hiddenSealing_narrow (writer : RawCtxMixedShared.Writer) (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) (narrow : pending.context.associatedData.length ≠ 153) :
    (hiddenSealing writer table replace pending).run frames = pure (none, frames) :=
  dite_eq_right_of_eq_false (eq_false narrow)

/-- The commitment-guessing term `2 · R · S / 2^512` is at most the tag-guessing term `R · S / 2^128` of the first S1 draft, so every origin bound of the corrected target implies the corresponding bound of that draft. -/
theorem guessTerm_le (budget : Budget) :
    guessTerm budget ≤ ((budget.receives * budget.sends : Nat) : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ := by
  have halve : (2 : ℝ≥0∞) * (((2 ^ 512 : Nat) : ℝ≥0∞))⁻¹ = (((2 ^ 511 : Nat) : ℝ≥0∞))⁻¹ := by
    have split : ((2 ^ 512 : Nat) : ℝ≥0∞) = 2 * ((2 ^ 511 : Nat) : ℝ≥0∞) := by
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_succ' (2 : ℝ≥0∞) 511
    rw [split, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have smaller : (((2 ^ 511 : Nat) : ℝ≥0∞))⁻¹ ≤ (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ := by
    rw [ENNReal.inv_le_inv, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ one_le_two (by norm_num)
  calc guessTerm budget = ((budget.receives * budget.sends : Nat) : ℝ≥0∞) * (2 * (((2 ^ 512 : Nat) : ℝ≥0∞))⁻¹) := by
        rw [guessTerm, Nat.mul_assoc, Nat.cast_mul, Nat.cast_ofNat, mul_comm (2 : ℝ≥0∞), mul_assoc]
    _ ≤ _ := by
        rw [halve]
        exact mul_le_mul_of_nonneg_left smaller zero_le

/-- The public hiding projection is the hiding view with the test bit and the fresh messages erased. -/
theorem publicHiding_hidingView (view : View n E X) : publicHiding view = eraseSecrets (hidingView view) := by
  rcases view with ⟨_ | value, produced, raw, slots⟩ <;> rfl

/-- The ledger's admission of a test depends on the transcript prefix only through its mode-P view, so `TestsHidden` is decided by the public transcript and the slot map. -/
theorem admittedTest_view (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (before other : List PqxdhDeploymentInterface.Entry) (same : PqxdhDeploymentTranscript.SameView before other)
    (handle : Handle) (left right : Pqxdh.Bytes) :
    AdmittedTest crypto codec serverKid before handle left right ↔
      AdmittedTest crypto codec serverKid other handle left right := by
  have first : firstTest before = firstTest other :=
    PqxdhDeploymentTranscript.findSome_view admissibleTest
      (PqxdhDeploymentTranscript.view_respects admissibleTest (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) before other same
  have designated := (PqxdhDeploymentTranscript.designate_view crypto codec serverKid before other same).1
  unfold AdmittedTest PqxdhDeploymentSecrecy.SameSession
  rw [first, designated]

/-- The Boolean advantage of two deterministic decisions is the absolute difference of their event probabilities. -/
theorem pure_advantage {α β : Type} (left : ProbComp α) (right : ProbComp β) (first : α → Bool)
    (second : β → Bool) :
    (left >>= fun value => pure (first value)).boolDistAdvantage (right >>= fun value => pure (second value)) =
      |(𝒟[first <$> left] {true}).toReal - (𝒟[second <$> right] {true}).toReal| := by
  simp only [ProbComp.boolDistAdvantage, bind_pure_comp]

section Relations
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The event form of `chain_lift` is the Boolean form at deterministic decisions, so the Boolean form alone gives the statement. -/
theorem chainLiftStatement_of_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : ChainReduction n)
    (bills : ChainBills) (aliasing refusal : BillInput → ℝ≥0∞)
    (bool : ChainLiftBool setup codec route serverKid bounds n hmac reduction bills aliasing refusal) :
    ChainLiftStatement setup codec route serverKid bounds n hmac reduction bills aliasing refusal := by
  refine ⟨bool, ?_⟩
  intro correct E X env startup allowance frame mode adversary budget respects event
  obtain ⟨bound, billed⟩ := bool correct env startup allowance frame mode adversary budget respects
    (fun view cache => pure (event view cache)) 0 (fun _ _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result) (chainCache result))
    (fun result => event (chainView result) (chainCache result))]
  exact bound

/-- The event form of the integrity half of `ctx_lift` follows from its Boolean form. -/
theorem ctxAuthLiftStatement_of_bool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : CtxReduction n) (bills : CtxBills) (refusal : BillInput → ℝ≥0∞)
    (bool : CtxAuthLiftBool setup codec route serverKid bounds n fallback reduction bills refusal) :
    CtxAuthLiftStatement setup codec route serverKid bounds n fallback reduction bills refusal := by
  refine ⟨bool, ?_⟩
  intro E X env startup allowance frame mode adversary budget respects event
  obtain ⟨bound, billed⟩ := bool env startup allowance frame mode adversary budget respects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- The event form of the privacy half of `ctx_lift` follows from its Boolean form. -/
theorem ctxPrivLiftStatement_of_bool (n : Nat) (reduction : CtxReduction n) (bills : CtxBills)
    (bool : CtxPrivLiftBool setup codec route serverKid bounds n reduction bills) :
    CtxPrivLiftStatement setup codec route serverKid bounds n reduction bills := by
  refine ⟨bool, ?_⟩
  intro E X env startup allowance frame mode adversary budget respects event
  obtain ⟨bound, billed⟩ := bool env startup allowance frame mode adversary budget respects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (ctxView result)) (fun result => event (ctxView result))]
  exact bound

/-- The event form of `record_lift` follows from its Boolean form. -/
theorem recordLiftStatement_of_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth privacy : CtxReduction n)
    (chainBills : ChainBills) (authBills privacyBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞)
    (bool : RecordLiftBool setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal) :
    RecordLiftStatement setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal := by
  refine ⟨bool, ?_⟩
  intro correct E X env startup allowance frame mode adversary budget respects event
  obtain ⟨bound, billed⟩ := bool correct env startup allowance frame mode adversary budget respects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- `record_lift` is the composition of its three parts: the chain lift at the cache-free decision, the integrity half and, in mode P, the privacy half, by the triangle inequality with every term at coefficient one. -/
theorem recordLiftBool_of_parts (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth privacy : CtxReduction n)
    (chainBills : ChainBills) (authBills privacyBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞)
    (chainLift : ChainLiftBool setup codec route serverKid bounds n hmac chain chainBills aliasing chainRefusal)
    (authLift : CtxAuthLiftBool setup codec route serverKid bounds n fallback auth authBills ctxRefusal)
    (privLift : CtxPrivLiftBool setup codec route serverKid bounds n privacy privacyBills) :
    RecordLiftBool setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal := by
  intro correct E X env startup allowance frame mode adversary budget respects decision cost costBound
  obtain ⟨chainBound, chainBilled⟩ := chainLift correct env startup allowance frame mode adversary budget respects
    (fun view _ => decision view) cost (fun view _ => costBound view)
  obtain ⟨authBound, authBilled⟩ := authLift env startup allowance frame mode adversary budget respects decision cost
    costBound
  have first := ProbComp.boolDistAdvantage_triangle
    (realChains setup codec route env serverKid bounds mode adversary >>= fun result => decision (chainView result))
    (idealChains setup codec route env serverKid bounds mode adversary >>= fun result => decision (chainView result))
    (idealRecords setup codec route env serverKid bounds mode adversary >>= fun result => decision (ctxView result))
  cases mode with
  | O =>
      refine ⟨?_, chainBilled, authBilled, fun same => by cases same⟩
      calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal first
        _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ := add_le_add chainBound authBound
        _ = _ := by simp only [recordLoss, reduceCtorEq, ite_false, add_zero]
  | P =>
      obtain ⟨privBound, privBilled⟩ := privLift env startup allowance frame .P adversary budget respects decision cost
        costBound
      refine ⟨?_, chainBilled, authBilled, fun _ => privBilled⟩
      have second := ProbComp.boolDistAdvantage_triangle
        (idealChains setup codec route env serverKid bounds .P adversary >>= fun result => decision (chainView result))
        (idealAuth setup codec route env serverKid bounds .P adversary >>= fun result => decision (ctxView result))
        (idealRecords setup codec route env serverKid bounds .P adversary >>= fun result => decision (ctxView result))
      calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal first
        _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ + ENNReal.ofReal (_ + _) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal second)
        _ = _ + (_ + _) := by
          congr 1
          exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ + (_ + _) := add_le_add chainBound (add_le_add authBound privBound)
        _ = _ := by simp only [recordLoss, ite_true, add_assoc]

/-- The event form of `ctx_lift` follows from its Boolean form. -/
theorem ctxLiftStatement_of_bool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : CtxReduction n) (authBills privacyBills : CtxBills) (refusal : BillInput → ℝ≥0∞)
    (bool : CtxLiftBool setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal) :
    CtxLiftStatement setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal := by
  refine ⟨bool, ?_⟩
  intro E X env startup allowance frame mode adversary budget respects event
  obtain ⟨bound, billed⟩ := bool env startup allowance frame mode adversary budget respects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- `ctx_lift` is the composition of its two halves: in mode O `idealRecords` is `idealAuth` (`idealRecords_O`) and the integrity half alone gives it; in mode P the triangle inequality through `idealAuth` adds the privacy half (`idealRecords_P`), every term with coefficient one. -/
theorem ctxLiftBool_of_parts (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : CtxReduction n) (authBills privacyBills : CtxBills) (refusal : BillInput → ℝ≥0∞)
    (authLift : CtxAuthLiftBool setup codec route serverKid bounds n fallback auth authBills refusal)
    (privLift : CtxPrivLiftBool setup codec route serverKid bounds n privacy privacyBills) :
    CtxLiftBool setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal := by
  intro E X env startup allowance frame mode adversary budget respects decision cost costBound
  obtain ⟨authBound, authBilled⟩ := authLift env startup allowance frame mode adversary budget respects decision cost
    costBound
  cases mode with
  | O =>
      refine ⟨?_, authBilled, fun same => by cases same⟩
      calc _ ≤ _ := authBound
        _ = _ := by simp only [ctxLoss, reduceCtorEq, ite_false, add_zero]
  | P =>
      obtain ⟨privBound, privBilled⟩ := privLift env startup allowance frame .P adversary budget respects decision cost
        costBound
      refine ⟨?_, authBilled, fun _ => privBilled⟩
      have second := ProbComp.boolDistAdvantage_triangle
        (idealChains setup codec route env serverKid bounds .P adversary >>= fun result => decision (chainView result))
        (idealAuth setup codec route env serverKid bounds .P adversary >>= fun result => decision (ctxView result))
        (idealRecords setup codec route env serverKid bounds .P adversary >>= fun result => decision (ctxView result))
      calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal second
        _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ + _ := add_le_add authBound privBound
        _ = _ := by simp only [ctxLoss, ite_true]

/-- The event form of the integrity record lift follows from its Boolean form. -/
theorem recordAuthLiftStatement_of_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (chainBills : ChainBills) (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞)
    (bool : RecordAuthLiftBool setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills
      aliasing chainRefusal ctxRefusal) :
    RecordAuthLiftStatement setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal := by
  refine ⟨bool, ?_⟩
  intro correct E X env startup allowance frame mode adversary budget respects event
  obtain ⟨bound, billed⟩ := bool correct env startup allowance frame mode adversary budget respects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- The integrity record lift is the composition of the chain lift at the cache-free decision and the integrity half, by the triangle inequality with every term at coefficient one, in both modes and without any privacy reduction. -/
theorem recordAuthLiftBool_of_parts (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : ChainReduction n) (auth : CtxReduction n)
    (chainBills : ChainBills) (authBills : CtxBills) (aliasing chainRefusal ctxRefusal : BillInput → ℝ≥0∞)
    (chainLift : ChainLiftBool setup codec route serverKid bounds n hmac chain chainBills aliasing chainRefusal)
    (authLift : CtxAuthLiftBool setup codec route serverKid bounds n fallback auth authBills ctxRefusal) :
    RecordAuthLiftBool setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal := by
  intro correct E X env startup allowance frame mode adversary budget respects decision cost costBound
  obtain ⟨chainBound, chainBilled⟩ := chainLift correct env startup allowance frame mode adversary budget respects
    (fun view _ => decision view) cost (fun view _ => costBound view)
  obtain ⟨authBound, authBilled⟩ := authLift env startup allowance frame mode adversary budget respects decision cost
    costBound
  have first := ProbComp.boolDistAdvantage_triangle
    (realChains setup codec route env serverKid bounds mode adversary >>= fun result => decision (chainView result))
    (idealChains setup codec route env serverKid bounds mode adversary >>= fun result => decision (chainView result))
    (idealAuth setup codec route env serverKid bounds mode adversary >>= fun result => decision (ctxView result))
  refine ⟨?_, chainBilled, authBilled⟩
  calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal first
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add chainBound authBound

/-- The hiding target gives every decision on the hiding projection advantage zero between replaced and unreplaced hidden plaintexts. -/
theorem hiding_advantage (n : Nat) (target : HidingStatement setup codec route serverKid bounds n)
    (env : Environment n E) (adversary : OracleComp (ModeSpec .P) X) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ message, (replace message).length = message.length) (decision : HidingView n E X → ProbComp Bool) :
    (ctxRun (fun _ => .random) replace setup codec route env serverKid bounds .P adversary >>= fun result =>
        decision (hidingView (ctxView result))).boolDistAdvantage
      (idealRecords setup codec route env serverKid bounds .P adversary >>= fun result =>
        decision (hidingView (ctxView result))) = 0 := by
  have same := congrArg (fun work => work >>= decision) (target env adversary replace lengths)
  simp only [bind_map_left] at same
  rw [same]
  exact ProbComp.boolDistAdvantage_self _

/-- The hiding target in event form: every event of the hiding projection has the same probability with replaced and unreplaced hidden plaintexts. -/
theorem hiding_event (n : Nat) (target : HidingStatement setup codec route serverKid bounds n)
    (env : Environment n E) (adversary : OracleComp (ModeSpec .P) X) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ message, (replace message).length = message.length) (event : HidingView n E X → Bool) :
    𝒟[(fun result => event (hidingView (ctxView result))) <$>
        ctxRun (fun _ => .random) replace setup codec route env serverKid bounds .P adversary] {true} =
      𝒟[(fun result => event (hidingView (ctxView result))) <$>
        idealRecords setup codec route env serverKid bounds .P adversary] {true} := by
  have same := congrArg (fun work => event <$> work) (target env adversary replace lengths)
  simp only [Functor.map_map] at same
  rw [same]

end Relations

end BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.positions_derivations' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.positions_derivations

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.analysis_chainView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.analysis_chainView

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.realChains_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.realChains_analysis

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.chains_selected_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.chains_selected_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.realChains_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.realChains_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.idealRecords_O' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.idealRecords_O

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.idealRecords_P' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.idealRecords_P

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.keyImpl_modes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.keyImpl_modes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.randomImpl_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.randomImpl_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.materialAt_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.materialAt_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxInterpreter_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxInterpreter_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiddenOpening_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiddenOpening_malformed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiddenSealing_narrow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiddenSealing_narrow

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.guessTerm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.guessTerm_le

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.publicHiding_hidingView' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.publicHiding_hidingView

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.admittedTest_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.admittedTest_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.pure_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.pure_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.chainLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.chainLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxAuthLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxAuthLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxPrivLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxPrivLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordLiftBool_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordLiftBool_of_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxLiftBool_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.ctxLiftBool_of_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordAuthLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordAuthLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordAuthLiftBool_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.recordAuthLiftBool_of_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiding_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiding_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiding_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftIdeal.hiding_event
