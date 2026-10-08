-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftSwap

/-!
# The flattened CTX world (items 4 and 5, world facts)

**Flattening.** `ctxRun_flat`: every CTX-mode world `PqxdhRecordLiftIdeal.ctxRun modes replace` is its startup (the environment's start under the compiled client and the CTX interpreter, `startup`), the installation of the constructed Server (`install`), and then one simulation of the observed adversary under `fullImpl`: the secrecy ledger over `nativeImpl`, which is the native dispatch over the compiled client over the CTX interpreter, flattened by `QueryImpl.mapStateTBase` and `QueryImpl.flattenStateT` onto the joint state of ledger, environment state, control state and private CTX state. `fullImpl_run` and `nativeImpl_run` unfold one query.

**Coins.** `nativeImpl_coin`: a native coin is one uniform query whose state update (one charged coin effect and one counted uniform query, `coinStep`) does not depend on the reply.

**Plaintext obliviousness.** `nativeImpl_send_zeros`: with the zeroing replacement `zeros` of hidden seal plaintexts (in any key modes), a native send of either of two plaintexts of equal length on a handle without a caller-known kernel (`KnownAt`) is the same computation on the native state. The source send admission never inspects its context (`beginSend_context`, `normalBegin_context`, `startContext_normalBegin`); the hidden sealing service reads a seal's context only through the replaced context, which zeroing makes depend on the plaintext's length only, and through the sequence, the material and the sender and target IDs (`hiddenSealing_zeros`, `ctxInterpreter_sealing_zeros`); hence the hidden send program (`sendProgram_zeros`), the owner send (`ownerSend_zeros`) and the Server and Beacon send steps (`serverStep_send_zeros`, `beaconStep_send_zeros`, through `native_serverSend_run` and `native_beaconSend_run`) agree; an absent Server, an absent peer and an absent or inactive owner make no query at all.

**Persistence.** `nativeImpl_known`: a caller-known kernel on a handle stays caller-known under every native command. Server installation needs a vacant peer key ID, Beacon installation an owner in `initSent`, no capability removes a peer or an established owner, and record operations keep the kernel's kind (`ownerRun_known`, `handler_peerKnown`, `handler_ownerKnown`, `handler_known`).

**Ledger.** `ledger_append`: every secrecy-ledger step appends exactly one transcript entry for its query. `ledger_inv`: the test session's first handle is the handle of the first admissible test of the transcript (`LedgerInv`, `firstTest_append`).

**Support.** `support_run_fst` and `support_keep_oracle` are generic facts on the reachable outputs of simulations.

**Contracts.** No theorem of this module has an assumption or contract hypothesis; contracts reached are listed per theorem in `doc/impl/record-lift-facts.md`. New Claude work.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftFlat
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-- The native state of the flattened world: the environment's own state, the record control and the CTX world's private state. -/
abbrev NativeState (n : Nat) (E : Type) := (E × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n

/-- Native commands over the compiled client, on the environment state and the control state together. -/
noncomputable def clientImpl (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT (E × PqxdhRecordLiftProtocol.Control n) (OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n))) :=
  ((PqxdhRecordLiftProtocol.handler codec.frameRead route).mapStateTBase (native env)).flattenStateT

/-- Native commands of the CTX world on its whole native state. -/
noncomputable def nativeImpl (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) : QueryImpl Spec (StateT (NativeState n E) ProbComp) :=
  ((ctxInterpreter modes replace setup codec).mapStateTBase (clientImpl env codec route)).flattenStateT

/-- Adversary queries of the CTX world (the secrecy ledger over the native commands) on the whole state. -/
noncomputable def fullImpl (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.Ledger × NativeState n E) ProbComp) :=
  ((nativeImpl modes replace setup codec route env).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds)).flattenStateT

/-- The startup of the CTX world: the environment's start under the compiled client and the CTX interpreter. -/
noncomputable def startup (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) (simulateQ coinLift env.start)).run
      PqxdhRecordLiftProtocol.initialControl)).run CtxPrivate.initial

/-- The installation of the constructed Server under the CTX interpreter. -/
noncomputable def install (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    ((PqxdhRecordLiftProtocol.handler (n := n) codec.frameRead route (.inl created)).run control)).run secret

/-- **Flattening.** The CTX world is its startup, the Server installation and then one simulation of the observed adversary under `fullImpl` from the empty ledger. -/
theorem ctxRun_flat (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    ctxRun modes replace setup codec route env serverKid bounds mode adversary =
      startup modes replace setup codec route env >>= fun born =>
        match born.1.1 with
        | none => pure ((none, born.1.2), born.2)
        | some (created, initial) =>
            install modes replace setup codec route created born.1.2 born.2 >>= fun installed =>
              (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
                  (result.1, result.2.1), result.2.2.1.1), result.2.2.1.2), result.2.2.2)) <$>
                (simulateQ (fullImpl modes replace setup codec route env serverKid bounds)
                  (asModeO mode adversary)).run
                  (PqxdhDeploymentSecrecy.Ledger.empty, ((initial, installed.1.2), installed.2)) := by
  unfold ctxRun PqxdhRecordLiftProtocol.program PqxdhRecordLiftProtocol.schedule PqxdhRecordLiftInterface.program
  simp only [simulateQ_bind, StateT.run_bind, startup]
  apply bind_congr
  rintro ⟨⟨born, control⟩, secret⟩
  rcases born with _ | ⟨created, initial⟩
  · simp only [simulateQ_pure, StateT.run_pure]
  · simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, install, fullImpl, nativeImpl, clientImpl]
    apply bind_congr
    intro installed
    rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      (native env), simulateQ_map, StateT.run_map,
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (ctxInterpreter modes replace setup codec),
      PqxdhDeploymentSecrecy.wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    rfl

/-- One adversary query of the flattened world: the secrecy ledger's program for the query, simulated by the native commands. -/
theorem fullImpl_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (state : NativeState n E) :
    (fullImpl modes replace setup codec route env serverKid bounds query).run (ledger, state) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (nativeImpl modes replace setup codec route env)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state :=
  rfl

/-- One native command of the CTX world: the native dispatch, the compiled client and the CTX interpreter. -/
theorem nativeImpl_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (state : NativeState n E) :
    (nativeImpl modes replace setup codec route env query).run state =
      (fun z => (z.1.1.1, ((z.1.1.2, z.1.2), z.2))) <$> (simulateQ (ctxInterpreter modes replace setup codec)
        ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) ((native env query).run state.1.1)).run
          state.1.2)).run state.2 := by
  simp only [nativeImpl, clientImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk, simulateQ_map,
    StateT.run_map, Functor.map_map]

/-- The private state after one counted native coin: one coin effect charged and one uniform query counted. -/
def coinStep (secret : CtxPrivate n) : CtxPrivate n :=
  { secret with base := { secret.base with primitive :=
    ({ secret.base.primitive.1 with
        effects := Function.update secret.base.primitive.1.effects .coin (secret.base.primitive.1.effects .coin + 1)
        uniform := secret.base.primitive.1.uniform + 1 }, secret.base.primitive.2) } }

/-- A native coin of the CTX world is one uniform query whose state update does not depend on the reply. -/
theorem nativeImpl_coin (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (coin : ℕ) (state : NativeState n E) :
    (nativeImpl modes replace setup codec route env (.inl coin)).run state =
      (fun reply => (reply, (state.1, coinStep state.2))) <$> (unifSpec.query coin : ProbComp _) := by
  rw [nativeImpl_run]
  simp only [native, coinLift, StateT.run, map_eq_bind_pure_comp]
  rfl

/-! ### Plaintext obliviousness of hidden sends with zeroed plaintexts -/

/-- The zeroing replacement: every hidden seal plaintext becomes zero bytes of its length. -/
def zeros (message : Pqxdh.Bytes) : Pqxdh.Bytes := List.replicate message.length 0

/-- Zeroing keeps the length. -/
theorem zeros_length (message : Pqxdh.Bytes) : (zeros message).length = message.length := List.length_replicate

/-- Replace the context of a send admission. -/
def setContext {Send Receive Material Context : Type} (context : Context) :
    RawCtxChainSend.Start Send Receive Material Context → RawCtxChainSend.Start Send Receive Material Context
  | .exhausted entry _ => .exhausted entry context
  | .requested pending => .requested { pending with context := context }

/-- The source send admission never inspects its context. -/
theorem beginSend_context {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (first second : Context) :
    RawCtxChainSend.beginSend kernel second = setContext second <$> RawCtxChainSend.beginSend kernel first := by
  simp only [RawCtxChainSend.beginSend, map_bind]
  congr 1
  funext advanced
  cases advanced.sequence
  all_goals simp only [map_bind, apply_ite, RawCtxMaterialInterpretation.rust_map_ok, setContext]

/-- The normalized source send admission with another context is the admission with its context replaced. -/
theorem normalBegin_context {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (first second : Context) :
    RawCtxChainSend.normalBegin kernel second = setContext second (RawCtxChainSend.normalBegin kernel first) := by
  have exact := beginSend_context kernel first second
  rw [RawCtxChainSend.normalBegin_exact, RawCtxChainSend.normalBegin_exact, RawCtxMaterialInterpretation.rust_map_ok]
    at exact
  exact RustM.ok.inj exact

/-- The selected seal input depends on its context, not on the proof of its width. -/
theorem selectedInput_congr (material : PqxdhFullSecretInputKdf.NonceOutput) (sequence : Std.U64) (first second : RawCtxSourceSend.SealContext)
    (firstWidth : first.associatedData.length = 153) (secondWidth : second.associatedData.length = 153)
    (same : first = second) :
    RawCtxSelectedMessageSealing.selectedInput material sequence first firstWidth =
      RawCtxSelectedMessageSealing.selectedInput material sequence second secondWidth := by
  subst same
  rfl

/-- With zeroed plaintexts, a hidden sealing reads its context only up to the plaintext's length. -/
theorem hiddenSealing_zeros (writer : RawCtxMixedShared.Writer) (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (pending : PqxdhRecordLiftProtocol.Sealing n) (plaintext : Pqxdh.Bytes)
    (length : plaintext.length = pending.context.plaintext.length) :
    hiddenSealing writer table zeros { pending with context :=
        ⟨plaintext, pending.context.targetId, pending.context.senderId, pending.context.associatedData⟩ } =
      hiddenSealing writer table zeros pending := by
  have same : replaceContext zeros
      ⟨plaintext, pending.context.targetId, pending.context.senderId, pending.context.associatedData⟩ =
        replaceContext zeros pending.context := by
    simp only [replaceContext, zeros, length]
  funext frames
  unfold hiddenSealing
  dsimp only
  apply dite_congr (by rw [same])
  · intro width
    rw [selectedInput_congr _ _ _ _ _ width same]
    congr 1
    funext reply
    cases reply <;> rfl
  · intro _
    rfl

/-- With zeroed plaintexts, the CTX world's sealing service reads a seal's context only up to the plaintext's length. -/
theorem ctxInterpreter_sealing_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Sealing n) (plaintext : Pqxdh.Bytes)
    (length : plaintext.length = pending.context.plaintext.length) :
    ctxInterpreter modes zeros setup codec
        (.sealing { pending with context :=
          ⟨plaintext, pending.context.targetId, pending.context.senderId, pending.context.associatedData⟩ }) =
      ctxInterpreter modes zeros setup codec (.sealing pending) := by
  funext state
  simp only [ctxInterpreter, hiddenSealing_zeros _ _ pending plaintext length]


/-- The context of a send admission. -/
def startContext {Send Receive Material Context : Type} :
    RawCtxChainSend.Start Send Receive Material Context → Context
  | .exhausted _ context => context
  | .requested pending => pending.context

/-- The normalized send admission keeps its context. -/
theorem startContext_normalBegin {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    startContext (RawCtxChainSend.normalBegin kernel context) = context := by
  rw [normalBegin_context kernel context context]
  cases RawCtxChainSend.normalBegin kernel context <;> rfl

/-- With zeroed plaintexts, the hidden send program reads its context only up to the plaintext's length. -/
theorem sendProgram_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (start : PqxdhRecordLiftChainCompiler.Start (Slot n) RawCtxSourceSend.SealContext) (plaintext : Pqxdh.Bytes)
    (length : plaintext.length = (startContext start).plaintext.length) :
    simulateQ (ctxInterpreter modes zeros setup codec) (simulateQ PqxdhRecordLiftProtocol.localLift
        (PqxdhRecordLiftOpaqueDrivers.sendProgram (Plaintext := RawCtxWholeOwner.Decrypted)
          (OpenContext := RawCtxWholeOwner.OpenContext) (Output := RawCtxSourceSend.Encrypted)
          (setContext ⟨plaintext, (startContext start).targetId, (startContext start).senderId,
            (startContext start).associatedData⟩ start))) =
      simulateQ (ctxInterpreter modes zeros setup codec) (simulateQ PqxdhRecordLiftProtocol.localLift
        (PqxdhRecordLiftOpaqueDrivers.sendProgram (Plaintext := RawCtxWholeOwner.Decrypted)
          (OpenContext := RawCtxWholeOwner.OpenContext) (Output := RawCtxSourceSend.Encrypted) start)) := by
  cases start with
  | exhausted entry context => rfl
  | requested pending =>
      simp only [setContext, startContext] at length ⊢
      simp only [PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, PqxdhRecordLiftProtocol.localLift, simulateQ_pure]
      have sealing : ctxInterpreter modes zeros setup codec (.sealing (RawCtxChainSend.ready
            { pending with context :=
              ⟨plaintext, pending.context.targetId, pending.context.senderId, pending.context.associatedData⟩ }
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))) =
          ctxInterpreter modes zeros setup codec (.sealing (RawCtxChainSend.ready pending
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))) :=
        ctxInterpreter_sealing_zeros modes setup codec
          (RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))
          plaintext length
      rw [sealing]
      rfl


/-- With zeroed plaintexts, a send on an owner with a hidden kernel reads the plaintext only through its length. -/
theorem ownerSend_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (sender : Std.U64) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (hidden : owner.kernel.origin.isSome) :
    simulateQ (ctxInterpreter modes zeros setup codec) (PqxdhRecordLiftProtocol.ownerSend sender first owner) =
      simulateQ (ctxInterpreter modes zeros setup codec) (PqxdhRecordLiftProtocol.ownerSend sender second owner) := by
  obtain ⟨stored, expected, associated, attempts⟩ := owner
  cases stored with
  | known kernel => simp [PqxdhRecordLiftWorldCompiler.StoredKernel.origin] at hidden
  | hidden slot kernel =>
      have empty : first.isEmpty = second.isEmpty := by
        cases first <;> cases second <;> simp at length ⊢
      unfold PqxdhRecordLiftProtocol.ownerSend
      rw [empty]
      split
      · rfl
      · simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend, simulateQ_bind]
        rw [normalBegin_context kernel (⟨first, expected, sender, associated⟩ : RawCtxSourceSend.SealContext)
          (⟨second, expected, sender, associated⟩ : RawCtxSourceSend.SealContext)]
        have same := sendProgram_zeros modes setup codec
          (RawCtxChainSend.normalBegin kernel (⟨first, expected, sender, associated⟩ : RawCtxSourceSend.SealContext))
          second
          (by rw [startContext_normalBegin]; exact length.symm)
        simp only [startContext_normalBegin] at same
        rw [same]


/-- A caller-known kernel is installed on the handle: a Server peer or an established Beacon owner whose stored kernel is caller-known. -/
def KnownAt (control : PqxdhRecordLiftProtocol.Control n) : Handle → Prop
  | .peer keyId => ∃ server peer kernel, control.server = some server ∧ server.peers keyId = some peer ∧
      peer.kernel = .known kernel
  | .owner owner => ∃ shell kernel, control.owners[owner]? = some (.established shell (.known kernel))

/-- With zeroed plaintexts, a Server send on a peer without a caller-known kernel reads the plaintext only through its length. -/
theorem serverStep_send_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder) (keyId : Std.U64)
    (first second : Pqxdh.Bytes) (length : first.length = second.length) (control : PqxdhRecordLiftProtocol.Control n)
    (notKnown : ¬KnownAt control (.peer keyId)) :
    simulateQ (ctxInterpreter modes zeros setup codec)
        ((PqxdhRecordLiftProtocol.serverStep decode route (.inl (first, keyId))).run control) =
      simulateQ (ctxInterpreter modes zeros setup codec)
        ((PqxdhRecordLiftProtocol.serverStep decode route (.inl (second, keyId))).run control) := by
  simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run]
  rcases hs : control.server with _ | server
  · simp only
  · rcases hp : server.peers keyId with _ | ⟨identity, stored⟩
    · simp only [hp]
    · cases stored with
      | known kernel => exact absurd ⟨server, _, kernel, hs, hp, rfl⟩ notKnown
      | hidden slot kernel =>
          simp only [hp, PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
            PqxdhDeploymentNative.serverTag, simulateQ_bind]
          rw [ownerSend_zeros modes setup codec _ first second length _ rfl]
          rfl

/-- With zeroed plaintexts, a Beacon send on an owner without a caller-known kernel reads the plaintext only through its length. -/
theorem beaconStep_send_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (owner : Nat) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (control : PqxdhRecordLiftProtocol.Control n) (notKnown : ¬KnownAt control (.owner owner)) :
    simulateQ (ctxInterpreter modes zeros setup codec)
        ((PqxdhRecordLiftProtocol.beaconStep decode owner (.inl first)).run control) =
      simulateQ (ctxInterpreter modes zeros setup codec)
        ((PqxdhRecordLiftProtocol.beaconStep decode owner (.inl second)).run control) := by
  simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run]
  rcases ho : control.owners[owner]? with _ | (phase | ⟨shell, stored⟩)
  · simp only [PqxdhDeploymentNative.absent]
  · simp only
  · cases stored with
    | known kernel => exact absurd ⟨shell, kernel, ho⟩ notKnown
    | hidden slot kernel =>
        simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep, simulateQ_bind]
        rw [ownerSend_zeros modes setup codec _ first second length _ rfl]
        rfl


/-- A native Server send is the compiled client's Server send step, with the environment state kept. -/
theorem native_serverSend_run (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (keyId : Std.U64) (m : Pqxdh.Bytes) (e : E) (control : PqxdhRecordLiftProtocol.Control n) :
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((native env (.inr (.serverSend keyId m))).run e)).run control =
      (fun p => ((p.1, e), p.2)) <$> (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (m, keyId))).run control := by
  simp only [native, StateT.lift, StateT.run]
  erw [simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_pure, PqxdhRecordLiftProtocol.handler, map_eq_bind_pure_comp]
  rfl

/-- A native Beacon send is the compiled client's Beacon send step, with the environment state kept. -/
theorem native_beaconSend_run (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat) (m : Pqxdh.Bytes) (e : E)
    (control : PqxdhRecordLiftProtocol.Control n) :
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((native env (.inr (.beaconSend owner m))).run e)).run control =
      (fun p => ((p.1, e), p.2)) <$> (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl m)).run control := by
  simp only [native, StateT.lift, StateT.run]
  erw [simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_pure, PqxdhRecordLiftProtocol.handler, map_eq_bind_pure_comp]
  rfl

/-- **Plaintext obliviousness.** With zeroed hidden plaintexts, a native send on a handle without a caller-known kernel, of either of two plaintexts of equal length, is the same computation on the native state. -/
theorem nativeImpl_send_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (handle : Handle) (first second : Pqxdh.Bytes)
    (length : first.length = second.length) (state : NativeState n E) (notKnown : ¬KnownAt state.1.2 handle) :
    (simulateQ (nativeImpl modes zeros setup codec route env) (PqxdhDeploymentSecrecy.send handle first)).run state =
      (simulateQ (nativeImpl modes zeros setup codec route env) (PqxdhDeploymentSecrecy.send handle second)).run state := by
  cases handle with
  | peer keyId =>
      simp only [PqxdhDeploymentSecrecy.send, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rw [nativeImpl_run, nativeImpl_run, native_serverSend_run, native_serverSend_run, simulateQ_map, simulateQ_map,
        serverStep_send_zeros modes setup codec codec.frameRead route keyId first second length state.1.2 notKnown]
      rfl
  | owner owner =>
      simp only [PqxdhDeploymentSecrecy.send, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rw [nativeImpl_run, nativeImpl_run, native_beaconSend_run, native_beaconSend_run, simulateQ_map, simulateQ_map,
        beaconStep_send_zeros modes setup codec codec.frameRead owner first second length state.1.2 notKnown]
      rfl


/-! ### Support invariants -/

section Support
variable {κ κ' : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}

/-- The value of a simulated run is a reachable value of the simulated program. -/
theorem support_run_fst {σ α : Type} (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (oa : OracleComp spec α)
    (s : σ) : ∀ p ∈ support ((simulateQ impl oa).run s), p.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      intro p hp
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp
  | query_bind q k ih =>
      intro p hp
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind] at hp
      obtain ⟨mid, _, hp⟩ := (MonadAttach.mem_support_bind).mp hp
      exact (MonadAttach.mem_support_bind).mpr ⟨mid.1, by simp, ih mid.1 mid.2 p hp⟩

/-- A state predicate that every query keeps is kept by every simulated program. -/
theorem support_keep_oracle {σ α : Type} (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (B : σ → Prop)
    (keep : ∀ q s, B s → ∀ p ∈ support ((impl q).run s), B p.2) (oa : OracleComp spec α) (s : σ) (hs : B s) :
    ∀ p ∈ support ((simulateQ impl oa).run s), B p.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      intro p hp
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hs
  | query_bind q k ih =>
      intro p hp
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind] at hp
      obtain ⟨mid, hmid, hp⟩ := (MonadAttach.mem_support_bind).mp hp
      exact ih mid.1 mid.2 (keep q s hs mid hmid) p hp

end Support


/-! ### Caller-known kernels persist -/

/-- A stored kernel is caller-known. -/
def StoredKnown : PqxdhRecordLiftWorldCompiler.StoredKernel n → Prop
  | .known _ => True
  | .hidden _ _ => False

/-- An owner record operation on a caller-known kernel leaves a caller-known kernel. -/
theorem ownerRun_known (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (known : StoredKnown owner.kernel) :
    ∀ p ∈ support (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner), StoredKnown p.2.kernel := by
  obtain ⟨stored, expected, associated, attempts⟩ := owner
  cases stored with
  | hidden slot kernel => exact absurd known id
  | known kernel =>
      intro p hp
      simp only [PqxdhRecordLiftProtocol.ownerRun, mem_support_bind_iff, mem_support_pure_iff] at hp
      obtain ⟨result, hresult, _, _, rfl⟩ := hp
      rcases query with plaintext | raw
      · simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend] at hresult
        split at hresult
        · simp only [mem_support_pure_iff] at hresult
          subst hresult
          trivial
        · simp only [PqxdhRecordLiftProtocol.kernelSend, mem_support_bind_iff, mem_support_pure_iff] at hresult
          obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hresult
          trivial
      · simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive] at hresult
        split at hresult
        · simp only [mem_support_pure_iff] at hresult
          subst hresult
          trivial
        · split at hresult
          · simp only [mem_support_pure_iff] at hresult
            subst hresult
            trivial
          · split at hresult
            · simp only [PqxdhRecordLiftProtocol.kernelReceive, mem_support_bind_iff, mem_support_pure_iff] at hresult
              obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hresult
              trivial
            · simp only [mem_support_pure_iff] at hresult
              subst hresult
              trivial


/-- The Server record has a caller-known kernel on the peer key ID. -/
def PeerKnown (server : Option (PqxdhRecordLiftWorldCompiler.Server n)) (keyId : Std.U64) : Prop :=
  ∃ srv peer, server = some srv ∧ srv.peers keyId = some peer ∧ StoredKnown peer.kernel

/-- The owner list has an established Beacon with a caller-known kernel at the index. -/
def OwnerKnown (owners : List (PqxdhRecordLiftWorldCompiler.Phase n)) (owner : Nat) : Prop :=
  ∃ shell stored, owners[owner]? = some (.established shell stored) ∧ StoredKnown stored

/-- A caller-known kernel on a handle, read separately from the Server record and from the owner list. -/
theorem knownAt_iff (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) :
    KnownAt control handle ↔ match handle with
      | .peer keyId => PeerKnown control.server keyId
      | .owner owner => OwnerKnown control.owners owner := by
  cases handle with
  | peer keyId =>
      constructor
      · rintro ⟨server, peer, kernel, hs, hp, hk⟩
        exact ⟨server, peer, hs, hp, by rw [hk]; trivial⟩
      · rintro ⟨server, ⟨identity, stored⟩, hs, hp, hk⟩
        cases stored with
        | known kernel => exact ⟨server, _, kernel, hs, hp, rfl⟩
        | hidden slot kernel => exact absurd hk id
  | owner owner =>
      constructor
      · rintro ⟨shell, kernel, ho⟩
        exact ⟨shell, _, ho, trivial⟩
      · rintro ⟨shell, stored, ho, hk⟩
        cases stored with
        | known kernel => exact ⟨shell, kernel, ho⟩
        | hidden slot kernel => exact absurd hk id


/-- Marking a slot as used leaves the Server record unchanged. -/
theorem markUsed_server (control : PqxdhRecordLiftProtocol.Control n) (role : Role) (ref : KernelRef n) :
    (PqxdhRecordLiftProtocol.markUsed control role ref).server = control.server := by
  cases ref <;> rfl

/-- Marking a slot as used leaves the owner list unchanged. -/
theorem markUsed_owners (control : PqxdhRecordLiftProtocol.Control n) (role : Role) (ref : KernelRef n) :
    (PqxdhRecordLiftProtocol.markUsed control role ref).owners = control.owners := by
  cases ref <;> rfl

/-- Every compiled-client step keeps a caller-known Server peer kernel. -/
theorem handler_peerKnown (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (keyId : Std.U64)
    (known : PeerKnown control.server keyId) :
    ∀ p ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control), PeerKnown p.2.server keyId := by
  obtain ⟨server, peer, hs, hp, hk⟩ := known
  have keep : PeerKnown control.server keyId := ⟨server, peer, hs, hp, hk⟩
  intro p hmem
  rcases query with created | effect | (send | raw) | ⟨owner, send | raw⟩
  · simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.initializeServer, StateT.run, hs] at hmem
    obtain rfl := (mem_support_pure_iff _ _).mp hmem
    exact keep
  · simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift]
      at hmem
    obtain ⟨mid, hmid, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
    obtain ⟨_, _, hmid⟩ := (mem_support_bind_iff _ _ _).mp hmid
    obtain rfl := (mem_support_pure_iff _ _).mp hmid
    rcases effect with coin | request
    · simp only [StateT.run_lift] at hmem
      obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · cases request with
      | peerPresent k =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
      | ownerPresent o =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
      | appendOwner sender identity phase =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
      | advanceOwner o phase =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          split at hmem
          · split at hmem
            all_goals
              obtain rfl := (mem_support_pure_iff _ _).mp hmem
              exact keep
          · obtain rfl := (mem_support_pure_iff _ _).mp hmem
            exact keep
      | installServer k identity ref =>
          simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installServer, StateT.run, hs] at hmem
          split at hmem
          · rename_i vacant
            obtain ⟨stored, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
            obtain rfl := (mem_support_pure_iff _ _).mp hmem
            have other : keyId ≠ k := fun same => by
              subst same
              rw [hp] at vacant
              exact absurd vacant.1 (Option.some_ne_none peer)
            exact ⟨_, peer, rfl, by simp only [Function.update_of_ne other, hp], hk⟩
          · obtain rfl := (mem_support_pure_iff _ _).mp hmem
            exact keep
      | installBeacon o shell ref =>
          simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installBeacon, StateT.run] at hmem
          split at hmem
          · obtain ⟨stored, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
            obtain rfl := (mem_support_pure_iff _ _).mp hmem
            simp only [markUsed_server]
            exact keep
          · obtain rfl := (mem_support_pure_iff _ _).mp hmem
            exact keep
      | hash bytes =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run_lift] at hmem
          obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
  · obtain ⟨message, k⟩ := send
    simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.serverStep, StateT.run, hs] at hmem
    rcases hpk : server.peers k with _ | other
    · simp only [hpk] at hmem
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · simp only [hpk] at hmem
      obtain ⟨result, hresult, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      by_cases same : keyId = k
      · subst same
        rw [hp] at hpk
        cases hpk
        exact ⟨_, _, rfl, Function.update_self _ _ _, ownerRun_known _ _ _ _ _ hk result hresult⟩
      · exact ⟨_, peer, rfl, by simp only [Function.update_of_ne same, hp], hk⟩
  · simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.serverStep, StateT.run, hs] at hmem
    split at hmem
    · obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact ⟨_, peer, rfl, hp, hk⟩
    · rename_i k _
      rcases hpk : server.peers k with _ | other
      · simp only [hpk] at hmem
        obtain rfl := (mem_support_pure_iff _ _).mp hmem
        exact ⟨_, peer, rfl, hp, hk⟩
      · simp only [hpk] at hmem
        obtain ⟨result, hresult, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
        obtain rfl := (mem_support_pure_iff _ _).mp hmem
        by_cases same : keyId = k
        · subst same
          rw [hp] at hpk
          cases hpk
          exact ⟨_, _, rfl, Function.update_self _ _ _, ownerRun_known _ _ _ _ _ hk result hresult⟩
        · exact ⟨_, peer, rfl, by simp only [Function.update_of_ne same, hp], hk⟩
  all_goals
    simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.beaconStep, StateT.run] at hmem
    split at hmem
    · obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · obtain ⟨result, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep


/-- Every compiled-client step keeps a caller-known established Beacon owner kernel. -/
theorem handler_ownerKnown (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat)
    (known : OwnerKnown control.owners owner) :
    ∀ p ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control), OwnerKnown p.2.owners owner := by
  obtain ⟨shell, stored, ho, hk⟩ := known
  have keep : OwnerKnown control.owners owner := ⟨shell, stored, ho, hk⟩
  have bound : owner < control.owners.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at ho
    simp at ho
  intro p hmem
  rcases query with created | effect | (send | raw) | ⟨index, send | raw⟩
  · simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.initializeServer, StateT.run] at hmem
    split at hmem
    all_goals
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
  · simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift]
      at hmem
    obtain ⟨mid, hmid, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
    obtain ⟨_, _, hmid⟩ := (mem_support_bind_iff _ _ _).mp hmid
    obtain rfl := (mem_support_pure_iff _ _).mp hmid
    rcases effect with coin | request
    · simp only [StateT.run_lift] at hmem
      obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · cases request with
      | peerPresent k =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
      | ownerPresent o =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
      | appendOwner sender identity phase =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact ⟨shell, stored, by rw [List.getElem?_append_left bound, ho], hk⟩
      | advanceOwner o phase =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at hmem
          split at hmem
          · rename_i before hbefore
            split at hmem
            · obtain rfl := (mem_support_pure_iff _ _).mp hmem
              have other : o ≠ owner := fun same => by
                subst same
                rw [ho] at hbefore
                simp at hbefore
              exact ⟨shell, stored, by rw [List.getElem?_set_ne other, ho], hk⟩
            · obtain rfl := (mem_support_pure_iff _ _).mp hmem
              exact keep
          · obtain rfl := (mem_support_pure_iff _ _).mp hmem
            exact keep
      | installServer k identity ref =>
          simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installServer, StateT.run] at hmem
          split at hmem
          · obtain rfl := (mem_support_pure_iff _ _).mp hmem
            exact keep
          · split at hmem
            · obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
              obtain rfl := (mem_support_pure_iff _ _).mp hmem
              simp only [markUsed_owners]
              exact keep
            · obtain rfl := (mem_support_pure_iff _ _).mp hmem
              exact keep
      | installBeacon o shell' ref =>
          simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installBeacon, StateT.run] at hmem
          split at hmem
          · rename_i ready
            obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
            obtain rfl := (mem_support_pure_iff _ _).mp hmem
            have other : o ≠ owner := fun same => by
              subst same
              have hready := ready.1
              rw [PqxdhRecordLiftProtocol.BeaconReady, ho] at hready
              simp at hready
            exact ⟨shell, stored, by rw [List.getElem?_set_ne other, ho], hk⟩
          · obtain rfl := (mem_support_pure_iff _ _).mp hmem
            exact keep
      | hash bytes =>
          simp only [PqxdhRecordLiftProtocol.capability, StateT.run_lift] at hmem
          obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
          obtain rfl := (mem_support_pure_iff _ _).mp hmem
          exact keep
  all_goals try
    simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.serverStep, StateT.run] at hmem
    repeat' split at hmem
    all_goals first
      | obtain rfl := (mem_support_pure_iff _ _).mp hmem
        exact keep
      | obtain ⟨_, _, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
        obtain rfl := (mem_support_pure_iff _ _).mp hmem
        exact keep
  all_goals
    simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.beaconStep, StateT.run] at hmem
    split at hmem
    · obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · obtain rfl := (mem_support_pure_iff _ _).mp hmem
      exact keep
    · rename_i shell' kernel' hindex
      obtain ⟨result, hresult, hmem⟩ := (mem_support_bind_iff _ _ _).mp hmem
      obtain rfl := (mem_support_pure_iff _ _).mp hmem
      by_cases same : index = owner
      · subst same
        rw [ho] at hindex
        cases hindex
        refine ⟨shell, _, List.getElem?_set_self bound, ownerRun_known _ _ _ _ _ hk result hresult⟩
      · exact ⟨shell, stored, by rw [List.getElem?_set_ne same, ho], hk⟩


/-- Every compiled-client step keeps every caller-known kernel. -/
theorem handler_known (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (handle : Handle) (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (known : KnownAt control handle) :
    ∀ p ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control), KnownAt p.2 handle := by
  intro p hp
  rw [knownAt_iff] at known ⊢
  cases handle with
  | peer keyId => exact handler_peerKnown decode route query control keyId known p hp
  | owner owner => exact handler_ownerKnown decode route query control owner known p hp

/-- **Persistence.** Every native command of the CTX world keeps every caller-known kernel. -/
theorem nativeImpl_known (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (handle : Handle) (query : Spec.Domain) (state : NativeState n E)
    (known : KnownAt state.1.2 handle) :
    ∀ p ∈ support ((nativeImpl modes replace setup codec route env query).run state), KnownAt p.2.1.2 handle := by
  intro p hp
  rw [nativeImpl_run, support_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  exact support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route) (fun control => KnownAt control handle)
    (handler_known codec.frameRead route handle) _ state.1.2 known z.1 (support_run_fst _ _ _ z hz)


/-! ### The secrecy ledger -/

/-- Every secrecy-ledger step appends exactly one entry for its query to the transcript. -/
theorem ledger_append (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : PqxdhDeploymentSecrecy.Ledger) :
    ∀ p ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger),
      ∃ reply, p.2.transcript = ledger.transcript ++ [⟨query, reply⟩] := by
  intro p hp
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at hp
    obtain ⟨reply, _, rfl⟩ := hp
    exact ⟨reply, rfl⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    repeat' split at hp
    all_goals first
      | obtain rfl := (mem_support_pure_iff _ _).mp hp
        exact ⟨_, rfl⟩
      | obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        first
          | obtain rfl := (mem_support_pure_iff _ _).mp hp
            exact ⟨_, rfl⟩
          | obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
            obtain rfl := (mem_support_pure_iff _ _).mp hp
            exact ⟨_, rfl⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    split at hp
    · obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain rfl := (mem_support_pure_iff _ _).mp hp
      exact ⟨_, rfl⟩
    · obtain rfl := (mem_support_pure_iff _ _).mp hp
      exact ⟨_, rfl⟩


/-- The ledger's test session starts at the first admissible test of its transcript. -/
def LedgerInv (ledger : PqxdhDeploymentSecrecy.Ledger) : Prop :=
  ledger.test.map PqxdhDeploymentSecrecy.TestState.first = firstTest ledger.transcript

/-- The empty ledger satisfies the invariant. -/
theorem ledgerInv_empty : LedgerInv PqxdhDeploymentSecrecy.Ledger.empty := rfl

/-- The first admissible test of an extended transcript. -/
theorem firstTest_append (transcript : List PqxdhDeploymentInterface.Entry) (entry : PqxdhDeploymentInterface.Entry) :
    firstTest (transcript ++ [entry]) = (firstTest transcript).or (admissibleTest entry) := by
  simp only [firstTest, List.findSome?_append, List.findSome?_singleton]

/-- A forwarded coin or command is never an admissible test. -/
theorem admissibleTest_forward (query : Spec.Domain) (reply : FullSpec.Range (.inl query)) :
    admissibleTest ⟨.inl query, reply⟩ = none := rfl

/-- A fresh-message command is never an admissible test. -/
theorem admissibleTest_fresh (handle : Handle) (length : Nat) (reply : FullSpec.Range (.inr (.fresh handle length))) :
    admissibleTest ⟨.inr (.fresh handle length), reply⟩ = none := rfl

open Classical in
/-- A test command is an admissible test exactly when its messages are admissible. -/
theorem admissibleTest_test (handle : Handle) (left right : Pqxdh.Bytes)
    (reply : FullSpec.Range (.inr (.test handle left right))) :
    admissibleTest ⟨.inr (.test handle left right), reply⟩ =
      if PqxdhDeploymentSecrecy.Admissible left right then some handle else none := rfl

/-- Every secrecy-ledger step keeps the test session at the first admissible test of the transcript. -/
theorem ledger_inv (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (inv : LedgerInv ledger) :
    ∀ p ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger),
      LedgerInv p.2 := by
  intro p hp
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at hp
    obtain ⟨reply, _, rfl⟩ := hp
    simp only [LedgerInv, PqxdhDeploymentSecrecy.Ledger.record, firstTest_append, admissibleTest_forward,
      Option.or_none]
    exact inv
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
    · simp only [admissible, ↓reduceIte] at hp
      cases hsession : ledger.test with
      | none =>
          simp only [hsession] at hp
          obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
          obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
          obtain rfl := (mem_support_pure_iff _ _).mp hp
          have none : firstTest ledger.transcript = none := by
            unfold LedgerInv at inv
            rw [← inv, hsession]
            rfl
          unfold LedgerInv
          dsimp only [PqxdhDeploymentSecrecy.Ledger.record]
          rw [firstTest_append, admissibleTest_test, ite_eq_left admissible, none]
          rfl
      | some session =>
          have first : firstTest ledger.transcript = some session.first := by
            unfold LedgerInv at inv
            rw [← inv, hsession]
            rfl
          simp only [hsession] at hp
          split at hp
          · obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
            obtain rfl := (mem_support_pure_iff _ _).mp hp
            simp only [LedgerInv, PqxdhDeploymentSecrecy.Ledger.record, firstTest_append, first, Option.some_or,
              Option.map_some]
          · obtain rfl := (mem_support_pure_iff _ _).mp hp
            simp only [LedgerInv, PqxdhDeploymentSecrecy.Ledger.record, firstTest_append, first, Option.some_or,
              hsession, Option.map_some]
    · simp only [admissible, ↓reduceIte] at hp
      obtain rfl := (mem_support_pure_iff _ _).mp hp
      unfold LedgerInv at inv ⊢
      dsimp only [PqxdhDeploymentSecrecy.Ledger.record]
      rw [firstTest_append, admissibleTest_test, ite_eq_right admissible, Option.or_none]
      exact inv
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at hp
    split at hp
    · obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain ⟨_, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
      obtain rfl := (mem_support_pure_iff _ _).mp hp
      simp only [LedgerInv, PqxdhDeploymentSecrecy.Ledger.record, firstTest_append, admissibleTest_fresh,
        Option.or_none]
      exact inv
    · obtain rfl := (mem_support_pure_iff _ _).mp hp
      simp only [LedgerInv, PqxdhDeploymentSecrecy.Ledger.record, firstTest_append, admissibleTest_fresh,
        Option.or_none]
      exact inv

end BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ctxRun_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ctxRun_flat

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.fullImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.fullImpl_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.zeros_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.zeros_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.beginSend_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.beginSend_context

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.normalBegin_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.normalBegin_context

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.selectedInput_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.selectedInput_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.hiddenSealing_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.hiddenSealing_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ctxInterpreter_sealing_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ctxInterpreter_sealing_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.startContext_normalBegin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.startContext_normalBegin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.sendProgram_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.sendProgram_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ownerSend_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ownerSend_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.serverStep_send_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.serverStep_send_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.beaconStep_send_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.beaconStep_send_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.native_serverSend_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.native_serverSend_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.native_beaconSend_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.native_beaconSend_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_send_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_send_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.support_run_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.support_run_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.support_keep_oracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.support_keep_oracle

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ownerRun_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ownerRun_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.knownAt_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.knownAt_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.markUsed_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.markUsed_server

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.markUsed_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.markUsed_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.handler_peerKnown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.handler_peerKnown

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.handler_ownerKnown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.handler_ownerKnown

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.handler_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.handler_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.nativeImpl_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ledger_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ledger_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ledgerInv_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ledgerInv_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.firstTest_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.firstTest_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.admissibleTest_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.admissibleTest_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.admissibleTest_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.admissibleTest_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.admissibleTest_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.admissibleTest_test

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ledger_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.ledger_inv
