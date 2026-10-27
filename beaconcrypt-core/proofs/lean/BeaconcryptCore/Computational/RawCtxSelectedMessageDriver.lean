import BeaconcryptCore.Computational.RawCtxSelectedMessageKdf
import BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization

/-!
The complete native receive and send drivers can use opaque selected material. Private derivations use the exact selected address with retained predecessor priority; an explicit prior-table service pays every fallback. Opening and sealing remain opaque callbacks over source pending state. Their mathematical source interpretation uses the original functional backend and complete shared state. No selected key is an argument of the executable compiled driver, and no callback-equivalence or final-event premise is assumed by its source equality.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageDriver
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxMaterialInterpretation RawCtxInterpretedOpening

noncomputable def privateTable (prior : Prior) (parent : Option Entry) (target : RootOutput) (output : FullOutput) : Prior :=
  match parent with
  | none => RawCtxSelectedParentPrivatePatch.privatePatch prior target output
  | some entry => lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry target

noncomputable def derive (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) : OracleComp PriorSpec (RatchetChain × Slot) :=
  match parent with
  | none => route target nonce next request
  | some entry => routeLater entry target nonce next request

/-- Every interpreted private derivation is the actual full native KDF response, with no excluded collision branch. -/
theorem derive_source (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (request : SymmetricRatchetKdfRequest) :
    (fun value : RatchetChain × Slot => (value.1, interpret key value.2)) <$> simulateQ (priorImpl prior) (derive parent target nonce next request) =
      pure (RawCtxInterpretedReceive.decodeResponse
        (RawCtxFunctionalFamily.execute (privateTable prior parent target (response key nonce next)) request)) := by
  cases parent with
  | none => simp only [derive, route_exact, map_pure, privateTable, step_exact]
  | some entry => simp only [derive, routeLater_exact, map_pure, privateTable, later_exact]

abbrev ReceiveServices (Context Plaintext : Type) :=
  PriorSpec + (Opening RatchetChain RatchetChain Slot Context →ₒ core.option.Option Plaintext)

abbrev SendServices (Context Output : Type) :=
  PriorSpec + (RawCtxInterpretedSend.Seal Slot Context →ₒ Option Output)

noncomputable def receiveCompiler {Context Plaintext : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Slot Context Plaintext) (OracleComp (ReceiveServices Context Plaintext))
  | .inl request => simulateQ (fun address => (ReceiveServices Context Plaintext).query (.inl address))
      (derive parent target nonce next request)
  | .inr pending => (ReceiveServices Context Plaintext).query (.inr pending)

noncomputable def sendCompiler {Context Output : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (RawCtxInterpretedSend.SendSpec Slot Context Output) (OracleComp (SendServices Context Output))
  | .inl request => simulateQ (fun address => (SendServices Context Output).query (.inl address))
      (derive parent target nonce next request)
  | .inr pending => (SendServices Context Output).query (.inr pending)

noncomputable def receive {Context Plaintext : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : Context) :=
  simulateQ (receiveCompiler (Plaintext := Plaintext) parent target nonce next)
    (RawCtxInterpretedReceive.receive kernel sequence context)

noncomputable def send {Context Output : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel) (context : Context) :=
  simulateQ (sendCompiler (Output := Output) parent target nonce next)
    (RawCtxInterpretedSend.send kernel context)

noncomputable def receiveServices {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl address => pure (prior address)
  | .inr pending => RawCtxFunctionalFamily.opening source writer
      (privateTable prior parent target (response key nonce next)) (toNative (mapOpening (interpret key) pending))

noncomputable def sendServices {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl address => pure (prior address)
  | .inr pending => RawCtxFunctionalFamily.sealing source writer
      (privateTable prior parent target (response key nonce next))
      (RawCtxInterpretedSend.nativeSeal (RawCtxInterpretedSend.mapSeal (interpret key) pending))

/-- Interpreting a prior lookup in any lawful monad gives exactly the retained private reply. -/
theorem derive_evaluated {m : Type → Type*} [Monad m] [LawfulMonad m]
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    simulateQ (fun address => (pure (prior address) : m FullOutput)) (derive parent target nonce next request) =
      pure (match parent with
        | none => step prior target nonce next request
        | some entry => later prior entry target nonce next request) := by
  cases parent <;> simp only [derive, routeLater, later, route, RawCtxSelectedMessageKdf.step]
  all_goals split
  all_goals try simp only [simulateQ_pure, simulateQ_map, simulateQ_spec_query, map_pure]
  split <;> simp only [simulateQ_pure, simulateQ_map, simulateQ_spec_query, map_pure]

/-- The compiled receive derivation is the actual private native response after interpretation; all shared state is retained. -/
theorem receive_derive {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    (fun value : RatchetChain × Slot => (value.1, interpret key value.2)) <$>
      ((receiveServices (A := A) source writer prior parent key target nonce next ∘ₛ
        receiveCompiler parent target nonce next) (.inl request)) =
      pure (RawCtxInterpretedReceive.decodeResponse
        (RawCtxFunctionalFamily.execute (privateTable prior parent target (response key nonce next)) request)) := by
  simp only [QueryImpl.compose, receiveCompiler, ← QueryImpl.simulateQ_compose]
  change (fun value : RatchetChain × Slot => (value.1, interpret key value.2)) <$>
    simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput))
      (derive parent target nonce next request) = _
  rw [derive_evaluated, map_pure]
  cases parent <;> simp only [privateTable, step_exact, later_exact]

/-- The entire selected-material receive is the actual native receive under the same private table and original stateful opening, including every rejected, cached and future path. -/
theorem receive_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key kernel) sequence context) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (receiveServices source writer prior parent key target nonce next)
          (receive parent target nonce next kernel sequence context) := by
  rw [← RawCtxFunctionalFamily.receive_handler, receive, ← QueryImpl.simulateQ_compose]
  apply RawCtxInterpretedReceive.receive_interpreted (interpret key)
  · intro request
    simp only [RawCtxMaterialPositions.bareReceiveImpl]
    exact (receive_derive source writer prior parent key target nonce next request).symm
  · intro pending
    exact (simulateQ_spec_query (receiveServices source writer prior parent key target nonce next) (.inr pending)).symm

/-- The send compiler pays the same explicit private lookup while retaining the source's exact decoded response. -/
theorem send_derive {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    (fun value : RatchetChain × Slot => (value.1, interpret key value.2)) <$>
      ((sendServices (A := A) source writer prior parent key target nonce next ∘ₛ
        sendCompiler parent target nonce next) (.inl request)) =
      pure (RawCtxInterpretedReceive.decodeResponse
        (RawCtxFunctionalFamily.execute (privateTable prior parent target (response key nonce next)) request)) := by
  simp only [QueryImpl.compose, sendCompiler, ← QueryImpl.simulateQ_compose]
  change (fun value : RatchetChain × Slot => (value.1, interpret key value.2)) <$>
    simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput))
      (derive parent target nonce next request) = _
  rw [derive_evaluated, map_pure]
  cases parent <;> simp only [privateTable, step_exact, later_exact]

/-- The complete source send, including failed sealing advancement, is the same opaque-material driver with the original sealing and writer effects. -/
theorem send_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send (RawCtxSelectedMessageReveals.nativeKernel key kernel) context) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (sendServices source writer prior parent key target nonce next)
          (send parent target nonce next kernel context) := by
  rw [← RawCtxFunctionalFamily.send_handler, send, ← QueryImpl.simulateQ_compose]
  apply RawCtxInterpretedSend.send_interpreted (interpret key)
  · intro request
    simp only [RawCtxMaterialPositions.bareSendImpl]
    exact (send_derive source writer prior parent key target nonce next request).symm
  · intro pending
    exact (simulateQ_spec_query (sendServices source writer prior parent key target nonce next) (.inr pending)).symm

/-- Native receive interpretation preserves the complete original shared primitive state as well as the published kernel and optional plaintext. -/
theorem receive_state {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key kernel) sequence context)).run state =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), result.2)) <$>
        (simulateQ (receiveServices source writer prior parent key target nonce next)
          (receive parent target nonce next kernel sequence context)).run state := by
  rw [receive_source, StateT.run_map]

/-- Native send interpretation retains writer failure, optional ciphertext and the entire original primitive state. -/
theorem send_state {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send (RawCtxSelectedMessageReveals.nativeKernel key kernel) context)).run state =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), result.2)) <$>
        (simulateQ (sendServices source writer prior parent key target nonce next)
          (send parent target nonce next kernel context)).run state := by
  rw [send_source, StateT.run_map]

/-- An arbitrary actual native receive starts in the all-known representation, preserving existing cached keys even if their bytes alias the target key. -/
theorem receive_known {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : ConcreteRatchetKernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive kernel sequence context) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (receiveServices source writer prior parent key target nonce next)
          (receive parent target nonce next (RawCtxSelectedMessageRevealInitialization.fromKernel kernel) sequence context) := by
  simpa only [RawCtxSelectedMessageRevealInitialization.kernel_roundtrip] using
    receive_source (A := A) source writer prior parent key target nonce next
      (RawCtxSelectedMessageRevealInitialization.fromKernel kernel) sequence context

/-- An arbitrary actual native send admits the same key-independent all-known initialization, retaining every original field. -/
theorem send_known {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send kernel context) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (sendServices source writer prior parent key target nonce next)
          (send parent target nonce next (RawCtxSelectedMessageRevealInitialization.fromKernel kernel) context) := by
  simpa only [RawCtxSelectedMessageRevealInitialization.kernel_roundtrip] using
    send_source (A := A) source writer prior parent key target nonce next
      (RawCtxSelectedMessageRevealInitialization.fromKernel kernel) context

end BeaconcryptCore.Computational.RawCtxSelectedMessageDriver

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.derive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.derive_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.derive_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.derive_evaluated
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_derive
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_derive
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_state
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_state
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.receive_known
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriver.send_known
