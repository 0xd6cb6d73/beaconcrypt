import BeaconcryptCore.Computational.RawCtxSelectedSendTrace
import BeaconcryptCore.Computational.RawCtxOwnerLabels

/-!
The actual opaque-material driver emits a private event for every completed KDF request and before every send callback. Each event carries the original outer owner and old kernel; the full request and next-chain/material response are retained, including parent retries and selected-address hits that require no prior-table lookup. A seal is recorded before its challenger reply, so an interpreter can retain a refused attempt. These events are private instrumentation, not network output or a nonce uniqueness assumption.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedDriverAudit
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey
open RawCtxSelectedMessageDriver RawCtxSelectedParentTable RawCtxSelectedParentEntry

inductive Event (Owner : Type) where
  | derived (owner : Owner) (sending : Bool) (entry : RawCtxSelectedMessageReveals.Kernel)
      (request : SymmetricRatchetKdfRequest) (response : RatchetChain × Slot)
  | sealing (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)

abbrev Audit (Owner : Type) := Event Owner →ₒ Unit
abbrev SendSpec (Owner : Type) := SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted + Audit Owner

def erase {Owner ι : Type} {original : OracleSpec ι} : QueryImpl (original + Audit Owner) (OracleComp original)
  | .inl query => original.query query
  | .inr _ => pure ()

noncomputable def sendCompiler {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (RawCtxInterpretedSend.SendSpec Slot RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (OracleComp (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted + Audit Owner))
  | .inl request => do
    let reply ← simulateQ (fun address => (SendSpec Owner).query (.inl (.inl address))) (derive parent target nonce next request)
    let _ ← (SendSpec Owner).query (.inr (.derived owner true entry request reply))
    pure reply
  | .inr pending => do
    let _ ← (SendSpec Owner).query (.inr (.sealing ⟨owner, entry, pending⟩))
    (SendSpec Owner).query (.inl (.inr pending))

set_option backward.isDefEq.respectTransparency false in
/-- Erasing the actual send audit returns the original private KDF/selected sealing compiler on every query. -/
theorem send_query {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (query : (RawCtxInterpretedSend.SendSpec Slot RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).Domain) :
    simulateQ erase (sendCompiler owner entry parent target nonce next query) =
      RawCtxSelectedMessageDriver.sendCompiler parent target nonce next query := by
  cases query with
  | inl request =>
    simp only [sendCompiler, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, erase, pure_bind]
    simp only [bind_pure]
    rw [← QueryImpl.simulateQ_compose]
    unfold RawCtxSelectedMessageDriver.sendCompiler
    congr 1
  | inr pending => simp [sendCompiler, erase, RawCtxSelectedMessageDriver.sendCompiler]

noncomputable def send {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (context : RawCtxSourceSend.SealContext) :=
  simulateQ (sendCompiler owner entry parent target nonce next) (RawCtxInterpretedSend.send entry context)

/-- The complete audited send erases to the literal original opaque driver, with full kernel and optional ciphertext unchanged. -/
theorem send_erased {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (context : RawCtxSourceSend.SealContext) :
    simulateQ erase (send owner entry parent target nonce next context) =
      RawCtxSelectedMessageDriver.send parent target nonce next entry context := by
  simp only [send, ← QueryImpl.simulateQ_compose]
  have same : erase ∘ₛ sendCompiler owner entry parent target nonce next =
      RawCtxSelectedMessageDriver.sendCompiler parent target nonce next := by
    funext query
    exact send_query owner entry parent target nonce next query
  rw [same]
  rfl

abbrev ReceiveSpec (Owner : Type) := ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted + Audit Owner

noncomputable def receiveCompiler {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Slot RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (OracleComp (ReceiveSpec Owner))
  | .inl request => do
    let reply ← simulateQ (fun address => (ReceiveSpec Owner).query (.inl (.inl address))) (derive parent target nonce next request)
    let _ ← (ReceiveSpec Owner).query (.inr (.derived owner false entry request reply))
    pure reply
  | .inr pending => (ReceiveSpec Owner).query (.inl (.inr pending))

set_option backward.isDefEq.respectTransparency false in
/-- Every receive KDF audit erases to the original derived response; cached and future openings preserve their original callback verbatim. -/
theorem receive_query {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (query : (RawCtxInterpretedReceive.ReceiveSpec Slot RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain) :
    simulateQ erase (receiveCompiler owner entry parent target nonce next query) =
      RawCtxSelectedMessageDriver.receiveCompiler parent target nonce next query := by
  cases query with
  | inl request =>
    simp only [receiveCompiler, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, erase, pure_bind]
    simp only [bind_pure]
    rw [← QueryImpl.simulateQ_compose]
    unfold RawCtxSelectedMessageDriver.receiveCompiler
    congr 1
  | inr pending => rfl

noncomputable def receive {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :=
  simulateQ (receiveCompiler owner entry parent target nonce next) (RawCtxInterpretedReceive.receive entry sequence context)

/-- The complete audited receive erases to the original driver, preserving cached/future paths, rollback and the actual optional plaintext. -/
theorem receive_erased {Owner : Type} (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ erase (receive owner entry parent target nonce next sequence context) =
      RawCtxSelectedMessageDriver.receive parent target nonce next entry sequence context := by
  simp only [receive, ← QueryImpl.simulateQ_compose]
  have same : erase ∘ₛ receiveCompiler owner entry parent target nonce next =
      RawCtxSelectedMessageDriver.receiveCompiler parent target nonce next := by
    funext query
    exact receive_query owner entry parent target nonce next query
  rw [same]
  rfl

/-- The actual native send consumes this audited driver under the literal original source interpreter, with no final callback-equivalence premise. -/
theorem send_source {Owner A : Type} (owner : Owner)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send (RawCtxSelectedMessageReveals.nativeKernel key entry) context) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (sendServices source writer prior parent key target nonce next ∘ₛ erase)
          (send owner entry parent target nonce next context) := by
  rw [QueryImpl.simulateQ_compose (sendServices source writer prior parent key target nonce next) erase, send_erased]
  exact RawCtxSelectedMessageDriver.send_source source writer prior parent key target nonce next entry context

/-- The complete native cached/future receive consumes the audited driver and retains the original source optional plaintext and shared primitive state. -/
theorem receive_source {Owner A : Type} (owner : Owner)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (entry : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key entry) sequence context) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (receiveServices source writer prior parent key target nonce next ∘ₛ erase)
          (receive owner entry parent target nonce next sequence context) := by
  rw [QueryImpl.simulateQ_compose (receiveServices source writer prior parent key target nonce next) erase, receive_erased]
  exact RawCtxSelectedMessageDriver.receive_source source writer prior parent key target nonce next entry sequence context

def observed {Owner State ι : Type} {base : OracleSpec ι} {m : Type → Type*} [Monad m]
    (original : QueryImpl base (OptionT (StateT State m))) :
    QueryImpl (base + Audit Owner) (OptionT (StateT (List (Event Owner) × State) m)) :=
  fun query => OptionT.mk fun state => match query with
  | .inl request => (fun reply => (reply.1, (state.1, reply.2))) <$> ((original request).run).run state.2
  | .inr event => pure (some (), (state.1 ++ [event], state.2))

/-- The audit interpreter keeps state outside optional stopping and erases every source query to its full original optional reply and primitive state. -/
theorem observed_query {Owner State ι : Type} {base : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (original : QueryImpl base (OptionT (StateT State m))) (query : (base + Audit Owner).Domain)
    (history : List (Event Owner)) (state : State) :
    Prod.map id Prod.snd <$> (((observed original query).run).run (history, state)) =
      ((simulateQ original (erase query)).run).run state := by
  cases query <;> simp [observed, erase, OptionT.run_pure, StateT.run, Functor.map_map, Prod.map_def]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A real optional stop retains the send event recorded before the unchanged primitive callback; failed serialization remains its original inner optional result. -/
theorem seal_observed {Owner State : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (original : QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (OptionT (StateT State m)))
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxSelectedSendTrace.Pending) (history : List (Event Owner)) (state : State) :
    ((simulateQ (observed original) (sendCompiler owner entry parent target nonce next (.inr pending))).run).run (history, state) =
      (fun reply => (reply.1, (history ++ [.sealing ⟨owner, entry, pending⟩], reply.2))) <$>
        ((original (.inr pending)).run).run state := by
  simp only [sendCompiler, simulateQ_bind, simulateQ_spec_query,
    OptionT.run_bind, Option.elimM, StateT.run_bind]
  simp only [observed, OptionT.run_mk, StateT.run]
  rw [pure_bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Erasing the retained audit preserves the entire adaptive optional computation and original state, including every early refusal. -/
theorem observed_program {Owner State Result ι : Type} {base : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (original : QueryImpl base (OptionT (StateT State m))) (program : OracleComp (base + Audit Owner) Result)
    (history : List (Event Owner)) (state : State) :
    Prod.map id Prod.snd <$> (((simulateQ (observed original) program).run).run (history, state)) =
      ((simulateQ original (simulateQ erase program)).run).run state := by
  induction program using OracleComp.inductionOn generalizing history state with
  | pure value => simp [simulateQ_pure, OptionT.run_pure, StateT.run_pure, Prod.map_def]
  | query_bind query next ih =>
    cases query with
    | inl request =>
      simp only [simulateQ_bind, simulateQ_spec_query, erase, OptionT.run_bind, Option.elimM,
        StateT.run_bind, map_bind]
      simp only [observed, OptionT.run_mk, StateT.run, bind_map_left]
      apply bind_congr
      intro reply
      rcases reply with ⟨none | value, after⟩
      · simp only [Option.elim_none]
        change Prod.map id Prod.snd <$> pure (none, (history, after)) = pure (none, after)
        rw [map_pure]
        rfl
      · exact ih value history after
    | inr event =>
      simp only [simulateQ_bind, simulateQ_spec_query, erase, pure_bind,
        OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
      simp only [observed, OptionT.run_mk, StateT.run, pure_bind]
      exact ih () (history ++ [event]) state

/-- Retaining the complete audit adds no underlying oracle queries, and preserves every original per-class bill even on stopped runs. -/
theorem observed_queries {Owner State Result ι κ : Type} {base : OracleSpec ι} {underlying : OracleSpec κ}
    (original : QueryImpl base (OptionT (StateT State (OracleComp underlying))))
    (program : OracleComp (base + Audit Owner) Result) (history : List (Event Owner)) (state : State)
    (select : underlying.Domain → Prop) [DecidablePred select] (bound : Nat) :
    ((((simulateQ (observed original) program).run).run (history, state))).IsQueryBoundP select bound ↔
      ((((simulateQ original (simulateQ erase program)).run).run state)).IsQueryBoundP select bound := by
  rw [← observed_program original program history state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxSelectedDriverAudit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.send_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.send_query

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.send_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.send_erased

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.receive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.receive_query

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.receive_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.receive_erased

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.send_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.receive_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.observed_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.observed_query

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.seal_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.seal_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.observed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.observed_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.observed_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedDriverAudit.observed_queries
