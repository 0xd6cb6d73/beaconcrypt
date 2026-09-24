import BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds

/-!
The material-labelled driver supplies the actual Server and Beacon family frontend. Native interpretation retains all role fields, peer lookup, AD selection, parsing, rejection and publication while the executable frontend receives no selected message key. Live reads carry their original optional labelled reply and timestamped history; a separate stopping interpreter can withhold a selected skipped-key disclosure before giving unavailable bytes to the original client.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageFamily
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals
variable {M P I D K A : Type} {S B : Nat}

noncomputable def calls {m : Type → Type*} [Monad m]
    (receiveService : QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) m)
    (sendService : QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) m)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    RawCtxChainOwner.Calls Kernel m where
  receive kernel sequence context := simulateQ receiveService (RawCtxSelectedMessageDriver.receive parent target nonce next kernel sequence context)
  send kernel context := simulateQ sendService (RawCtxSelectedMessageDriver.send parent target nonce next kernel context)

noncomputable def frontend {m : Type → Type*} [Monad m]
    (receiveService : QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) m)
    (sendService : QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) m)
    (publicService : QueryImpl RawCtxServerServices.PublicSpec m)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericFamilyFrontend.impl (calls receiveService sendService parent target nonce next) publicService
    sender route decode (PeerMetadata := P) (Identity := I) (DhPair := D) (KemPair := K) (serverCount := S) (beaconCount := B)

/-- Every actual native family operation has the same complete labelled-role publication under the concrete selected private table and original public services. -/
theorem frontend_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (state : Roles M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer (privateTable prior parent target (response key nonce next)))
      ((RawCtxProtocolRoles.protocolImpl S B sender route decode query).run
        (RawCtxGenericRoleFamily.nativeRoles (nativeKernel key) state)) =
      Prod.map id (RawCtxGenericRoleFamily.nativeRoles (nativeKernel key)) <$>
        (frontend (receiveServices source writer prior parent key target nonce next)
          (sendServices source writer prior parent key target nonce next)
          (RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxServerServices.publicLift)
          parent target nonce next sender route decode query).run state := by
  exact RawCtxGenericFamilyNative.step (nativeKernel key)
    (calls (receiveServices source writer prior parent key target nonce next)
      (sendServices source writer prior parent key target nonce next) parent target nonce next)
    (RawCtxFunctionalFamily.backend (A := A) source writer (privateTable prior parent target (response key nonce next)))
    (RawCtxSelectedMessageDriver.receive_source source writer prior parent key target nonce next)
    (RawCtxSelectedMessageDriver.send_source source writer prior parent key target nonce next)
    sender route decode query state

def tick (history : RawCtxSelectedMessageFreshness.History S B) : RawCtxSelectedMessageFreshness.History S B :=
  { history with position := history.position + 1 }

/-- Every non-read source action keeps the same observation list and advances the original API timestamp. -/
theorem interpret_tick (key : RootOutput) (history : RawCtxSelectedMessageFreshness.History S B) :
    interpretHistory key (tick history) = RawCtxProtocolReveals.tick (interpretHistory key history) := rfl

abbrev Reader (m : Type → Type*) (S B : Nat) :=
  (request : RawCtxProtocolReveals.Request S B) →
    (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request → m ((RawCtxProtocolReveals.RevealSpec S B).Range request)

noncomputable def live {m : Type → Type*} [Monad m]
    (receiveService : QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) m)
    (sendService : QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) m)
    (publicService : QueryImpl RawCtxServerServices.PublicSpec m) (reader : Reader m S B)
    (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (State M P I D K S B) m) :=
  fun query state => match query with
  | .inl request => do
    let result ← (frontend receiveService sendService publicService parent target nonce next sender route decode request).run state.1
    pure (result.1, (result.2, tick state.2))
  | .inr request => do
    let observed := RawCtxSelectedMessageReveals.step request state
    let value ← reader request observed.1
    pure (value, observed.2)

def sourceReader {m : Type → Type*} [Monad m] (key : RootOutput) : Reader m S B :=
  fun request value => pure (interpretReply key request value)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual native live step retains the complete original role state and the exact interpreted observation history. -/
theorem live_source_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : State M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer (privateTable prior parent target (response key nonce next)))
      ((RawCtxProtocolReveals.protocolImpl S B sender route decode query).run (nativeState key state)) =
      Prod.map id (nativeState key) <$>
        (live (receiveServices source writer prior parent key target nonce next)
          (sendServices source writer prior parent key target nonce next)
          (RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxServerServices.publicLift)
          (sourceReader key) parent target nonce next sender route decode query).run state := by
  cases query with
  | inl request =>
    have mapped := congrArg (fun computation => (fun result =>
      (result.1, (result.2, RawCtxProtocolReveals.tick (interpretHistory key state.2)))) <$> computation)
      (frontend_source (A := A) source writer prior parent key target nonce next sender route decode request state.1)
    simpa only [RawCtxProtocolReveals.protocolImpl, live, StateT.run, nativeState, bind_pure_comp,
      simulateQ_map, Functor.map_map, interpret_tick, Prod.map_def, id_eq] using mapped
  | inr request =>
    simp only [RawCtxProtocolReveals.protocolImpl, live, StateT.run, nativeState, source_reply, sourceReader,
      RawCtxSelectedMessageReveals.step, pure_bind, simulateQ_pure, map_pure, Prod.map_def, id_eq, interpret_note, observation_reply]

/-- Every adaptive native family continuation has the same full material-labelled role and history interpretation, with no assumed schedule equality. -/
theorem live_source_schedule {Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : State M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer (privateTable prior parent target (response key nonce next)))
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run (nativeState key state)) =
      Prod.map id (nativeState key) <$>
        (simulateQ (live (receiveServices source writer prior parent key target nonce next)
          (sendServices source writer prior parent key target nonce next)
          (RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxServerServices.publicLift)
          (sourceReader key) parent target nonce next sender route decode) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact (map_run_simulateQ_eq_of_query_map_eq
    (live (receiveServices source writer prior parent key target nonce next)
      (sendServices source writer prior parent key target nonce next)
      (RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxServerServices.publicLift)
      (sourceReader key) parent target nonce next sender route decode)
    ((RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next))).mapStateTBase
      (RawCtxProtocolReveals.protocolImpl S B sender route decode))
    (nativeState key)
    (fun query state => (live_source_step (A := A) source writer prior parent key target nonce next sender route decode query state).symm)
    client state).symm

/-- Every actual prior role family and reveal history can enter the complete adaptive labelled interpreter, including preexisting byte aliases. -/
theorem live_known_schedule {Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer (privateTable prior parent target (response key nonce next)))
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run state) =
      Prod.map id (nativeState key) <$>
        (simulateQ (live (receiveServices source writer prior parent key target nonce next)
          (sendServices source writer prior parent key target nonce next)
          (RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxServerServices.publicLift)
          (sourceReader key) parent target nonce next sender route decode) client).run
            (RawCtxSelectedMessageRevealInitialization.fromState state) := by
  simpa only [RawCtxSelectedMessageRevealInitialization.state_roundtrip] using
    live_source_schedule (A := A) source writer prior parent key target nonce next sender route decode client
      (RawCtxSelectedMessageRevealInitialization.fromState state)

end BeaconcryptCore.Computational.RawCtxSelectedMessageFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.frontend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.frontend_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.interpret_tick' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.interpret_tick
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.live_source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.live_source_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.live_source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.live_source_schedule
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.live_known_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageFamily.live_known_schedule
