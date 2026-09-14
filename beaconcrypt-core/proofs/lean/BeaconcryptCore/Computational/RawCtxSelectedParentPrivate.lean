import BeaconcryptCore.Computational.RawCtxSelectedParentReadMask

/-!
The selected child is replaced only on private KDF callbacks. Public HKDF evaluations remain the supplied common real function at every input, including a successful guess of the selected input. The same complete original input list bounds changes at known private byte aliases; it may conservatively also count public inputs and live values. The read-only exposure flag and all shared primitive effects are retained. This is the native private-table comparison interface, not a public random-function game.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentPrivate
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

noncomputable def alternate {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl (.inl (.inl _)) => pure (RawCtxSelectedParentTable.step prior entry
      (RawCtxKdfRequestTable.fullResponse output) .hidden)
  | .inl (.inr (.inl (.inl _))) => pure (RawCtxSelectedParentTable.step prior entry
      (RawCtxKdfRequestTable.fullResponse output) .hidden)
  | query => RawCtxSelectedParentLive.handler source writer prior entry output reader view query

noncomputable def handler {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) :=
  RawCtxSelectedAliasCoupling.routed
    (RawCtxSelectedParentLive.handler (Auxiliary := Auxiliary) source writer prior entry output reader view)
    (alternate source writer prior entry output reader view) inputs target

noncomputable def observed {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) :=
  RawCtxFlaggedQueryTrace.trace
    (handler (Auxiliary := Auxiliary) source writer prior entry output reader view target)
    inputs RawCtxSelectedParentReadMask.direct

/-- Every original public projection stays real, even when its input is the selected private input. -/
theorem public_real {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) (query : JointKdfViewQuery) :
    handler (Auxiliary := Auxiliary) source writer prior entry output reader view target
      (.inl (.inr (.inr (.inr (.inr query))))) = pure (view query) := by
  simp [handler, RawCtxSelectedAliasCoupling.routed, alternate, RawCtxSelectedParentLive.handler]

/-- A known receive alias uses the same full child response as the omitted input, while every other private input retains the predecessor lookup. -/
theorem known_receive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) (chain : RatchetChain) :
    handler (Auxiliary := Auxiliary) source writer prior entry output reader view target
      (.inl (.inl (.inl (.known chain)))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) := by
  by_cases same : target = RawCtxSelectedQueryTrace.rootVector chain <;>
    simp [handler, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedAliasPrimitives.inputs,
      RawCtxSelectedQueryTrace.inputs, alternate, RawCtxSelectedParentLive.handler,
      RawCtxSelectedParentSource.labelReceive, same]

/-- The unavailable receive input uses the selected complete response. -/
theorem hidden_receive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) :
    handler (Auxiliary := Auxiliary) source writer prior entry output reader view target
      (.inl (.inl (.inl .hidden))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) .hidden) := by
  simp [handler, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedAliasPrimitives.inputs,
    RawCtxSelectedQueryTrace.inputs, RawCtxSelectedParentLive.handler, RawCtxSelectedParentSource.labelReceive]

/-- Send uses the identical known-input alias test and child response. -/
theorem known_send {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) (chain : RatchetChain) :
    handler (Auxiliary := Auxiliary) source writer prior entry output reader view target
      (.inl (.inr (.inl (.inl (.known chain))))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) :=
  known_receive source writer prior entry output reader view target chain

/-- Send and receive reuse the same unavailable-input response. -/
theorem hidden_send {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) :
    handler (Auxiliary := Auxiliary) source writer prior entry output reader view target
      (.inl (.inr (.inl (.inl .hidden)))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) .hidden) :=
  hidden_receive source writer prior entry output reader view target

/-- Actual optional read replies stay unchanged by private alias routing. -/
theorem read_same {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput) (query : ReadInput) :
    handler (Auxiliary := Auxiliary) source writer prior entry output reader view target (.inr query) =
      pure (reader query.1 query.2) := by
  simp [handler, RawCtxSelectedAliasCoupling.routed, alternate, RawCtxSelectedParentLive.handler]
  rfl

/-- Private alias routing costs at most the same original full candidate event, retaining all source state and prior read exposure. -/
theorem distance {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput)
    (client : OracleComp Spec Result) (state : RawCtxSelectedParentLive.State Auxiliary) :
    tvDist ((simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view) client).run state)
      ((simulateQ (observed source writer prior entry output reader view target) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 |
        (simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view) client).run state].toReal := by
  exact RawCtxFlaggedQueryTrace.distance
    (RawCtxSelectedParentLive.handler source writer prior entry output reader view)
    (alternate source writer prior entry output reader view)
    inputs RawCtxSelectedParentReadMask.direct target client state

end BeaconcryptCore.Computational.RawCtxSelectedParentPrivate

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.public_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.public_real
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.known_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.known_receive
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.hidden_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.hidden_receive
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.known_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.known_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.hidden_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.hidden_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.read_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.read_same
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivate.distance
