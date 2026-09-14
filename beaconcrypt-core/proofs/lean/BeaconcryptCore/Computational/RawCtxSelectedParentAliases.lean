import BeaconcryptCore.Computational.RawCtxSelectedParentLive
import BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace

/-!
Exact byte aliases in either direction and public projections use the same selected child response, while all other addresses retain the prior lookup and predecessor entry. Routing preserves the complete shared primitive state, optional reads, original candidate prefix and separate direct-disclosure flag. The coupling charges an actual candidate event; its real-world and uniform-world bounds require their separate computational arguments. Neither keys nor request addresses are assumed distinct.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentAliases
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open RawCtxSelectedParentLive
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

noncomputable def alternate {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl (.inl (.inl _)) => pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) .hidden)
  | .inl (.inr (.inl (.inl _))) => pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) .hidden)
  | .inl (.inr (.inr (.inr (.inr query)))) =>
      if query.domain.info = FixedHkdfDomain.ratchet.info then pure (query.project output)
      else handler source writer prior entry output reader view (.inl (.inr (.inr (.inr (.inr query)))))
  | query => handler source writer prior entry output reader view query

noncomputable def consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) (target : RootOutput) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxSelectedAliasCoupling.routed (handler source writer prior entry output reader view)
    (alternate source writer prior entry output reader view) inputs target

noncomputable def observed {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) (target : RootOutput) :=
  RawCtxFlaggedQueryTrace.trace (consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target)
    inputs (RawCtxSelectedParentLive.direct entry)

/-- The unavailable child input uses one complete supplied response in the original receive interface. -/
theorem hidden_receive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) (target : RootOutput) :
    consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target (.inl (.inl (.inl .hidden))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) .hidden) := by
  simp [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedAliasPrimitives.inputs,
    RawCtxSelectedQueryTrace.inputs, RawCtxSelectedParentLive.handler, RawCtxSelectedParentSource.labelReceive]

/-- Every known equal-byte receive input routes to that same child response; no distinct-key premise is used. -/
theorem known_receive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (target : RootOutput) (chain : RatchetChain) :
    consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target (.inl (.inl (.inl (.known chain)))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) := by
  by_cases same : target = RawCtxSelectedQueryTrace.rootVector chain <;>
    simp [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedAliasPrimitives.inputs,
      RawCtxSelectedQueryTrace.inputs, alternate, RawCtxSelectedParentLive.handler,
      RawCtxSelectedParentSource.labelReceive, same]

/-- Send and receive share the identical unavailable-input response. -/
theorem hidden_send {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) (target : RootOutput) :
    consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target (.inl (.inr (.inl (.inl .hidden)))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) .hidden) :=
  hidden_receive source writer prior entry output reader view target

/-- Known send inputs use the same concrete equality and response as receive inputs. -/
theorem known_send {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (target : RootOutput) (chain : RatchetChain) :
    consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target (.inl (.inr (.inl (.inl (.known chain))))) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) :=
  known_receive source writer prior entry output reader view target chain

/-- In the routed comparison public aliases use the selected child response only at its exact label and input; all other public evaluations are unchanged. -/
theorem public_consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (target : RootOutput) (query : JointKdfViewQuery) :
    consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target
        (.inl (.inr (.inr (.inr (.inr query))))) =
      if query.address = FixedHkdfDomain.ratchet.address target.toList then pure (query.project output)
      else pure (view query) := by
  simp only [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedAliasPrimitives.inputs,
    RawCtxSelectedPublicTrace.inputs, RawCtxSelectedAliasPrimitives.public_input_exact]
  by_cases bytes : query.input = target.toList <;>
    simp [bytes, alternate, RawCtxSelectedParentLive.handler, JointKdfViewQuery.address, FixedHkdfDomain.address]

/-- Routing never changes an actual optional live reply, including known-value aliases. -/
theorem read_consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (target : RootOutput) (query : ReadInput) :
    consistent (Auxiliary := Auxiliary) source writer prior entry output reader view target (.inr query) =
      pure (reader query.1 query.2) := by
  simp [consistent, RawCtxSelectedAliasCoupling.routed, alternate, RawCtxSelectedParentLive.handler]
  rfl

/-- The complete routed continuation differs by at most its original final candidate event, retaining every prior entry and the separate direct-disclosure flag. -/
theorem distance {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (target : RootOutput) (client : OracleComp Spec Result) (state : RawCtxSelectedParentLive.State Auxiliary) :
    tvDist ((simulateQ (RawCtxSelectedParentLive.observed source writer prior entry output reader view) client).run state)
      ((simulateQ (observed source writer prior entry output reader view target) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 |
        (simulateQ (RawCtxSelectedParentLive.observed source writer prior entry output reader view) client).run state].toReal := by
  exact RawCtxFlaggedQueryTrace.distance (handler source writer prior entry output reader view)
    (alternate source writer prior entry output reader view) inputs (RawCtxSelectedParentLive.direct entry) target client state

end BeaconcryptCore.Computational.RawCtxSelectedParentAliases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.hidden_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.hidden_receive
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.known_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.known_receive
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.hidden_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.hidden_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.known_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.known_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.public_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.public_consistent
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.read_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.read_consistent
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentAliases.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentAliases.distance
