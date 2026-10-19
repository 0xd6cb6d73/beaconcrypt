import BeaconcryptCore.Computational.RawCtxSelectedInitialSource
import BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler
import BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace

/-!
Replacing the retained initializer first32 coordinate changes a private known-input KDF callback only when its exact input is the initializer root. Both directions share the actual ratchet domain, so this case is charged to the original candidate list rather than excluded by a new freshness rule. Public projections, optional live replies and complete shared effects stay identical on both sides. The supplied child response may be arbitrary; this module makes no target-independence or small-alias-probability claim.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialMask
open RawCtxSelectedChain RawCtxSelectedInitialEntry RawCtxSelectedInitialTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev View := (query : JointKdfViewQuery) → JointKdfViewSpec.Range query

def atRoot (root other : RootOutput) (nonce : NonceOutput) : Entry :=
  ⟨FixedHkdfDomain.ratchet.address root.toList, other, nonce⟩

/-- A known private initializer request is exactly an equality of the actual 32 input bytes. -/
theorem initializer_exact (root other : RootOutput) (nonce : NonceOutput) (chain : RatchetChain) :
    initializerQuery (atRoot root other nonce) (.known chain) =
      decide (root = RawCtxSelectedQueryTrace.rootVector chain) := by
  simp [initializerQuery, atRoot, RawCtxKdfRequestTable.address, RawCtxChainSend.nativeRequest,
    FixedHkdfDomain.address, FixedHkdfDomain.info, RawCtxSelectedQueryTrace.rootVector]
  apply decide_eq_decide.mpr
  exact ⟨fun h => Subtype.ext h.symm, fun h => (congrArg List.Vector.toList h).symm⟩

noncomputable def handler {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (reader : Reader) (view : View) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl (.inl request) => RawCtxSelectedInitialSource.labelReceive source writer prior entry target
      (RawCtxKdfRequestTable.fullResponse output) request
  | .inl (.inr (.inl request)) => RawCtxSelectedInitialSource.labelSend source writer prior entry target
      (RawCtxKdfRequestTable.fullResponse output) request
  | .inl (.inr (.inr (.inr (.inr query)))) => pure (view query)
  | .inl (.inr (.inr (.inr (.inl hash)))) =>
      (RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) (.inr (.inl hash))
  | .inl (.inr (.inr (.inl coin))) =>
      (RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) (.inl coin)
  | .inr query => pure (reader query.1 query.2)

noncomputable def privateInputs : Spec.Domain → List RootOutput
  | .inl (.inl (.inl (.known chain))) => [RawCtxSelectedQueryTrace.rootVector chain]
  | .inl (.inr (.inl (.inl (.known chain)))) => [RawCtxSelectedQueryTrace.rootVector chain]
  | _ => []

/-- Outside a recorded initializer-root input the full primitive callback does not use the retained first32 coordinate. -/
theorem query_safe {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (root other left right : RootOutput) (nonce : NonceOutput) (output : FullOutput)
    (reader : Reader) (view : View) (query : Spec.Domain) (safe : root ∉ privateInputs query) :
    handler (Auxiliary := Auxiliary) source writer prior (atRoot root other nonce) left output reader view query =
      handler source writer prior (atRoot root other nonce) right output reader view query := by
  rcases query with ((slot | opening) | ((slot | sealing) | (coin | (hash | view)))) | read
  all_goals try rfl
  all_goals simp only [handler, RawCtxSelectedInitialSource.labelReceive, RawCtxSelectedInitialSource.labelSend]
  all_goals apply congrArg pure
  all_goals apply step_before
  all_goals cases slot <;> simp_all [privateInputs, initializer_exact]
  all_goals rfl

/-- Exact-input routing replaces the coordinate throughout the same full primitive interface. -/
theorem routed_eq {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (root other left right : RootOutput) (nonce : NonceOutput) (output : FullOutput)
    (reader : Reader) (view : View) :
    RawCtxSelectedAliasCoupling.routed
      (handler (Auxiliary := Auxiliary) source writer prior (atRoot root other nonce) left output reader view)
      (handler source writer prior (atRoot root other nonce) right output reader view) privateInputs root =
      handler source writer prior (atRoot root other nonce) right output reader view := by
  funext query
  by_cases hit : root ∈ privateInputs query
  · simp [RawCtxSelectedAliasCoupling.routed, hit]
  · simpa only [RawCtxSelectedAliasCoupling.routed, ite_eq_right hit] using
      query_safe source writer prior root other left right nonce output reader view query hit

/-- The full adaptive replacement costs the actual initializer-root candidate event, with every prior candidate and separate live-disclosure flag retained. -/
theorem distance {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (root other left right : RootOutput) (nonce : NonceOutput) (output : FullOutput)
    (reader : Reader) (view : View) (direct : Spec.Domain → Bool) (client : OracleComp Spec Result)
    (state : (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) × Bool) :
    tvDist ((simulateQ (RawCtxFlaggedQueryTrace.trace
      (handler source writer prior (atRoot root other nonce) left output reader view) privateInputs direct) client).run state)
      ((simulateQ (RawCtxFlaggedQueryTrace.trace
        (handler source writer prior (atRoot root other nonce) right output reader view) privateInputs direct) client).run state) ≤
      Pr[fun result => root ∈ result.2.1.2 | (simulateQ (RawCtxFlaggedQueryTrace.trace
        (handler source writer prior (atRoot root other nonce) left output reader view) privateInputs direct) client).run state].toReal := by
  have bound := RawCtxFlaggedQueryTrace.distance
    (handler source writer prior (atRoot root other nonce) left output reader view)
    (handler source writer prior (atRoot root other nonce) right output reader view) privateInputs direct root client state
  rwa [routed_eq] at bound

/-- Each actual primitive callback adds at most one private known-input candidate. -/
theorem inputs_bound (query : Spec.Domain) : (privateInputs query).length ≤ 1 := by
  rcases query with ((slot | opening) | ((slot | sealing) | publicQuery)) | read
  all_goals try exact Nat.zero_le 1
  all_goals cases slot <;> simp [privateInputs]

end BeaconcryptCore.Computational.RawCtxSelectedInitialMask

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialMask.initializer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialMask.initializer_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialMask.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialMask.query_safe
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialMask.routed_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialMask.routed_eq
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialMask.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialMask.distance
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialMask.inputs_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialMask.inputs_bound
