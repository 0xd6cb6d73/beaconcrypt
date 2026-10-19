import BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling

/-!
A common private primitive capability combines the actual selected receive and send callbacks with real public coins, fixed-source KDF projections and the shared commitment cache. The source handler has no selected input parameter. Its alternate reuses one full76 response on byte-equal known chains in either direction and on exactly the selected public (info,input) address; hidden slots already reuse that response. All typed projections therefore keep their original aliases, without assuming key or handle injectivity.

The existing concrete input log and full-state coupling bound this routing change by a matching-input event. This module alone does not instantiate the original outer source compiler, prove the reached native cut or discharge live exposure. No public random-HKDF oracle or extra cryptographic assumption is introduced. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives
open RawCtxSelectedChain PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame

abbrev ReceiveSpec := RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial
  RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted
abbrev SendSpec := RawCtxChainSend.SendSpec Slot Slot RatchetMaterial
  RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted
abbrev Spec := ReceiveSpec + (SendSpec + RawCtxServerServices.PublicSpec)

noncomputable def handler {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => receiveLabels source writer (RawCtxKdfRequestTable.fullResponse output) request
  | .inr (.inl request) => sendLabels source writer (RawCtxKdfRequestTable.fullResponse output) request
  | .inr (.inr request) => (RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) request

def inputs : Spec.Domain → List RootOutput
  | .inl request => RawCtxSelectedQueryTrace.inputs request
  | .inr (.inl request) => RawCtxSelectedQueryTrace.inputs request
  | .inr (.inr request) => RawCtxSelectedPublicTrace.inputs request

/-- This alternate is invoked only at equal recorded bytes; a public label mismatch still uses the actual source function. -/
noncomputable def alternate {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (output : FullOutput) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl (.inl _) => pure (step source (RawCtxKdfRequestTable.fullResponse output) .hidden)
  | .inl (.inr request) => handler source writer output (.inl (.inr request))
  | .inr (.inl (.inl _)) => pure (step source (RawCtxKdfRequestTable.fullResponse output) .hidden)
  | .inr (.inl (.inr request)) => handler source writer output (.inr (.inl (.inr request)))
  | .inr (.inr (.inr (.inr view))) =>
      if view.domain.info = FixedHkdfDomain.ratchet.info then pure (view.project output)
      else handler source writer output (.inr (.inr (.inr (.inr view))))
  | .inr (.inr (.inr (.inl hash))) => handler source writer output (.inr (.inr (.inr (.inl hash))))
  | .inr (.inr (.inl coin)) => handler source writer output (.inr (.inr (.inl coin)))

noncomputable def consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxSelectedAliasCoupling.routed (handler source writer output) (alternate source writer output) inputs target

set_option backward.isDefEq.respectTransparency false in
/-- Public candidate equality is exact byte equality, without injectivity of any chain, owner or key map. -/
theorem public_input_exact (target : RootOutput) (bytes : Pqxdh.Bytes) :
    target ∈ RawCtxSelectedPublicTrace.bytesCandidate bytes ↔ bytes = target.toList := by
  by_cases length : bytes.length = 32
  · simp only [RawCtxSelectedPublicTrace.bytesCandidate, length, _root_.dite_true, List.mem_singleton]
    exact ⟨fun same => (congrArg Subtype.val same).symm,
      fun same => Subtype.ext same.symm⟩
  · simp only [RawCtxSelectedPublicTrace.bytesCandidate, length, _root_.dite_false, List.not_mem_nil, false_iff]
    exact fun same => length ((congrArg List.length same).trans target.2)

/-- Actual hidden send and receive requests keep one selected full76 response, independently of labels or owners. -/
theorem hidden_receive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) :
    consistent (Auxiliary := Auxiliary) source writer output target (.inl (.inl .hidden)) =
      pure (step source (RawCtxKdfRequestTable.fullResponse output) .hidden) := by
  simp [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedQueryTrace.inputs,
    handler, receiveLabels]

/-- The same actual byte equality selects the response on a known receive input, including a newly returned chain alias. -/
theorem known_receive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) (chain : RatchetChain) :
    consistent (Auxiliary := Auxiliary) source writer output target (.inl (.inl (.known chain))) =
      pure (step source (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) := by
  by_cases same : target = RawCtxSelectedQueryTrace.rootVector chain
  · simp [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedQueryTrace.inputs,
      alternate, same]
  · simp [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedQueryTrace.inputs,
      handler, receiveLabels, same]

/-- Send uses exactly the same hidden-input response as receive. -/
theorem hidden_send {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) :
    consistent (Auxiliary := Auxiliary) source writer output target (.inr (.inl (.inl .hidden))) =
      pure (step source (RawCtxKdfRequestTable.fullResponse output) .hidden) :=
  hidden_receive source writer output target

/-- Both directions test the same concrete known input, without distinct-key or distinct-handle premises. -/
theorem known_send {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) (chain : RatchetChain) :
    consistent (Auxiliary := Auxiliary) source writer output target (.inr (.inl (.inl (.known chain)))) =
      pure (step source (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) :=
  known_receive source writer output target chain

/-- Public views use the selected full response precisely at the same original label/input address, retaining all projections and the complete primitive state. -/
theorem public_consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) (view : JointKdfViewQuery) :
    consistent (Auxiliary := Auxiliary) source writer output target (.inr (.inr (.inr (.inr view)))) =
      if view.address = FixedHkdfDomain.ratchet.address target.toList then pure (view.project output)
      else handler source writer output (.inr (.inr (.inr (.inr view)))) := by
  simp only [consistent, RawCtxSelectedAliasCoupling.routed, inputs, RawCtxSelectedPublicTrace.inputs,
    public_input_exact]
  by_cases bytes : view.input = target.toList
  · simp only [bytes, ite_true, alternate, JointKdfViewQuery.address, FixedHkdfDomain.address,
      PqxdhJointKdf.JointKdfAddress.mk.injEq, and_true]
  · simp only [bytes, ite_false, JointKdfViewQuery.address, FixedHkdfDomain.address,
      PqxdhJointKdf.JointKdfAddress.mk.injEq, and_false]

/-- The concrete combined backend changes only at a byte candidate recorded by the same adaptive program. Full original cache, auxiliary state and optional results survive the bound. -/
theorem recorded_distance {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RootOutput) (client : OracleComp Spec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    tvDist ((simulateQ (RawCtxSelectedQueryTrace.recorded (handler source writer output) inputs) client).run (state, []))
      ((simulateQ (RawCtxSelectedQueryTrace.recorded (consistent source writer output target) inputs) client).run (state, [])) ≤
    Pr[fun result => target ∈ result.2.2 |
      (simulateQ (RawCtxSelectedQueryTrace.recorded (handler source writer output) inputs) client).run (state, [])].toReal :=
  RawCtxSelectedAliasCoupling.recorded_distance (handler source writer output)
    (alternate source writer output) inputs target client state

end BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.public_input_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.public_input_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.hidden_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.hidden_receive

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.known_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.known_receive

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.hidden_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.hidden_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.known_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.known_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.public_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.public_consistent

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.recorded_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasPrimitives.recorded_distance
