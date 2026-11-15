-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
/-! Successful current source build exposes the literal final service callback on its stored Ready descriptor. The cut retains the full runtime poststate; pin, occupancy and reservation prefixes may have arbitrary effects and failure behavior. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut
open RegistrationNativePlatformServerMaterialFrontend
open RegistrationServerReferenceRoot (Ready)
variable {S Encoded : Type}
private theorem pure_apply {T X : Type} {m : Type → Type} [Monad m] (value : X) (before : T) :
    (pure value : StateT T m X) before = pure (value,before) := rfl
private theorem bind_apply {T X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT T m X) (next : X → StateT T m Y) (before : T) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem lift_apply {T X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : T) : (StateT.lift work : StateT T m X) before = (fun value => (value,before)) <$> work := bind_pure_comp _ _
attribute [local irreducible] peer.begin_completion_lookup RegistrationServerSdkSource.preflight

variable (deriveAd : AdHash (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin → StateT S ProbComp (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT S ProbComp Bool) (present : U64 → StateT S ProbComp Bool)
    (service : Service (StateT S ProbComp) Encoded)

def Called (message : RegistrationNativeRelatedFamily.Message) (keyId : U64) (bytes : Encoded) (after : S) : Prop :=
  ∃ control initial before peer, peer.key_id = keyId ∧ peer.encoded = bytes ∧
    (.ok (.Ok peer),after) ∈ support ((service control initial message).run before)

private theorem finish_cut (published : RustM (RegistrationHiddenInstall.Result Encoded))
    (before : RegistrationServerMaterialFrontend.State) (reply : Result Encoded)
    (after : RegistrationServerMaterialFrontend.State) (keyId : U64) (bytes : Encoded)
    (returned : finish published before = (reply,after)) (success : reply = .ok (some (keyId,bytes))) :
    ∃ peer, published = .ok (.Ok peer) ∧ peer.key_id = keyId ∧ peer.encoded = bytes := by
  cases published with
  | fail error | div => simp only [finish,Prod.mk.injEq] at returned; simp_all
  | ok value => cases value with
    | Err previous => simp only [finish,Prod.mk.injEq] at returned; simp_all
    | Ok peer =>
      simp only [finish,Prod.mk.injEq] at returned
      rw [← returned.1] at success
      simp only [RustM.ok.injEq,Option.some.injEq,Prod.mk.injEq] at success
      exact ⟨peer,rfl,success.1,success.2⟩

/-- A supported successful final phase has the exact service result and complete final runtime state. -/
theorem after_result (control : pqxdh.ServerState) (message : RegistrationNativeRelatedFamily.Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (front afterFront : RegistrationServerMaterialFrontend.State) (before after : S) (keyId : U64) (bytes : Encoded)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      (((afterResult reserve service control message action).run front).run before)) :
    Called service message keyId bytes after := by
  cases action with
  | fail error | div => simp [afterResult] at supported
  | ok action => cases action with
    | Err previous => simp [afterResult] at supported
    | Ok initial =>
      simp only [afterResult,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
      obtain ⟨admitted,_reserved,continued⟩ := supported
      cases accepted : admitted.1 with
      | false => simp [accepted] at continued
      | true =>
        simp only [accepted,ite_true,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,mem_support_bind_iff] at continued
        obtain ⟨published,called,returned⟩ := continued
        simp only [StateT.run,pure_apply,mem_support_pure_iff,Prod.mk.injEq] at returned
        have sameRuntime : published.2 = after := returned.2.symm
        obtain ⟨peer,reply,key,encoding⟩ := finish_cut published.1 front (.ok (some (keyId,bytes))) afterFront keyId bytes returned.1.symm rfl
        refine ⟨control,initial,admitted.2,peer,key,encoding,?_⟩
        rw [show published = (.ok (.Ok peer),after) from Prod.ext reply sameRuntime] at called
        exact called

/-- Successful material demand follows the actual AD callback and retains its complete reached state. -/
theorem after_occupancy (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (message : RegistrationNativeRelatedFamily.Message) (occupied : Bool)
    (front afterFront : RegistrationServerMaterialFrontend.State) (before after : S) (keyId : U64) (bytes : Encoded)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      (((afterOccupancy deriveAd reserve service control lookup message occupied).run front).run before)) :
    Called service message keyId bytes after := by
  cases selected : lookup.resume occupied with
  | fail error | div => simp [afterOccupancy,selected] at supported
  | ok result => cases result with
    | Err previous => simp [afterOccupancy,selected] at supported
    | Ok pending =>
      simp only [afterOccupancy,selected,StateT.run_bind,StateT.run_lift,
        bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
      obtain ⟨hashed,_called,continued⟩ := supported
      exact after_result reserve service control message _ front afterFront hashed.2 after keyId bytes continued

/-- Every actual lookup, preflight and occupancy outcome retains that same successful service cut. -/
theorem after_pin (control : pqxdh.ServerState) (ready : Ready) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin))
    (front afterFront : RegistrationServerMaterialFrontend.State) (before after : S) (keyId : U64) (bytes : Encoded)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      (((afterPin deriveAd reserve present service control ready application current).run front).run before)) :
    Called service ready.reference keyId bytes after := by
  cases current with
  | fail error | div => simp [RegistrationNativePlatformServerMaterialFrontend.afterPin,StateT.run,pure_apply] at supported
  | ok current => cases current with
    | none => simp [RegistrationNativePlatformServerMaterialFrontend.afterPin,StateT.run,pure_apply] at supported
    | some current =>
      simp only [RegistrationNativePlatformServerMaterialFrontend.afterPin,StateT.run] at supported
      cases begun : peer.begin_completion_lookup control current (RegistrationServerMaterialFrontend.token ready) application with
      | fail error | div => simp [begun,pure_apply] at supported
      | ok reply => cases reply with
        | Err previous => simp [begun,pure_apply] at supported
        | Ok lookup =>
          simp only [begun] at supported
          cases requested : lookup.request with
          | fail error | div => simp [requested,pure_apply] at supported
          | ok requestedId =>
            simp only [requested] at supported
            split at supported
            · rw [bind_apply,mem_support_bind_iff] at supported
              obtain ⟨occupied,_asked,continued⟩ := supported
              exact after_occupancy deriveAd reserve service control lookup ready.reference occupied.1
                front afterFront occupied.2 after keyId bytes continued
            · simp [pure_apply] at supported

/-- Pure pin selection and all earlier effects precede the same literal final service callback. -/
theorem complete (ready : Ready) (application : Slice U8)
    (front afterFront : RegistrationServerMaterialFrontend.State) (before after : S) (keyId : U64) (bytes : Encoded)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      (((RegistrationNativePlatformServerMaterialFrontend.complete deriveAd pin reserve present service ready application).run front).run before)) :
    Called service ready.reference keyId bytes after := by
  simp only [RegistrationNativePlatformServerMaterialFrontend.complete,StateT.run,bind_apply,mem_support_bind_iff] at supported
  obtain ⟨current,_asked,continued⟩ := supported
  exact after_pin deriveAd reserve present service front.control ready application current.1 front afterFront current.2 after keyId bytes continued

/-- The moved-token build uses the Ready actually stored at its pre-call session and keeps the exact final runtime state. -/
theorem build (handle : Nat) (application : Option (Slice U8)) (ready : Ready)
    (front afterFront : RegistrationServerMaterialFrontend.State)
    (stored : front.sessions[handle]? = some (some ready)) (before after : S) (keyId : U64) (bytes : Encoded)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      (((RegistrationNativePlatformServerMaterialFrontend.build deriveAd pin reserve present service handle application).run front).run before)) :
    Called service ready.reference keyId bytes after := by
  simp only [RegistrationNativePlatformServerMaterialFrontend.build,StateT.run,RegistrationServerMaterialFrontend.take,stored] at supported
  cases application with
  | none => simp [pure_apply] at supported
  | some application => exact complete deriveAd pin reserve present service ready application _ afterFront before after keyId bytes supported
/-- Interpreting the exact current source leaves preserves the same stored descriptor and final service poststate. -/
theorem program (implementation : QueryImpl RegistrationNativePlatformServerFrontendProgram.Spec (StateT S ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (ready : Ready)
    (front afterFront : RegistrationServerMaterialFrontend.State)
    (stored : front.sessions[handle]? = some (some ready)) (before after : S) (keyId : U64) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some (keyId,bytes)),afterFront),after) ∈ support
      ((simulateQ implementation ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before)) :
    Called (fun control initial message => implementation (.service control initial message)) ready.reference keyId bytes after := by
  rw [RegistrationNativePlatformServerFrontendProgram.interpret] at supported
  exact build (fun pending => implementation (.adHash pending)) (fun current => implementation (.pin current)) (implementation .reserve)
    (fun keyId => implementation (.present keyId)) (fun control initial message => implementation (.service control initial message))
    handle application ready front afterFront stored before after keyId bytes supported

end BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.after_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.after_result

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.after_occupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerServiceCut.after_occupancy
