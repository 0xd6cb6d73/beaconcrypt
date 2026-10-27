import BeaconcryptCore.Computational.PqxdhInitialPendingPost
import BeaconcryptCore.Computational.PqxdhInitialGenericBuilder

/-!
The complete Server builder uses the same exposed pending interface as the subsequent original post schedule. It retains current identity and peer lookup, consumed registration, allocation and application gates, the first private send, erase and serialization callbacks and exact publication. Only frontend state is stored here; actual shared primitive and private cache effects remain in the interpreter.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingBuilder
open PqxdhInitialPendingPost PqxdhInitialGenericBuilder
variable {ι Chain Kernel M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

section Interpretation
variable {κ : Type} {spec : OracleSpec κ} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Interpreting the actual first send retains erase, serialization, optional failure and full peer publication in their original order. -/
theorem after_interpretation (impl : QueryImpl spec m)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : P)
    (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ impl (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state) =
      PqxdhInitialGenericPublication.afterInitialization
        (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ aux)
        candidate authenticated kernel metadata state := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, simulateQ_bind,
    RawCtxGenericOwnerInterpretation.interpretedCalls]
  apply bind_congr
  rintro ⟨advanced, encrypted⟩
  apply bind_congr
  intro erased
  cases encrypted with
  | none => exact simulateQ_pure _ _
  | some encrypted =>
      simp only [simulateQ_bind]
      apply bind_congr
      intro serialized
      cases serialized <;> exact simulateQ_pure _ _

/-- Every actual identity, allocation and application gate precedes the same interpreted first-send tail. -/
theorem candidate_interpretation (impl : QueryImpl spec m)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (initial : RustM Kernel) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ impl (candidate calls aux initial pending data metadata state) =
      candidate (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ aux)
        initial pending data metadata state := by
  simp only [candidate, simulateQ_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp only [Bool.not_false, ite_true, simulateQ_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial with
      | fail error => exact simulateQ_pure _ _
      | div => exact simulateQ_pure _ _
      | ok kernel =>
          simp only [continueRust]
          split
          · exact simulateQ_pure _ _
          · split
            · simp only [simulateQ_bind]
              apply bind_congr
              intro allocated
              cases allocated
              · simp only [Bool.not_false, ite_true, simulateQ_pure]
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : pending.key_id_binding with
                | fail error => exact simulateQ_pure _ _
                | div => exact simulateQ_pure _ _
                | ok binding =>
                    simp only [simulateQ_map, after_interpretation]
            · exact simulateQ_pure _ _

/-- The original current peer allocation and complete Ready builder commute with the same interpreter, including all Rust error branches. -/
theorem ready_interpretation (impl : QueryImpl spec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ impl (readyBuild source calls aux initial binding ready metadata state) =
      readyBuild source (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ aux)
        initial binding ready metadata state := by
  unfold readyBuild usedBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => exact simulateQ_pure _ _
  | div => exact simulateQ_pure _ _
  | ok value =>
      cases value with
      | Err error => exact simulateQ_pure _ _
      | Ok key =>
          simp only [continueRust]
          cases preparation : PqxdhRegistrationInputs.prepare state.control
            (PqxdhAcceptedRegistration.usedReady source.crypto binding ready)
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact simulateQ_pure _ _
          | div => exact simulateQ_pure _ _
          | ok result =>
              cases result with
              | Err error => exact simulateQ_pure _ _
              | Ok candidate => exact candidate_interpretation impl calls aux initial candidate ready.application metadata state

end Interpretation
def consume (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) :
    Front Chain M P I D K S B :=
  { before with consumed := Function.update before.consumed index ready.consumed.consumed }

def selected (sender : M → Std.U64) (index : Fin S) (before : Front Chain M P I D K S B) :
    PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes) :=
  ⟨(before.roles.1.1 index).server, sender (before.roles.1.1 index).server.metadata,
    before.controls index, before.consumed index⟩

def install (index : Fin S) (before : Front Chain M P I D K S B)
    (updated : PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes)) :
    Front Chain M P I D K S B :=
  { roles := ((Function.update before.roles.1.1 index { before.roles.1.1 index with server := updated.server }, before.roles.1.2), before.roles.2)
    controls := Function.update before.controls index updated.control
    consumed := Function.update before.consumed index updated.consumed }

def reinstall (index : Fin S) (before : Front Chain M P I D K S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes))) :
    RustM (Option PqxdhServerRegistrationPublication.Response) × Front Chain M P I D K S B :=
  match result with
  | .ok value => (.ok value.1, install index before value.2)
  | .fail error => (.fail error, before)
  | .div => (.div, before)

noncomputable def build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (Front Chain M P I D K S B) (OracleComp (Spec extra Chain I D K X Response Shared S B))
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun before =>
  let current := consume index ready before
  let input := selected sender index current
  reinstall index current <$> readyBuild source PqxdhInitialPendingPost.calls auxForward initial
    ⟨input.server.identity, input.identityKeyId⟩ ready metadata input

section BuildInterpretation
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def interpretedBuild (impl : QueryImpl (Spec extra Chain I D K X Response Shared S B) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (Front Chain M P I D K S B) m (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun before =>
  let current := consume index ready before
  let input := selected sender index current
  reinstall index current <$> readyBuild source
    (RawCtxGenericOwnerInterpretation.interpretedCalls impl PqxdhInitialPendingPost.calls) (impl ∘ₛ auxForward) initial
    ⟨input.server.identity, input.identityKeyId⟩ ready metadata input

/-- The complete consumed-registration and first-send builder is the literal interpretation of the exposed pending source program. -/
theorem build_interpretation (impl : QueryImpl (Spec extra Chain I D K X Response Shared S B) m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) :
    simulateQ impl ((build source initial sender index metadata ready).run before) =
      (interpretedBuild impl source initial sender index metadata ready).run before := by
  simp only [build, interpretedBuild, StateT.run, simulateQ_map, ready_interpretation]

end BuildInterpretation

/-- Supplying the typed initial kernel removes the Ready root from the entire source builder, while all other private state remains retained. -/
theorem root_unused (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput) :
    build (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (B := B)
      source initial sender index metadata { ready with root := root } =
      build source initial sender index metadata ready := rfl

end BeaconcryptCore.Computational.PqxdhInitialPendingBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.after_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.after_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.candidate_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.candidate_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.ready_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.ready_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.build_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.build_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingBuilder.root_unused
