-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal
import BeaconcryptCore.Computational.CborRawRecordOriginFlatten

/-! Installed hidden origins persist at their physical record handles under every permitted private CTX reply. These receipts read actual Protocol control and use its proved one-use installation and forward-storage laws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
open PqxdhRecordLiftInterface (WorldSpec Slot)
open PqxdhRecordLiftProtocol (Control)
open PqxdhRecordLiftProtocolHistory (Safe view)
open PqxdhRecordLiftWorldProvenance (Forward)
variable {n : Nat} {Reader Response Secret Value : Type}

/-- Closing the actual cursor, Protocol and private service can only select an original open World reply path. -/
theorem open_support (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (shell : CborRecordWorldClient.Shell)
    (before : Control n) (secret : Secret)
    (result : ((Value × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work shell before secret)) :
    result.1.1.1 ∈ support work := by
  have privateSupport : result.1 ∈ support
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler work).run shell)).run before) := by
    apply OracleComp.support_simulateQ_run'_subset service _ secret
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have protocolSupport : result.1.1 ∈ support ((simulateQ CborRecordWorldClient.handler work).run shell) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhRecordLiftProtocol.handler codec.frameRead route) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst privateSupport
  apply OracleComp.support_simulateQ_run'_subset CborRecordWorldClient.handler work shell
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst protocolSupport

/-- The structural source forward relation preserves every already installed hidden handle and its exact slot. -/
theorem forward (before after : Control n) (advanced : Forward (view before) (view after))
    (handle : PqxdhDeploymentInterface.Handle) (slot : Slot n)
    (installed : PqxdhRecordLiftIdeal.handleSlot before handle = some slot) :
    PqxdhRecordLiftIdeal.handleSlot after handle = some slot := by
  cases handle with
  | peer keyId =>
      simp only [PqxdhRecordLiftIdeal.handleSlot, PqxdhRecordLiftIdeal.peerSlot, Option.bind_eq_some_iff] at installed
      obtain ⟨server, present, peer, stored, origin⟩ := installed
      cases formed : peer.kernel with
      | known kernel => simp only [formed, PqxdhRecordLiftWorldCompiler.StoredKernel.origin] at origin; cases origin
      | hidden hidden kernel =>
          simp only [formed, PqxdhRecordLiftWorldCompiler.StoredKernel.origin] at origin
          have same : hidden = slot := Option.some.inj origin
          subst hidden
          obtain ⟨nextServer, nextPeer, serverAt, peerAt, ahead⟩ := advanced.1 server present keyId peer stored
          obtain ⟨next, nextAt, _progress⟩ := ahead slot kernel formed
          change after.server = some nextServer at serverAt
          simp only [PqxdhRecordLiftIdeal.handleSlot, PqxdhRecordLiftIdeal.peerSlot, serverAt,
            Option.bind_some, peerAt, nextAt, PqxdhRecordLiftWorldCompiler.StoredKernel.origin]
  | owner owner =>
      simp only [PqxdhRecordLiftIdeal.handleSlot, PqxdhRecordLiftIdeal.ownerSlot, Option.bind_eq_some_iff] at installed
      obtain ⟨phase, present, origin⟩ := installed
      cases phase with
      | inactive phase => cases origin
      | established shell stored =>
          cases formed : stored with
          | known kernel =>
              simp only [PqxdhRecordLiftWorldCompiler.Phase.origin, formed,
                PqxdhRecordLiftWorldCompiler.StoredKernel.origin] at origin
              cases origin
          | hidden hidden kernel =>
              simp only [PqxdhRecordLiftWorldCompiler.Phase.origin, formed,
                PqxdhRecordLiftWorldCompiler.StoredKernel.origin] at origin
              have same : hidden = slot := Option.some.inj origin
              subst hidden
              obtain ⟨nextShell, nextKernel, nextAt, ahead⟩ := advanced.2 owner shell stored present
              obtain ⟨next, nextKernelAt, _progress⟩ := ahead slot kernel formed
              change after.owners[owner]? = some (.established nextShell nextKernel) at nextAt
              simp only [PqxdhRecordLiftIdeal.handleSlot, PqxdhRecordLiftIdeal.ownerSlot, nextAt,
                Option.bind_some, PqxdhRecordLiftWorldCompiler.Phase.origin, nextKernelAt,
                PqxdhRecordLiftWorldCompiler.StoredKernel.origin]

/-- The actual cursor-aware World program preserves control safety and every previous hidden handle under any private service. -/
theorem interpreted (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (shell : CborRecordWorldClient.Shell)
    (before : Control n) (safe : Safe before) (secret : Secret)
    (result : ((Value × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work shell before secret)) :
    Safe result.1.2 ∧ ∀ handle slot, PqxdhRecordLiftIdeal.handleSlot before handle = some slot →
      PqxdhRecordLiftIdeal.handleSlot result.1.2 handle = some slot := by
  have step := PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route
    ((simulateQ CborRecordWorldClient.handler work).run shell) before safe secret result supported
  exact ⟨step.1, forward before result.1.2 step.2⟩

end BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots.forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots.forward
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots.interpreted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots.open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots.open_support
