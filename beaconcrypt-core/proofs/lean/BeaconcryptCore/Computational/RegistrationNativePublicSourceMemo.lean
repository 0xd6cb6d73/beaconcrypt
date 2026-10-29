-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceServer
import BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt

/-! Prepared roots are private source receipts, derived at successful native preparation. The current environment's signing history remains a separate coordinate of the exact memo lens; these lemmas add no successful-prepare restriction to the public experiment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceEffects (Extra close)
open RegistrationNativePublicSourceCallbacks (services)
open RegistrationNativePublicSourceState (MemoCorrect)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationAuthenticationCompiler.program

variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

instance : RegistrationServerReferenceMemoReceipt.MemoStore Extra where
  read := Prod.fst
  remember := RegistrationNativePublicSourceCallbacks.remember
  read_remember := by
    intro before message root
    change Function.update before.1 message root message = root
    exact Function.update_self _ _ _

/-- The private source memo starts empty, so its functional source correctness is unconditional. -/
theorem initial_correct (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) :
    MemoCorrect setup seed scalar RegistrationNativeReferenceInterpreter.initial := by
  intro message root stored
  cases stored

/-- Preparing any actual source descriptor preserves correctness of all memo entries. -/
theorem update_correct (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (memo : RegistrationNativeReferenceInterpreter.State)
    (correct : MemoCorrect setup seed scalar memo) (message : Message) :
    MemoCorrect setup seed scalar (Function.update memo message
      (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message)) := by
  intro queried root stored
  by_cases equal : queried = message
  · subst queried
    simpa only [Function.update_self] using stored
  · rw [Function.update_of_ne equal] at stored
    exact correct queried root stored

/-- A literal source preparation never destroys any earlier successfully prepared root. -/
theorem update_keeps (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (memo : RegistrationNativeReferenceInterpreter.State)
    (correct : MemoCorrect setup seed scalar memo) (message queried : Message) (root : RootOutput)
    (stored : memo queried = some root) :
    Function.update memo message
      (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message) queried = some root := by
  by_cases equal : queried = message
  · subst queried
    rw [Function.update_self]
    exact correct message root stored
  · rw [Function.update_of_ne equal]
    exact stored

/-- An actual successful mixed-client accept returns a native live capability whose literal source root is already prepared. -/
theorem accept_receipt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (selected : Bool) (packet : registration.InitPacket)
    (handle : Nat) (before after : RegistrationNativePublicSourceServer.State n KemSK source)
    (supported : (.ok (some handle), after) ∈ support
      ((RegistrationNativePublicSourceServer.run setup wire route sign seed scalar selected
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    ∃ ready root, after.1.server.sessions[handle]? = some (some ready) ∧
      after.2.roots ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  have reached : (.ok (some handle), RegistrationNativePublicSourceServer.layout after) ∈ support
      ((RegistrationServerOpenReferenceSourceAccept.close setup seed scalar
        RegistrationNativePublicSourceCallbacks.remember (services setup wire route sign seed scalar)
          (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run
        (RegistrationNativePublicSourceServer.layout before)) := by
    rw [← RegistrationNativePublicSourceServer.server_layout setup wire route sign seed scalar selected]
    rw [support_map]
    exact ⟨(.ok (some handle), after), supported, rfl⟩
  exact RegistrationServerReferenceMemoReceipt.accept setup checks verify seed scalar
    (services setup wire route sign seed scalar) packet handle
    (RegistrationNativePublicSourceServer.layout before) (RegistrationNativePublicSourceServer.layout after) reached

end BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.initial_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.initial_correct
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.update_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.update_correct
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.update_keeps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.update_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.accept_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo.accept_receipt
