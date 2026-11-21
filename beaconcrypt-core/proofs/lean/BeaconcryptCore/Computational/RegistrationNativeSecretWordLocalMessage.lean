-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage
import BeaconcryptCore.Computational.RegistrationNativeLocalMessage

/-! An ordinary Beacon owner supplies its own two prekey-DH coordinates while retaining the opaque KEM word. Evaluation commutes with the original local translation, so arbitrary pins and literal byte aliases keep their actual native operands. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeSecretWordMessage (Message eval input)

def materialize (joint : Primitives) (dh : DhInterface joint) (localScalar : ScalarBytes)
    (message : Message) : Option Message :=
  match message.third with
  | .pinned peer => do
      let first ← dh.dh localScalar message.staticPeer
      let third ← dh.dh localScalar peer
      pure { message with third := .supplied first third }
  | _ => some message

/-- Supplying ordinary-owner coordinates changes no evaluated KEM field or failure branch. -/
theorem eval_materialize (joint : Primitives) (dh : DhInterface joint) (localScalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    (materialize joint dh localScalar message).map (eval candidate) =
      RegistrationNativeLocalMessage.materialize joint dh localScalar (eval candidate message) := by
  cases shape : message.third <;>
    simp only [materialize, RegistrationNativeLocalMessage.materialize, eval, shape,
      Option.map_some]
  rename_i peer
  cases first : dh.dh localScalar message.staticPeer <;>
    cases third : dh.dh localScalar peer <;> rfl

/-- The ordinary owner's actual optional root address is unchanged by supplying its own DH coordinates. -/
theorem materialize_input (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (localScalar selectedScalar : ScalarBytes)
    (message : Message) (peer : PeerEncoding) (pinned : message.third = .pinned peer) :
    (materialize joint dh localScalar message).bind (input joint dh seed selectedScalar) =
      input joint dh seed localScalar message := by
  simp only [materialize, pinned, input, eval, RegistrationNativeRelatedFamily.firstValue,
    RegistrationNativeRelatedFamily.thirdValue]
  cases first : dh.dh localScalar message.staticPeer <;>
    cases third : dh.dh localScalar peer <;>
    simp [input, eval, RegistrationNativeRelatedFamily.firstValue, RegistrationNativeRelatedFamily.thirdValue]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage.eval_materialize' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage.eval_materialize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage.materialize_input' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage.materialize_input
