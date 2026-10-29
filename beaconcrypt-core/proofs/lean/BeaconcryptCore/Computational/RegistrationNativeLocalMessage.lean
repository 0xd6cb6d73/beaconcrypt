-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedFamily

/-! An ordinary Beacon owner retains its own prekey scalar. Its two native prekey-DH coordinates can therefore be supplied locally to the same root service used by the selected owner. This translation preserves the actual optional input and its literal aliases; it neither tests protection nor reads the selected scalar. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeLocalMessage
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeRelatedFamily

/-- Evaluate ordinary-owner prekey DH in the same first-then-third order as the actual native input. -/
def materialize (joint : Primitives) (dh : DhInterface joint) (localScalar : ScalarBytes)
    (message : Message) : Option Message :=
  match message.third with
  | .pinned peer => do
      let first ← dh.dh localScalar message.staticPeer
      let third ← dh.dh localScalar peer
      pure { message with third := .supplied first third }
  | _ => some message

/-- The service receives exactly the ordinary owner's actual 192-byte input, independently of the selected challenge scalar. -/
theorem materialize_input (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (localScalar selectedScalar : ScalarBytes)
    (message : Message) (peer : PeerEncoding) (pinned : message.third = .pinned peer) :
    (materialize joint dh localScalar message).bind (input joint dh seed selectedScalar) =
      input joint dh seed localScalar message := by
  simp only [materialize, pinned, input, firstValue, thirdValue]
  cases first : dh.dh localScalar message.staticPeer <;>
    cases third : dh.dh localScalar peer <;>
    simp [input, address, firstValue, thirdValue]

end BeaconcryptCore.Computational.RegistrationNativeLocalMessage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalMessage.materialize_input' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalMessage.materialize_input
