-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTaggedCodec
import BeaconcryptCore.Computational.PqxdhDeploymentNative

/-! Every native deployment command outside registration build and finish is independent of the internal response representation. Exact handler equality keeps the complete scheduler state, primitive caches, counters and produced-frame log. The two record equations also hold for arbitrary local record queries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborTaggedOther
open PqxdhServerAuthExperiment PqxdhJointIdentity
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem server_step (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (sender : Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) :
    PqxdhDeploymentNative.serverStep setup (CborTaggedCodec.codec wire) route query =
    PqxdhDeploymentNative.serverStep setup (CborRegistrationCodec.normalize wire sender) route query := by
  rfl

theorem beacon_step (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (sender : Std.U64) (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    PqxdhDeploymentNative.beaconStep setup (CborTaggedCodec.codec wire) index query =
    PqxdhDeploymentNative.beaconStep setup (CborRegistrationCodec.normalize wire sender) index query := by
  rfl

def Other : PqxdhDeploymentInterface.Spec.Domain → Prop
  | .inr (.build _ _) | .inr (.finish _ _) => False
  | _ => True

theorem native_other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (sender : Std.U64) (query : PqxdhDeploymentInterface.Spec.Domain) (other : Other query) :
    PqxdhDeploymentNative.handler setup (CborTaggedCodec.codec wire) checks route seed query =
    PqxdhDeploymentNative.handler setup (CborRegistrationCodec.normalize wire sender) checks route seed query := by
  cases query
  case inr command =>
    cases command
    all_goals simp only [Other] at other
    all_goals rfl
  case inl => rfl

end BeaconcryptCore.Computational.CborTaggedOther

/-- info: 'BeaconcryptCore.Computational.CborTaggedOther.server_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedOther.server_step
/-- info: 'BeaconcryptCore.Computational.CborTaggedOther.beacon_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedOther.beacon_step
/-- info: 'BeaconcryptCore.Computational.CborTaggedOther.native_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedOther.native_other
