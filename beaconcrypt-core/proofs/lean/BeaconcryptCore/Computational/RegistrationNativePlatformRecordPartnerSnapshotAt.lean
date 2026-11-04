-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal
/-! Actual hidden slot receipts retain their complete selected input and the public handle at the same successful native installation ordinal. Persistent dictionary injectivity compares inputs directly, without identifying roots or material. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role Slot)
open RegistrationNativePlatformRecordSlotGhost (Receipt)
open RegistrationNativePlatformRecordPartnerSlotTrace (State Valid)
open RegistrationNativePlatformRecordPartnerSnapshotOrdinal (receiptHandles)
variable {n : Nat} {I KemSK ProviderState Physical : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
local notation "Input" => RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
local notation "Selected" => RegistrationNativeSelectiveHiddenService.selected
  (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate

/-- A hidden receipt and the exact source handle list identify one common native/public installation ordinal. -/
theorem receipt_at (current : State n KemSK ProviderState Physical) (valid : Valid Input Selected current)
    (transcript : List RegistrationNativeInterface.Entry) (role : Role)
    (publicHandles : receiptHandles role current.1.snapshot=RegistrationNativeInstallOrdinals.handles role transcript)
    (counts : RegistrationNativeInstallOrdinals.Counts role current.2.1.events transcript)
    (position : Nat) (receipt : Receipt n) (found : current.1.snapshot.installs[position]?=some receipt)
    (typed : receipt.role=role) (slot : Slot n) (hidden : receipt.slot=some slot) :
    ∃ ordinal message bytes,
      RegistrationNativeInstallOrdinals.At role current.2.1.events transcript ordinal message receipt.handle ∧
      Input message=some bytes ∧ Selected bytes=true ∧ current.2.2.1.1.keys.slots bytes=some slot := by
  obtain ⟨entries,past,later,entry,message,bytes,ordered,split,_length,actual,named,formed,selected,assigned,_events⟩ :=
    RegistrationNativePlatformRecordPartnerSlotTrace.receipt_at setup seed scalar candidate current valid position receipt found slot hidden
  obtain ⟨ordinal,located⟩ := RegistrationNativePlatformRecordPartnerSnapshotOrdinal.from_witness role current.1 current.2.1
    transcript entries past later entry ordered publicHandles counts split
    ((congrArg Receipt.role actual).trans typed) message named
  exact ⟨ordinal,message,bytes,by simpa only [actual] using located,formed,selected,assigned⟩

/-- Opposite-role hidden receipts for one persistent slot have their own public ordinals and the same complete selected input. -/
theorem same_slot (current : State n KemSK ProviderState Physical) (valid : Valid Input Selected current)
    (transcript : List RegistrationNativeInterface.Entry)
    (publicHandles : ∀role,receiptHandles role current.1.snapshot=RegistrationNativeInstallOrdinals.handles role transcript)
    (counts : ∀role,RegistrationNativeInstallOrdinals.Counts role current.2.1.events transcript)
    (peerPosition ownerPosition : Nat) (peerReceipt ownerReceipt : Receipt n)
    (peerFound : current.1.snapshot.installs[peerPosition]?=some peerReceipt)
    (ownerFound : current.1.snapshot.installs[ownerPosition]?=some ownerReceipt)
    (peerRole : peerReceipt.role=.server) (ownerRole : ownerReceipt.role=.beacon)
    (slot : Slot n) (peerSlot : peerReceipt.slot=some slot) (ownerSlot : ownerReceipt.slot=some slot) :
    ∃ peerOrdinal ownerOrdinal peerMessage ownerMessage bytes,
      RegistrationNativeInstallOrdinals.At .server current.2.1.events transcript peerOrdinal peerMessage peerReceipt.handle ∧
      RegistrationNativeInstallOrdinals.At .beacon current.2.1.events transcript ownerOrdinal ownerMessage ownerReceipt.handle ∧
      Input peerMessage=some bytes ∧ Input ownerMessage=some bytes ∧ Selected bytes=true := by
  obtain ⟨peerOrdinal,peerMessage,peerBytes,peerAt,peerFormed,peerSelected,peerAssigned⟩ :=
    receipt_at setup seed scalar candidate current valid transcript .server (publicHandles .server) (counts .server)
      peerPosition peerReceipt peerFound peerRole slot peerSlot
  obtain ⟨ownerOrdinal,ownerMessage,ownerBytes,ownerAt,ownerFormed,_ownerSelected,ownerAssigned⟩ :=
    receipt_at setup seed scalar candidate current valid transcript .beacon (publicHandles .beacon) (counts .beacon)
      ownerPosition ownerReceipt ownerFound ownerRole slot ownerSlot
  have equal := valid.1.2 peerBytes ownerBytes slot peerAssigned ownerAssigned
  exact ⟨peerOrdinal,ownerOrdinal,peerMessage,ownerMessage,peerBytes,peerAt,ownerAt,peerFormed,equal ▸ ownerFormed,peerSelected⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt.receipt_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt.receipt_at
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt.same_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt.same_slot
