-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills

/-! Every locally evaluated encapsulation is charged when the source is scanned or resumed. Private service bounds remain unchanged, while the conservative uniform allowance adds the full primitive encapsulation bill for every permitted occurrence. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted
open PqxdhRegistrationJointKemEncapsulation PqxdhRegistrationJointKemCutBounds PqxdhRegistrationJointKemProgramBills
open PqxdhDynamicKemJointBounds (IsIdentityCreate IsDecapsulation IsUniform)
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

structure Bills (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qCreate qD qUniform : Nat) : Prop where
  creates : work.IsQueryBoundP (IsIdentityCreate (KemSK := KemSK)) qCreate
  decaps : work.IsQueryBoundP (IsDecapsulation (KemSK := KemSK)) qD
  uniform : work.IsQueryBoundP (IsUniform (KemSK := KemSK)) qUniform

/-- Local real encapsulation does not request a private signing, DH, key-creation or decapsulation capability; its actual random/base work remains in its uniform bill. -/
theorem encaps_private (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (request : PqxdhRegistrationJointKemCut.Request) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (actual setup (.inr request)).IsQueryBoundP (fun query => poolClass (KemSK := KemSK) query = kind) 0 :=
  PqxdhRegistrationJointOpenCosts.coins_nonuniform _ kind nonuniform

/-- The actual local encapsulation distribution pays its complete evaluated primitive/base uniform allowance. -/
theorem encaps_uniform (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (caps : KemCaps) (bounded : KemBound setup caps) (request : PqxdhRegistrationJointKemCut.Request) :
    (actual setup (.inr request)).IsQueryBoundP (IsUniform (KemSK := KemSK)) caps.encapsCost := by
  rw [actual, PqxdhLiveKemBirth.coins_class]
  simpa only [IsUniform, isQueryBoundP_true_iff] using
    PqxdhServerAuthSourceCosts.encaps_uniform setup caps bounded request.2

/-- Every interpreted source continuation keeps its all-reply private caps and pays each real encapsulation in addition to the conservative original native allowance. -/
theorem actual_bills (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (work : OracleComp (Spec KemSK) Result) (qCreate qD qUniform qEncap : Nat)
    (bills : Bounds work qCreate qD qUniform qEncap) :
    Bills (simulateQ (actual setup) work) qCreate qD (qUniform + caps.encapsCost * qEncap) := by
  constructor
  · simpa only [creates_class, Nat.zero_mul, Nat.add_zero] using
      actual_bound setup work (fun query => poolClass (KemSK := KemSK) query = .identityCreate)
        qCreate qEncap 0 (by simpa only [creates_class] using bills.creates) bills.encaps
        (fun request => encaps_private setup request .identityCreate (by decide))
  · simpa only [decaps_class, Nat.zero_mul, Nat.add_zero] using
      actual_bound setup work (fun query => poolClass (KemSK := KemSK) query = .decapsulate)
        qD qEncap 0 (by simpa only [decaps_class] using bills.decaps) bills.encaps
        (fun request => encaps_private setup request .decapsulate (by decide))
  · exact actual_bound setup work _ qUniform qEncap caps.encapsCost bills.uniform bills.encaps
      (encaps_uniform setup caps bounded)

/-- The exact executable prechallenge scan inherits every source request cap and the full allowance for all earlier public encapsulations. -/
theorem scan_bills (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (work : OracleComp (Spec KemSK) Result) (qCreate qD qUniform qEncap index : Nat)
    (bills : Bounds work qCreate qD qUniform qEncap) :
    Bills (PqxdhRegistrationJointKemCut.scan setup work index) qCreate qD (qUniform + caps.encapsCost * qEncap) := by
  constructor
  · simpa only [creates_class, Nat.zero_mul, Nat.add_zero] using
      scan_bound setup work index (fun query => poolClass (KemSK := KemSK) query = .identityCreate)
        qCreate qEncap 0 (by simpa only [creates_class] using bills.creates) bills.encaps
        (fun request => encaps_private setup request .identityCreate (by decide))
  · simpa only [decaps_class, Nat.zero_mul, Nat.add_zero] using
      scan_bound setup work index (fun query => poolClass (KemSK := KemSK) query = .decapsulate)
        qD qEncap 0 (by simpa only [decaps_class] using bills.decaps) bills.encaps
        (fun request => encaps_private setup request .decapsulate (by decide))
  · exact scan_bound setup work index _ qUniform qEncap caps.encapsCost bills.uniform bills.encaps
      (encaps_uniform setup caps bounded)

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.encaps_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.encaps_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.encaps_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.encaps_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.actual_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.actual_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.scan_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted.scan_bills
