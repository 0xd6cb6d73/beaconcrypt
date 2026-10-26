-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborPublicClient
import BeaconcryptCore.Computational.CborInactiveFinish
import BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant

/-! The existing compiler invariant reconstructs each active Server pin from successful public creation records. Kernel merging changes only established kernels, so it preserves active pin selection and every inactive owner classification. No additional private read or pin invariant is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborLogPins
open PqxdhServerAuthExperiment PqxdhDeploymentCompile
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def pins (log : Log) : CborPublicClient.Pins := fun index => Prod.snd <$> log.owners[index]?

theorem active_pin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : PqxdhDeploymentCompileInvariant.Good setup codec copies native)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : native.owners[index]? = some owner)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (active : owner.beacon.phase = .initSent control prekey oneTime kem) :
    (pins copies.log index).getD 0#u64 = control.expected_server_binding.identity_key_id := by
  obtain ⟨pin, keyId, created, _, shape⟩ := good.owners index owner found
  simp only [active] at shape
  simp [pins, created, shape.1]

theorem selection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : PqxdhDeploymentCompileInvariant.Good setup codec copies native)
    (index : Nat) (raw : Pqxdh.Bytes) :
    CborProductionBoundary.normalizationSender (.inr (.finish index raw)) (merge copies native) =
      (pins copies.log index).getD 0#u64 ∨
    (∀ owner, (merge copies native).native.owners[index]? = some owner →
      ∀ control prekey oneTime kem, owner.beacon.phase ≠ .initSent control prekey oneTime kem) := by
  cases found : native.owners[index]?
  case some owner =>
    cases phase : owner.beacon.phase
    case initSent control prekey oneTime kem =>
      left
      cases kernel : copies.owners index <;>
        simpa [CborProductionBoundary.normalizationSender, merge, List.getElem?_mapIdx,
          found, mergeOwner, kernel, phase] using
          (active_pin setup codec copies native good index owner found control prekey oneTime kem phase).symm
    all_goals right
    all_goals simp_all [merge, List.getElem?_mapIdx, mergeOwner]
    all_goals cases kernel : copies.owners index
    all_goals simp_all
  simp [merge, List.getElem?_mapIdx, found]

end BeaconcryptCore.Computational.CborLogPins

/-- info: 'BeaconcryptCore.Computational.CborLogPins.active_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborLogPins.active_pin
/-- info: 'BeaconcryptCore.Computational.CborLogPins.selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborLogPins.selection
