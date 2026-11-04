-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
/-! Reify an actual returned ordinary-controller kernel into the source object's generated RatchetManager constructor. Only that kernel changes; the established control, full binding and assigned identifier persist. This is the returned-object component of the ordinary wrapper correspondence, not a theorem about the complete SDK call by itself. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel
open BeaconcryptCore.Computational
open AdapterPublicWrapperState
variable [material : PublicWrapperPlatform.Material]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source} {KemSK A : Type}

def install (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    RustM beaconcrypt_public_wrapper.beacon.Beacon := do
  let manager ← beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel kernel
  .ok {self with state := .Established control binding manager}

def returned (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (result : RustM (ratchet.concrete.ConcreteRatchetKernel ×A)) :
    RustM (A ×beaconcrypt_public_wrapper.beacon.Beacon) := do
  let next ← result
  let stored ← install self control binding next.1
  .ok (next.2,stored)

theorem install_exact (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    install self control binding kernel=.ok {self with state := .Established control binding ⟨⟨some kernel⟩⟩} := by rfl

theorem returned_exact (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (reply : A) :
    returned self control binding (.ok (kernel,reply))=
      .ok (reply,{self with state := .Established control binding ⟨⟨some kernel⟩⟩}) := by rfl

theorem returned_fail (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (error : Aeneas.Std.Error) :
    returned (A := A) self control binding (.fail error)=.fail error := by rfl

theorem returned_div (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) :
    returned (A := A) self control binding .div=.div := by rfl

theorem material_preserved (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : Beacon view joint pool self owner world)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (manager : beaconcrypt_public_wrapper.ratchet.RatchetManager)
    (stored : self.state=.Established control binding manager)
    (completed : RegistrationBeaconSeed.PublicCompleted)
    (established : owner.phase=.established completed) (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    Beacon view joint pool {self with state := .Established control binding ⟨⟨some kernel⟩⟩} owner
      (some (.established ⟨binding.assigned_key_id,control,binding.associated_data⟩ kernel)) := by
  have phase := related.phase
  simp only [Phase,stored,established] at phase
  refine ⟨related.identityPublic,related.identitySecret,related.mldsa,related.pin,
    related.serverPublic,related.identifier,?_⟩
  simp only [Phase,established]
  exact ⟨phase.1,phase.2.1,kernel,rfl,rfl⟩

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.install_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.install_exact
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.returned_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.returned_exact
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.returned_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.returned_fail
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.returned_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.returned_div
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.material_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel.material_preserved
