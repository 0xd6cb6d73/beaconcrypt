-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationSeedPublic

/-! The complete bound Server continuation runs the actual sequence-one raw record, actual response hash and ML signing, exact signature admission, dynamic signed-view encoder and native publication. It reads an independent seed only through the whole kernel it finally publishes. The thin program executes on a fixed placeholder; the private World supplies the genuine generated kernel at a hidden-slot installation. No signature, populated AD or publication decision is synthesized by a legacy codec. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationBoundPublication
open RegistrationWorldServerPublication (Result)
variable {Encoded : Type}

abbrev Spec := RegistrationRawSealBridge.Spec + RegistrationSigningShared.Spec

def rawLift : QueryImpl RegistrationRawSealBridge.Spec (OracleComp Spec) :=
  fun query => Spec.query (.inl query)

def signingLift : QueryImpl RegistrationSigningShared.Spec (OracleComp Spec) :=
  fun query => Spec.query (.inr query)

/-- Only the actual successful raw-record capability reaches response hashing and signing. -/
def after (encode : registration.SignedResponseView → core.option.Option Encoded)
    (record : RustM RegistrationServerRecordExecutor.Result) : OracleComp Spec (RustM (Result Encoded)) :=
  match record with
  | .ok (.Ok pending) => simulateQ signingLift (RegistrationWorldServerPublication.program encode pending)
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The real native first-record and publication controllers share one open primitive interface. -/
def program (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp Spec (RustM (Result Encoded)) := do
  let record ← simulateQ rawLift (simulateQ RegistrationRawSealBridge.nativeAdapter
    (RegistrationBoundKeySchedule.factored initial output))
  after encode record

/-- Every late failure retains its native result; only successful publication carries the replaced private kernel. -/
theorem after_map (kernel : ConcreteRatchetKernel)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (record : RustM RegistrationServerRecordExecutor.Result) :
    after encode (RegistrationKernelErasure.mapResult kernel record) =
      RegistrationPublicationKernelErasure.result kernel <$> after encode record := by
  cases record with
  | fail error => rfl
  | div => rfl
  | ok value =>
    cases value with
    | Err previous => rfl
    | Ok pending =>
      simp only [RegistrationKernelErasure.mapResult, RawCtxMaterialInterpretation.rust_map_ok,
        RegistrationKernelErasure.mapCore, after, RegistrationPublicationKernelErasure.program_map, simulateQ_map]

/-- The complete actual hash/sign/encode/publication phase has identical effects and decisions for every seed; only its published kernel changes. -/
theorem program_map (kernel₂ : ConcreteRatchetKernel)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed₁ seed₂ : PqxdhRecordLiftSeed.Seed)
    (kernelRun : PqxdhRecordLiftSeed.serverKernel seed₂ = .ok kernel₂) :
    program encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed₂) =
      RegistrationPublicationKernelErasure.result kernel₂ <$>
        program encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed₁) := by
  simp only [program, RegistrationSeedPublic.factored_raw_map initial material seed₁ seed₂ kernel₂ kernelRun,
    simulateQ_map, bind_map_left, map_bind]
  apply bind_congr
  intro record
  exact after_map kernel₂ encode record

def fixedSeed : PqxdhRecordLiftSeed.Seed :=
  (RegistrationBoundKeySchedule.zero, RegistrationBoundKeySchedule.zero)

/-- The public continuation has no private seed input and never supplies one to a primitive callback. -/
def thin (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material) :
    OracleComp Spec (RustM (Result Encoded)) :=
  program encode initial (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed)

/-- Actual private seed semantics are exactly the World Server kernel, applied only to a successful native publication. -/
theorem split (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    program encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      RegistrationPublicationKernelErasure.result (PqxdhRecordLiftWorld.kernel .server seed) <$>
        thin encode initial material :=
  program_map _ encode initial material fixedSeed seed (PqxdhRecordLiftWorld.kernel_exact .server seed)

/-- Public native publication output omits only the private whole kernel. -/
structure PublicResponse (Encoded : Type) where
  control : pqxdh.ServerState
  binding : session.SessionBinding
  encoded : Encoded

def publicResponse (published : registration.PublishedServerResponse Encoded) : PublicResponse Encoded :=
  ⟨published.control, published.binding, published.encoded⟩

def publicResult (result : RustM (Result Encoded)) :
    RustM (core.result.Result (PublicResponse Encoded) pqxdh.ServerState) :=
  RegistrationPublicationKernelErasure.mapOk publicResponse <$> result

private theorem public_replace (kernel : ConcreteRatchetKernel) (value : RustM (Result Encoded)) :
    publicResult (RegistrationPublicationKernelErasure.result kernel value) = publicResult value := by
  cases value with
  | fail error => rfl
  | div => rfl
  | ok value => cases value <;> rfl

/-- The entire actual public reply and all effects are independent of the generated chains at fixed position-one material. -/
theorem public_program (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    publicResult <$> program encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      publicResult <$> thin encode initial material := by
  rw [split, Functor.map_map]
  apply map_congr
  intro value
  exact public_replace _ value

/-- Every actual successful publication retains precisely the generated post-sequence-one World kernel, rather than a reset or caller-known kernel. -/
theorem published_kernel (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support
      (program encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed))) :
    published.kernel = PqxdhRecordLiftWorld.kernel .server seed := by
  rw [split] at supported
  obtain ⟨value, _possible, equal⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases value with
  | fail error => cases equal
  | div => cases equal
  | ok value =>
    cases value with
    | Err previous => cases equal
    | Ok original =>
      simp only [RegistrationPublicationKernelErasure.result, RawCtxMaterialInterpretation.rust_map_ok,
        RegistrationPublicationKernelErasure.mapOk, RustM.ok.injEq, core.result.Result.Ok.injEq] at equal
      cases equal
      rfl

end BeaconcryptCore.Computational.RegistrationBoundPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundPublication.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundPublication.after_map

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundPublication.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundPublication.program_map

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundPublication.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundPublication.split

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundPublication.public_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundPublication.public_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundPublication.published_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundPublication.published_kernel
