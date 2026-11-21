-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedConstruct

/-! Actual generated native startup with an independent private Server seed. Runtime initialization and the original counted dummy constructor draw remain before ML generation and pin initialization; all optional source failures are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedStart
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeExperiment (Initial)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def finish (source : RegistrationNativeMldsa.Source)
    (constructed : (Option (PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) × Unit) × PqxdhRecordLiftWorld.State n) :
    ProbComp (Option (Initial n KemSK source)) := do
  match constructed.1.1 with
  | none => pure none
  | some created =>
      let generated ← (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)).run constructed.2
      match generated.1 with
      | none => pure none
      | some credential =>
          let initialized ← (RegistrationWorldServerFrontend.start created credential.publicKey
            RegistrationServerRoleBackend.empty).run generated.2
          match initialized.1 with
          | .ok (.Some native) => pure (some ⟨created, credential,
              ⟨RegistrationServerFrontendCompiler.erase native, [], PqxdhLiveKemBirth.empty, 0⟩⟩)
          | _ => pure none

noncomputable def start (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) : ProbComp (Option (Initial n KemSK source)) := do
  let constructed ← (PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := Std.Array Std.U8 151#usize) setup.joint ensureInit identityIndex serverKeyId none).run ())).run
      (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n)
  finish source (RegistrationNativeSeedConstruct.replace setup.joint identityIndex serverKeyId seed constructed.1, constructed.2)

/-- The complete actual generated native startup has the same law with an early independent private Server seed, retaining all original counted dummy draws and failures. -/
theorem eager (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId =ᵈ
      (do let seed ← PqxdhJointIdentity.sampleSeed
          start setup source ensureInit identityIndex serverKeyId seed) := by
  exact RegistrationNativeSeedConstruct.eager setup.joint ensureInit identityIndex serverKeyId
    PqxdhRecordLiftWorld.initial (fun value world => finish source (value, world))

end BeaconcryptCore.Computational.RegistrationNativeSeedStart

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedStart.eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedStart.eager
