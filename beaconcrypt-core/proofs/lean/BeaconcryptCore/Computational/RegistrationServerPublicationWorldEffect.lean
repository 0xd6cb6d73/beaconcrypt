-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreement

/-! The actual native effect lens preserves the complete caller World and auxiliary coordinates. The source publication compiler imports this definition and retains its separate all-request, raw and signing correspondence obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler
variable {n : Nat} {Auxiliary : Type}

noncomputable def effect : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n)
    (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) := fun query before =>
  (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
    (PqxdhRecordLiftWorld.effects query).run before.world.1

end BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler
