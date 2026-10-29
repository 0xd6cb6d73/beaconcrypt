-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence

/-! The finite finishing correspondence lifts to the actual owner roster. Only the selected owner's private prekey scalar and the existing record-request analysis ledger are erased; every other owner and the complete reached native World remain in the compared result. Pending coherence is recovered from the actual roster invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRoster
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner restoreOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def dummy : PqxdhJointGapDh.ScalarBytes := List.Vector.replicate 32 0

def eraseRoster (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source) :=
  match owners[index]? with
  | none => owners
  | some owner => owners.set index (restoreOwner dummy (eraseOwner owner))

def view (index : Nat)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.State source) ×
      EnvState RegistrationServerRoleBackend.State) :=
  ((result.1.1, eraseRoster index result.1.2), RegistrationBeaconReferenceNativeRecord.erase result.2)

def rebuild (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State) ×
      RegistrationNativeExperiment.State n KemSK source) :=
  (((result.1.1.1, owners.set index (restoreOwner dummy result.1.1.2)),
    result.1.2), result.2)

private theorem set_twice {Element : Type} (items : List Element) (index : Nat) (first second : Element) :
    (items.set index first).set index second = items.set index second := by
  induction items generalizing index with
  | nil => rfl
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          change head :: (rest.set index first).set index second = head :: rest.set index second
          rw [ih]

/-- Actual roster lookup supplies pending coherence, and the source finish preserves all unselected owners, failures and World effects under the selected public view. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source)
    (owners : RegistrationNativeBeaconFrontend.State source) (index : Nat) (owner : Owner source)
    (found : owners[index]? = some owner) (coherent : RegistrationNativeBeaconCoherence.Holds owners)
    (packet : Option registration.ResponsePacket) (env : EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationBeaconReferenceNativeInterpreter.State n KemSK source)
    (sameScalar : owner.prekeyScalar = scalar) (erased : Std.Array U8 357#usize) :
    rebuild index owners <$>
      (RegistrationBeaconReferenceNativeCompletion.drop <$>
        (simulateQ (RegistrationBeaconReferenceNativeInterpreter.implementation setup checks wire representation created scalar credential)
          (((RegistrationBeaconReferenceFinish.finish setup source packet :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
              (Auxiliary := RegistrationServerRoleBackend.State) source (RustM (Option Pqxdh.Bytes))).run (eraseOwner owner)).run
                (RegistrationBeaconReferenceNativeRecord.erase env))).run before) =
      Prod.map (view index) id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (((RegistrationNativeBeaconFrontend.finish setup source wire index packet).run owners).run env)).run before.2.2 := by
  have finite := RegistrationBeaconReferenceNativeFinish.finish_source setup checks wire representation created scalar credential
    owner packet env before sameScalar
    (fun pending oneTime phase => RegistrationNativeBeaconCoherence.pending owners coherent index owner found pending oneTime phase)
    erased
  have mapped := congrArg (fun work => rebuild index owners <$> work) finite
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [RegistrationBeaconReferenceNativeOwner.finish_source setup wire index packet owners owner found]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  simpa only [Functor.map_map, rebuild, view, RegistrationBeaconReferenceNativeContinuation.view,
    Prod.map_def, id_eq, eraseRoster, List.getElem?_set_self within, set_twice] using mapped

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRoster.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRoster.finish_source
