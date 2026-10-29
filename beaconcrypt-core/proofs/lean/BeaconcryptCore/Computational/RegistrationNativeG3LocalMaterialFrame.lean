-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys

/-! Every actual callback outside preparation and material demand retains the selected material cache without reading it. Replacing that cache on both sides commutes with actual publication, World effects, routed KEM work and record commands; the complete semantic World and both receipt coordinates remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3LocalKeys (State actual)
variable {n : Nat} {ι KemSK ProviderState Reader Response : Type} {base : OracleSpec ι}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    StateT.lift work before = (fun reply => (reply, before)) <$> work := by
  simp only [StateT.lift, bind_pure_comp]

abbrev Cache (n : Nat) := (RegistrationNativePairedServices.MaterialSpec n).QueryCache

def put (before : State n KemSK ProviderState) (cache : Cache n) : State n KemSK ProviderState :=
  (({ before.1.1 with keys := { before.1.1.keys with materials := cache } }, before.1.2), before.2)

def Ordinary : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr (.inl (.inl _))) => False
  | _ => True

/-- Cache replacement changes only selected material cells and is idempotent under a later replacement. -/
theorem put_put (before : State n KemSK ProviderState) (first second : Cache n) :
    put (put before first) second = put before second := rfl

/-- Actual ordinary callbacks commute with replacing the selected material cache while retaining every other reached private and World field. -/
theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (quiet : Ordinary (KemSK := KemSK) query)
    (before : State n KemSK ProviderState) (cache : Cache n) :
    (actual setup codec route wire sign seed scalar candidate provider query).run (put before cache) =
      Prod.map id (fun after => put after cache) <$>
        (actual setup codec route wire sign seed scalar candidate provider query).run before := by
  rcases query with (message | (message | common) | kem) | record
  · exact quiet.elim
  · exact quiet.elim
  · rcases common with publication | effect
    all_goals simp only [state_map_apply, lift_apply, actual, RegistrationNativeG3LocalKeys.execute,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
      RegistrationNativeHiddenInterpreter.effect, StateT.run, simulateQ_map, Functor.map_map, Prod.map_def, id_eq, put]
  · simp only [state_map_apply, actual, RegistrationNativeG3LocalKeys.execute,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.routed,
      StateT.run, simulateQ_map, Functor.map_map, Prod.map_def, id_eq, put]
  · simp only [state_map_apply, lift_apply, actual, RegistrationNativeG3LocalKeys.execute,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, StateT.run, simulateQ_map, Functor.map_map, Prod.map_def, id_eq, put]
end BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame.put_put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame.put_put
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame.query
