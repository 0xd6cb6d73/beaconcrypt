-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceState
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects

/-! Concrete source interpretation of the mixed public client's side effects, with one World, pool, root memo and chronological receipt state. This layout connects the actual open Server/Beacon source lemmas to the public reference frontend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State M world effect kem routedKem)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Extra := RegistrationNativeReferenceInterpreter.State × List RegistrationSigningShared.Receipt
abbrev Private (n : Nat) (KemSK : Type) := RegistrationNativeKemReferenceWorld.Private n KemSK Extra

def toPrivate (before : State n KemSK) : Private n KemSK :=
  ⟨before.world, before.pool, (before.roots, before.receipts)⟩
def fromPrivate (before : Private n KemSK) : State n KemSK :=
  ⟨before.extra.1, before.world, before.pool, before.extra.2⟩

def close (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : M n KemSK Value) : StateT (State n KemSK) ProbComp Value :=
  fun before => simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar) (work.run before)

/-- The actual source interpretation of a World computation preserves every other private coordinate. -/
theorem close_world (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK) :
    (close setup seed scalar (world work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world := by
  simp only [close, world, StateT.run, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have coins : RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar ∘ₛ
      RegistrationNativePublicInterpreter.coins = QueryImpl.ofLift unifSpec ProbComp := rfl
  rw [coins, simulateQ_ofLift_eq_self]

/-- The source-private layout is an exact reassembly, including both receipt histories and the root memo. -/
theorem layout (before : State n KemSK) : fromPrivate (toPrivate before) = before := by
  cases before
  rfl

/-- Either syntactic selected-getter route has the identical real native KEM computation. -/
theorem routed_real (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selected : Bool)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    simulateQ (RegistrationNativePublicInterpreter.handler (n := n) setup wire route sign)
      (RegistrationNativePublicFrontend.liftLocal selected (.inr (.inr query))) = kem setup query := by
  rcases query with query | query | key
  · simp only [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route,
      simulateQ_spec_query, RegistrationNativePublicFrontend.liftRoutedKem,
      RegistrationNativePublicInterpreter.handler, routedKem]
  · simp only [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route,
      simulateQ_spec_query, RegistrationNativePublicFrontend.liftRoutedKem,
      RegistrationNativePublicInterpreter.handler, routedKem]
  · cases selected <;> simp only [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route,
      Bool.false_eq_true, ite_false, ite_true,
      simulateQ_spec_query, RegistrationNativePublicFrontend.liftRoutedKem,
      RegistrationNativePublicInterpreter.handler, routedKem]

/-- Actual real native KEM state agrees with the existing open source world and opaque pool interpretation. -/
theorem kem_source (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : State n KemSK) :
    Prod.map id toPrivate <$> (close setup seed scalar (kem setup query)).run before =
      (RegistrationNativeKemReferenceWorld.kem setup RegistrationNativePublicInterpreter.unavailable query).run (toPrivate before) := by
  cases query with
  | inl query =>
      cases query <;> simp [close, kem, RegistrationNativePublicInterpreter.unavailable,
        RegistrationNativeKemReferenceWorld.kem, RegistrationNativeKemInterface.source,
        PqxdhRecordLiftWorld.sampled, StateT.lift, StateT.run, StateT.monad_pure_def, StateT.pure, toPrivate]
  | inr query => cases query with
    | inl query =>
        change Prod.map id toPrivate <$> simulateQ
          (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
          ((kem setup (.inr (.inl query))).run before) = _
        simp only [kem, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp, simulateQ_map]
        change Prod.map id toPrivate <$> ((fun result => (result.1.1,
          { result.2 with pool := result.1.2 })) <$> (close setup seed scalar
          (world (PqxdhRecordLiftWorld.sampled
            ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.pool)))).run before) = _
        rw [close_world]
        simp only [RegistrationNativeKemReferenceWorld.kem, RegistrationNativeKemInterface.source,
          StateT.run, toPrivate, Functor.map_map, Prod.map, id_eq]
        have mapped := RegistrationNativeKemReferenceWorld.sampled_map
          ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.pool)
          (fun result => (result.1, ((), result.2))) before.world
        simp only [StateT.run] at mapped
        rw [mapped]
        simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
    | inr key =>
        change Prod.map id toPrivate <$> (close setup seed scalar (world
          (PqxdhRecordLiftWorld.sampled (simulateQ
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))))).run before = _
        rw [close_world, RegistrationNativeKemReferenceWorld.kem_encapsulation]
        simp only [Functor.map_map, toPrivate, Prod.map, id_eq]

end BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.close_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.close_world
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.layout
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.routed_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.routed_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.kem_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects.kem_source
