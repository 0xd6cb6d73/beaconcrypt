-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners

/-! Every original typed native command restores from the concrete symbolic frontend under the audited checked interpretation. Actual parsed-accept routing, raw record owner lookup, mandatory authentication, ordinary translated references and failure poststates all remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State input)
open RegistrationNativeSecretWordCheckedFrontend (native implementation)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- All actual public World effects have the same checked interpretation. -/
theorem effect (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ (native (KemSK := KemSK) source inside candidate input) (RegistrationNativePublicFrontend.effect query) =
      simulateQ (implementation source inside candidate input) (RegistrationNativeSecretWordFrontend.effect query) := by
  simp only [RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, RegistrationNativeSecretWordFrontend.effect,
    native, QueryImpl.compose, RegistrationNativeSecretWordCheckedFrontend.realization,
    simulateQ_spec_query, implementation]

/-- Actual raw record lookup uses the same stored physical owner index and preserves the complete frontend. -/
theorem record (source : RegistrationNativeMldsa.Source)
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    simulateQ (native (n := n) (KemSK := KemSK) hkdf inside candidate input)
      ((RegistrationNativePublicFrontend.record query).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (implementation hkdf inside candidate input)
          ((RegistrationNativeSecretWordFrontend.record query).run before) := by
  rcases query with query | ⟨index, query⟩
  · simp only [RegistrationNativePublicFrontend.record, RegistrationNativeSecretWordFrontend.record,
      StateT.run, simulateQ_map, simulateQ_spec_query, RegistrationNativeSecretWordCheckedFrontend.record,
      implementation, Functor.map_map]
    rfl
  · cases query <;>
      simp only [RegistrationNativePublicFrontend.record, RegistrationNativeSecretWordFrontend.record,
        StateT.run, State.eval]
    all_goals cases found : before.beacons[index]? <;>
      simp only [simulateQ_pure, map_pure, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeSecretWordCheckedFrontend.record, implementation, Functor.map_map]
    all_goals rfl

attribute [local irreducible] RegistrationNativePublicFrontend.handler RegistrationNativeSecretWordFrontend.handler

/-- Every actual original typed operation restores exactly, including malformed optional finish and pre-authentication parsed-attempt increment. -/
theorem query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before) := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler,
        StateT.run_lift, bind_pure_comp, simulateQ_map]
      rw [effect]
      simp only [Functor.map_map]
      rfl
  | inr query =>
      cases query with
      | create edPin mlPin keyId =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            RegistrationNativeSecretWordCheckedBirth.create setup source inside candidate seed scalar selectedOwner publicPrekey edPin mlPin keyId before
      | bundle index =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            RegistrationNativeSecretWordCheckedBirth.bundle setup source wire inside candidate seed scalar selectedOwner publicPrekey index before
      | accept packet =>
          simp only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler,
            StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
          simpa only [State.eval] using RegistrationNativeSecretWordCheckedFrontendServer.accept setup checks source.verify
            (decide (before.parsedAccepts = selectedAccept)) inside candidate seed scalar packet
            { before with parsedAccepts := before.parsedAccepts + 1 }
      | build handle application =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            RegistrationNativeSecretWordCheckedFrontendServer.build setup checks wire sign inside candidate seed scalar handle application before
      | finish index packet =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            RegistrationNativeSecretWordCheckedOwners.finish setup source inside candidate seed scalar index packet before
      | hmac key bytes =>
          simp only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler,
            StateT.run_pure, simulateQ_pure, map_pure]
          rfl
      | hash bytes =>
          simp only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler,
            StateT.run_lift, bind_pure_comp, simulateQ_map]
          rw [effect]
          simp only [Functor.map_map]
          rfl
      | serverSend keyId plaintext =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            record source setup.source inside candidate (input setup.joint setup.dh seed scalar) (.inl (.inl (plaintext, keyId))) before
      | serverRaw raw =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            record source setup.source inside candidate (input setup.joint setup.dh seed scalar) (.inl (.inr raw)) before
      | beaconSend index plaintext =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            record source setup.source inside candidate (input setup.joint setup.dh seed scalar) (.inr (index, .inl plaintext)) before
      | beaconRaw index raw =>
          simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativeSecretWordFrontend.handler] using
            record source setup.source inside candidate (input setup.joint setup.dh seed scalar) (.inr (index, .inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep.effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep.record
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep.query
