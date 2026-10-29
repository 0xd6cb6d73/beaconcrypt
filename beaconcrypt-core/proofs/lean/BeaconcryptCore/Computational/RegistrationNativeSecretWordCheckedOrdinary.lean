-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners

/-! Ordinary owners supply their own two prekey-DH coordinates before checked preparation. Literal realization commutes with that exact translation. Successful checked preparation retains the supplied descriptor name, including its opaque word, rather than assuming an inverse for arbitrary oracle replies. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeSecretWordMessage (Message eval literal input)
open RegistrationNativeSecretWordServerSource (realize)
open RegistrationNativeSecretWordChecked (implementation native preparation)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def original (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (OracleComp (RegistrationNativeSecretWordChecked.Spec n KemSK)) :=
  native setup.source inside candidate (input setup.joint setup.dh seed scalar) ∘ₛ
    RegistrationNativePublicOwners.ordinary setup localScalar

def symbolic (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (OracleComp (RegistrationNativeSecretWordChecked.Spec n KemSK)) :=
  implementation setup.source inside candidate (input setup.joint setup.dh seed scalar) ∘ₛ
    RegistrationNativeSecretWordOwners.ordinary setup localScalar

/-- The ordinary owner's real local-DH translation enters the word language with the exact same optional supplied descriptor. -/
theorem literal_materialize (setup : Setup base KemSK) (scalar : ScalarBytes)
    (message : RegistrationNativeRelatedFamily.Message) :
    RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar (literal message) =
      (RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message).map literal := by
  cases shape : message.third <;>
    simp only [RegistrationNativeSecretWordLocalMessage.materialize, RegistrationNativeLocalMessage.materialize,
      literal, shape, Option.map_some]
  rename_i peer
  cases first : setup.dh.dh scalar message.staticPeer <;>
    cases third : setup.dh.dh scalar peer <;> rfl

/-- Full local realization commutes with ordinary-owner materialization, without a premise about the prepared oracle's returned names. -/
theorem ordinary_realize (setup : Setup base KemSK) (scalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    realize (n := n) candidate ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar =
      RegistrationNativeSecretWordOwners.ordinary setup scalar ∘ₛ realize candidate := by
  funext query
  cases query with
  | inl message =>
      simp only [QueryImpl.compose, RegistrationNativePublicOwners.ordinary, realize,
        RegistrationNativeSecretWordInterface.prepare, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeSecretWordOwners.ordinary, literal_materialize]
      cases formed : RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message <;>
        simp only [Option.map_none, Option.map_some, simulateQ_pure, simulateQ_spec_query, realize,
          RegistrationNativeSecretWordInterface.prepare, map_pure]
  | inr query =>
      rcases query with (message | query) | query | query | key
      all_goals try cases query
      all_goals simp only [QueryImpl.compose, RegistrationNativePublicOwners.ordinary, realize,
        RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.common,
        RegistrationNativeSecretWordInterface.localKem, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeSecretWordOwners.ordinary]

/-- Concrete checked preparation preserves the actual local supplied name and evaluates precisely the retained KEM field, on every optional local-DH or root-input failure. -/
theorem preparation_source (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (seed : IdentitySeed) (selectedScalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed selectedScalar))
      (RegistrationNativePublicOwners.ordinary setup localScalar (.inl (eval candidate message))) =
      Option.map (eval candidate) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed selectedScalar))
          (RegistrationNativeSecretWordOwners.ordinary setup localScalar (.inl message)) := by
  have translated := RegistrationNativeSecretWordLocalMessage.eval_materialize setup.joint setup.dh localScalar candidate message
  cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh localScalar message with
  | none =>
      have old : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar (eval candidate message) = none := by
        simpa only [formed, Option.map_none] using translated.symm
      simp only [RegistrationNativePublicOwners.ordinary, RegistrationNativeSecretWordOwners.ordinary,
        old, formed, simulateQ_pure, map_pure, Option.map_none]
  | some supplied =>
      have old : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar (eval candidate message) = some (eval candidate supplied) := by
        simpa only [formed, Option.map_some] using translated.symm
      simp only [RegistrationNativePublicOwners.ordinary, RegistrationNativeSecretWordOwners.ordinary, old, formed,
        native, QueryImpl.apply_compose, simulateQ_spec_query, realize, RegistrationNativeSecretWordInterface.prepare,
        simulateQ_map, simulateQ_spec_query, implementation, preparation]
      have valid := RegistrationNativeSecretWordCheckedInput.valid_literal_eval setup.joint setup.dh seed selectedScalar candidate supplied
      cases left : input setup.joint setup.dh seed selectedScalar (literal (eval candidate supplied)) <;>
        cases right : input setup.joint setup.dh seed selectedScalar supplied <;>
        simp_all [RegistrationNativeSecretWordMessage.eval_literal]

/-- The actual ordinary Beacon root capability keeps its locally supplied returned descriptor and all public metadata under concrete checked word evaluation. -/
theorem beacon_client (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (seed : IdentitySeed) (selectedScalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (authenticated : beaconcrypt_core.registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared beaconcrypt_core.registration.AuthenticatedResponse) :
    simulateQ ((native (n := n) setup.source inside candidate (input setup.joint setup.dh seed selectedScalar) ∘ₛ
      RegistrationNativePublicOwners.ordinary setup localScalar) ∘ₛ RegistrationBeaconReferenceCompiler.prepare)
      (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending)) =
      RegistrationNativeSecretWordBeaconRoot.restore candidate <$>
        simulateQ ((implementation setup.source inside candidate (input setup.joint setup.dh seed selectedScalar) ∘ₛ
          RegistrationNativeSecretWordOwners.ordinary setup localScalar) ∘ₛ RegistrationNativeSecretWordInterface.prepare)
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending) := by
  simp only [RegistrationBeaconReferenceRoot.client, RegistrationNativeSecretWordBeaconRoot.client,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, QueryImpl.apply_compose,
    RegistrationBeaconReferenceCompiler.prepare, RegistrationNativeSecretWordInterface.prepare,
    simulateQ_spec_query]
  rw [← RegistrationNativeSecretWordBeaconRoot.message_eval candidate pending,
    preparation_source setup localScalar inside seed selectedScalar candidate]
  simp only [Functor.map_map]
  congr 1
  funext reply
  cases reply <;> rfl

/-- Arbitrary source continuations commute with local realization before the concrete checked interpreter runs. -/
theorem program_source (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :
    simulateQ (original setup localScalar inside candidate seed scalar) work =
      simulateQ (symbolic setup localScalar inside candidate seed scalar) (simulateQ (realize candidate) work) := by
  simp only [original, symbolic, native, QueryImpl.simulateQ_compose]
  rw [← QueryImpl.simulateQ_compose (realize candidate) (RegistrationNativePublicOwners.ordinary setup localScalar),
    ordinary_realize, QueryImpl.simulateQ_compose]

/-- Ordinary materialization forwards every actual environment callback unchanged. -/
theorem effects (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ (original setup localScalar inside candidate seed scalar)
        (simulateQ RegistrationBeaconReferenceCompiler.effect work) =
      simulateQ (symbolic setup localScalar inside candidate seed scalar)
        (simulateQ RegistrationNativeSecretWordInterface.effect work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
/-- The complete ordinary root client retains its actual supplied descriptor through subsequent continuations. -/
theorem client_compiled (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (authenticated : beaconcrypt_core.registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared beaconcrypt_core.registration.AuthenticatedResponse) :
    simulateQ (original (n := n) setup localScalar inside candidate seed scalar)
      (simulateQ RegistrationBeaconReferenceCompiler.prepare
        (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending))) =
      RegistrationNativeSecretWordBeaconRoot.restore candidate <$>
        simulateQ (symbolic setup localScalar inside candidate seed scalar)
          (simulateQ RegistrationNativeSecretWordInterface.prepare (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)) := by
  simpa only [original, symbolic, QueryImpl.simulateQ_compose] using
    beacon_client (n := n) setup localScalar inside seed scalar candidate authenticated pending

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.literal_materialize' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.literal_materialize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.ordinary_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.ordinary_realize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.preparation_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.beacon_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.beacon_client

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.client_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary.client_compiled
