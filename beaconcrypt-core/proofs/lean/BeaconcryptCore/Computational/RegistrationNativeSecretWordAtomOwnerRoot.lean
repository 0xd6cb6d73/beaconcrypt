-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter

/-! Successful actual selected and ordinary Beacon root preparation preserves the opaque KEM word of its same collected input. Ordinary DH materialization may change the returned descriptor name, but cannot change its KEM suffix. The actual source echo is proved rather than required of arbitrary oracle replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordTargetServerExecution (localImpl)
open RegistrationNativeSecretWordAtomOwnerGetter (withScalar)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

/-- Ordinary local DH substitution retains the exact opaque KEM suffix, including failed materialization. -/
theorem materialize_kem (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (message translated : Message)
    (formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message = some translated) :
    translated.kem = message.kem := by
  cases shape : message.third <;>
    simp only [RegistrationNativeSecretWordLocalMessage.materialize, shape] at formed
  all_goals try (cases formed; rfl)
  rename_i peer
  cases first : setup.dh.dh scalar message.staticPeer <;> cases third : setup.dh.dh scalar peer <;>
    simp only [first, third] at formed
  all_goals first
    | contradiction
    | (cases formed; rfl)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer false

private theorem plain_echo (message reference : Message) (before after : State n KemSK)
    (supported : (some reference, after) ∈ support ((implementation (.inl (.inl message))).run before)) : reference = message := by
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  rw [RegistrationNativeSecretWordInterpreter.prepare_run, mem_support_pure_iff] at native
  have returned : (input message).map (fun _ => message) = some reference := (congrArg Prod.fst native).symm
  cases realized : input message with
  | none => simp only [realized, Option.map_none, reduceCtorEq] at returned
  | some key => simpa only [realized, Option.map_some, Option.some.injEq] using returned.symm

/-- The actual local incoming root callback retains its KEM suffix even when an ordinary owner returns a translated descriptor. -/
theorem query_kem (scalar : Option PqxdhJointGapDh.ScalarBytes) (message reference : Message)
    (before after : State n KemSK)
    (supported : (some reference, after) ∈ support
      (((withScalar setup localImplementation scalar) (.inl message)).run before)) : reference.kem = message.kem := by
  cases scalar with
  | none =>
      have actual : (some reference, after) ∈ support ((implementation (.inl (.inl message))).run before) := by
        simpa only [withScalar, localImpl, QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal,
          simulateQ_spec_query] using supported
      exact congrArg Message.kem (plain_echo setup wire route sign input inside provider outer message reference before after actual)
  | some scalar =>
      simp only [withScalar, QueryImpl.compose, RegistrationNativeSecretWordOwners.ordinary] at supported
      cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message with
      | none => simp only [formed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
      | some translated =>
          have actual : (some reference, after) ∈ support ((implementation (.inl (.inl translated))).run before) := by
            simpa only [formed, simulateQ_spec_query, localImpl, QueryImpl.compose,
              RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query] using supported
          exact (congrArg Message.kem (plain_echo setup wire route sign input inside provider outer translated reference before after actual)).trans
            (materialize_kem setup scalar message translated formed)

/-- A successful actual root client keeps the atom or literal from the same successfully collected input on both owner paths. -/
theorem client_kem (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (withScalar setup localImplementation scalar)
        (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before)) :
    ready.reference.kem = pending.collected.kem := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    RegistrationNativeSecretWordInterface.prepare, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  cases referenceShape : result.1 with
  | none => simp only [referenceShape, Option.map_none] at equal; cases equal
  | some reference =>
      simp only [referenceShape, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
      obtain ⟨sameReady, _sameState⟩ := equal
      cases sameReady
      apply query_kem setup wire route sign input inside provider outer scalar
        (RegistrationNativeSecretWordBeaconRoot.message pending) reference before result.2
      simpa only [← referenceShape, Prod.mk.eta] using reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot.materialize_kem' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot.materialize_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot.query_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot.query_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot.client_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot.client_kem
