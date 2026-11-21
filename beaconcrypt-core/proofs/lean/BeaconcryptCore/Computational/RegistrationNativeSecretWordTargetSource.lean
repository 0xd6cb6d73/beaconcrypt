-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter

/-! The actual symbolic frontend and its concrete combined interpreter flatten to one typed native handler while retaining the entire frontend, ordinary World, flags and KEM pool/phase. Arbitrary outer protected-key replies may influence every continuation. Parsed-attempt facts follow from the executing controller rather than a real-SDK source substitution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeSecretWordMessage.State source × RegistrationNativeSecretWordInterpreter.State n KemSK

noncomputable def implementation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp) :=
  outer.mapStateTBase (RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider)

noncomputable def typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK source) ProbComp) :=
  ((implementation setup wire route sign input inside provider outer).mapStateTBase
    (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey)).flattenStateT

/-- Flattening retains the complete reached frontend and concrete private interpreter state. -/
theorem typed_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source) :
    (typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (implementation setup wire route sign input inside provider outer)
          ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
            selectedOwner selectedAccept publicPrekey query).run before.1)).run before.2 :=
  QueryImpl.flattenStateT_mapStateTBase_apply_run _ _ _ _ _

/-- The actual closed typed callback has the controller's parsed ordinal under arbitrary outer key-table replies. -/
theorem typed_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey query).run before)) :
    result.2.1.parsedAccepts = before.1.parsedAccepts + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  rw [typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have original : reached.1 ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset (implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  cases equal
  exact RegistrationNativeSecretWordTargetCounter.typed_counter setup checks wire sign selectedOwner selectedAccept publicPrekey
    query before.1 reached.1 original


/-- The complete concrete interpreted Word frontend is the literal original full native ledger under this typed source, with both complete poststates retained. -/
theorem run_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$>
      (simulateQ (implementation setup wire route sign input inside provider outer)
        (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
          serverKeyId bounds mode work before.1)).run before.2 =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) mode work before := by
  rw [RegistrationNativeFullCompiler.compile_run, RegistrationNativeSecretWordFrontend.run,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource.typed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource.typed_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource.typed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource.typed_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource.run_source
