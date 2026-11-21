-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainInterface
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly

/-! Evaluating the literal native interpreter's provider state gives the actual early candidate provider, including every pre-getter decapsulation, typed observation and private getter marker. All ordinary World and full program results remain in the exact state map. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativeSecretWordNativePlain (NativeFrame native realized)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def embed (candidate : MlKemSharedSecret)
    (before : NativeFrame n KemSK (RegistrationNativeSecretWordKemProvider.State KemSK)) :
    NativeFrame n KemSK (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) :=
  (before.1, RegistrationNativeSecretWordKemProvider.evalState candidate before.2)

/-- Every actual native callback retains its full World and realizes precisely the concrete early provider's reply, pool and phase. -/
theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : NativeFrame n KemSK (RegistrationNativeSecretWordKemProvider.State KemSK)) :
    Prod.map id (embed candidate) <$>
      (native setup wire route sign seed scalar target
        (realized candidate (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)) query).run before =
      (native setup wire route sign seed scalar target
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate) query).run (embed candidate before) := by
  rcases query with (prepare | (demand | common) | kem) | record
  case inl.inr.inr =>
    have source := congrArg (simulateQ RegistrationNativeKeyCompiler.coins)
      (RegistrationNativeSecretWordKemEarly.query_source setup.baseImpl setup.kem selected pairs publicKey challenge candidate kem before.2)
    have mapped := congrArg (fun work => (fun result => (result.1, (before.1, result.2))) <$> work) source
    simpa only [native, realized, embed, StateT.run, simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using mapped
  all_goals simp only [native, RegistrationNativeSecretWordNativePlain.ordinary, embed, StateT.run,
    StateT.lift, bind_pure_comp, map_pure, Functor.map_map, Prod.map_def, id_eq]

/-- The exact early-provider realization preserves every output and complete reached frame through arbitrary adaptive native work. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : NativeFrame n KemSK (RegistrationNativeSecretWordKemProvider.State KemSK)) :
    Prod.map id (embed candidate) <$>
      (simulateQ (native setup wire route sign seed scalar target
        (realized candidate (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))) work).run before =
      (simulateQ (native setup wire route sign seed scalar target
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate)) work).run (embed candidate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (embed candidate)
    (query_source setup wire route sign seed scalar target selected pairs publicKey challenge candidate) work before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider.program_source
