-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativePlatformPublicCoinEmbedding (embed)
variable {n : Nat} {I KemSK ProviderState A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
local notation "oldBackend" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
local notation "newBackend" => RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider

/-- Each literal corrected request compiles through the shared selective World service with the same complete private state. -/
theorem query (request : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain) :
    simulateQ oldBackend (embed request) = newBackend request := by
  cases request with
  | inl request => simp only [embed, simulateQ_spec_query, RegistrationNativePlatformSelectiveEntropyBackend.handler]
  | inr coin =>
      apply StateT.ext
      intro before
      simp only [embed, RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal,
        simulateQ_spec_query, RegistrationNativePlatformSelectiveEntropyBackend.handler,
        RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
        RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect, StateT.run]
      rfl

/-- Every adaptive corrected tree retains exact replies, World effects and full selective private state under the explicit coin embedding. -/
theorem program (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A) :
    simulateQ oldBackend (simulateQ embed work) = simulateQ newBackend work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind request next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, query]
      congr 1
      funext reply
      exact ih reply

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding.program
