-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCreateCosts
import BeaconcryptCore.Computational.RegistrationNativeBundleCosts
import BeaconcryptCore.Computational.RegistrationNativeFinishCosts
import BeaconcryptCore.Computational.RegistrationNativeAcceptCosts
import BeaconcryptCore.Computational.RegistrationNativeBuildCosts

/-! The actual raw native frontend has a literal callback allowance for every class. Malformed parser inputs and every reached failure retain their own prefix costs. The six implemented classes are derived from their actual typed source programs; all remaining admitted frontend classes cost zero. Only primitive generation, signing and indexed-provider execution receipts are inputs. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeConcreteFrame
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open RegistrationNativeWeightedContext (map_bound)
attribute [local irreducible] RegistrationNativePublicFrontend.handler
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

def allowance (qGenerate qSign qKem : Nat) (index : Fin 14) (kind : EffectKind) :=
  if index = 1 then RegistrationNativeCreateCosts.createBill qGenerate qKem kind
  else if index = 2 then RegistrationNativeBundleCosts.bundleBill qSign kind
  else if index = 3 then RegistrationNativeAcceptCosts.bill qKem kind
  else if index = 4 then RegistrationNativeBuildCosts.bill qSign kind
  else if index = 5 then RegistrationNativeFinishCosts.finishBill qKem kind
  else 0

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
  (selectedOwner selectedAccept qGenerate qSign qKem : Nat)
  (generation : source.generate.IsTotalQueryBound qGenerate)
  (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
  (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)

include generation signing in
set_option backward.isDefEq.respectTransparency false in
theorem frontend_bound (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : RegistrationNativePublicFrontend.State source) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill (n := n) qSign qKem query kind)
      ((RegistrationNativeHiddenEnvironmentRaw.frontend setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr query.val)).run before)
      (allowance qGenerate qSign qKem (RegistrationNativeInterface.queryClass (.inl (.inr query.val))) kind) := by
  rcases query with ⟨command, permitted⟩
  cases command with
  | create edPin mlPin keyId =>
      simp only [RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter]
      cases PqxdhDeploymentInterface.parsePin edPin <;> cases RegistrationNativeWire.parseMldsaPin mlPin
      all_goals simp only [simulateQ_pure, StateT.run_pure, simulateQ_map, simulateQ_spec_query, StateT.run_map]
      all_goals first
        | trivial
        | exact map_bound _ _ _ _ (RegistrationNativeCreateCosts.frontend_bound setup checks wire source _ selectedOwner selectedAccept
            (setup.dh.publicKey scalar) qGenerate qSign qKem generation _ _ keyId before kind)
  | bundle owner =>
      simp only [RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
        simulateQ_map, simulateQ_spec_query, StateT.run_map]
      exact map_bound _ _ _ _ (RegistrationNativeBundleCosts.frontend_bound setup checks wire source _ selectedOwner selectedAccept
        (setup.dh.publicKey scalar) qSign qKem signing owner before kind)
  | accept bytes =>
      simp only [RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter]
      cases RegistrationNativeWire.readInit wire bytes with
      | none => simp only [simulateQ_pure, StateT.run_pure]; trivial
      | some packet =>
          simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
          exact map_bound _ _ (Prod.map RegistrationNativeRawAdapter.resultOption id) _ (RegistrationNativeAcceptCosts.frontend_bound setup checks wire source _ selectedOwner selectedAccept qSign qKem
            (setup.dh.publicKey scalar) packet before kind)
  | build handle application =>
      simp only [RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
        simulateQ_map, simulateQ_spec_query, StateT.run_map]
      exact map_bound _ _ _ _ (RegistrationNativeBuildCosts.frontend_bound setup checks wire source _ selectedOwner selectedAccept qSign qKem
        (setup.dh.publicKey scalar) (RegistrationNativePrimitiveCosts.signing_bound source qSign signing credential) handle _ before kind)
  | finish owner bytes =>
      simp only [RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
        simulateQ_map, simulateQ_spec_query, StateT.run_map]
      exact map_bound _ _ _ _ (RegistrationNativeFinishCosts.frontend_bound setup checks wire source _ selectedOwner selectedAccept
        (setup.dh.publicKey scalar) _ owner before qSign qKem kind)
  | hmac key bytes =>
      simp only [RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
        simulateQ_spec_query, RegistrationNativePublicFrontend.handler, StateT.run_pure]
      trivial
  | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend owner plaintext | beaconRaw owner raw => exact permitted.elim

include generation signing kem in
theorem frame : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider
    selectedOwner selectedAccept (allowance qGenerate qSign qKem) := by
  intro credential
  constructor
  · trivial
  · intro query before kind
    exact RegistrationNativeRestrictedCosts.callback_bound (n := n) setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept qSign qKem signing kem query before _ kind
      (frontend_bound (n := n) setup checks wire source scalar selectedOwner selectedAccept qGenerate qSign qKem generation signing
        credential query before.1 kind)

end BeaconcryptCore.Computational.RegistrationNativeConcreteFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteFrame.frontend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteFrame.frontend_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteFrame.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteFrame.frame
