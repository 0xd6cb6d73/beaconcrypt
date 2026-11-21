-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerProviderCollect
import BeaconcryptCore.Computational.RegistrationServerProviderStage

/-! The generic primitive engine instantiates the actual mutable-Env Server collector under the same provider. Its added cache frame is unused, while the real provider World cache and all reached Env/pool/phase fields remain exact. Private preparation memo updates are handled separately by the actual accept wrapper. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderLocal (lower primitive)
open RegistrationServerProviderCache (Local visit native)
open RegistrationBeaconReferenceGenericStage (liftCache)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)

noncomputable def plainStage (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (Local n KemSK ProviderState) ProbComp (RustM (Option RegistrationServerReferenceRoot.Ready)) := do
  let input ← lower (localImpl setup wire route sign seed scalar provider selected)
    (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)
  match input with
  | none => pure (.ok none)
  | some input => StateT.lift (simulateQ (RegistrationServerReferenceSourceClient.prepare setup.source setup.joint setup.dh seed scalar)
      (RegistrationServerReferenceRoot.client authenticated.binding input))

/-- The generic engine reference phase is the actual lowered collector and literal source preparation, with only its unused extra cache projected. -/
theorem reference_project (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (RegistrationServerProviderStage.referenceStage setup.source setup.joint setup.dh setup.serverDomain seed scalar
      (primitive setup checks wire route sign seed scalar provider selected)
      (fun point => liftCache (visit setup checks wire route sign seed scalar provider selected point)) packet authenticated).run before =
      (plainStage setup checks wire route sign seed scalar provider selected packet authenticated).run before.1 := by
  simp only [RegistrationServerProviderStage.referenceStage, plainStage, StateT.run_bind, map_bind]
  rw [← RegistrationServerProviderCollect.collect_project setup checks wire route sign seed scalar provider selected packet authenticated before, bind_map_left]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => simp only [StateT.run_pure, map_pure]; rfl
  | some input =>
      simp only [Prod.map_def, id_eq, StateT.run_lift, bind_pure_comp, Functor.map_map]

/-- The actual collector plus source root capability restores the complete native agreement under the same arbitrary provider, retaining its whole current World and environment. -/
theorem reference_native (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : Local n KemSK ProviderState) (cache : CtxRomAuth.CtxRO.QueryCache) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)) id <$>
      (plainStage setup checks wire route sign seed scalar provider selected packet authenticated).run before =
      (simulateQ (native setup checks wire route sign seed scalar provider selected)
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before := by
  have source := RegistrationServerProviderStage.reference_native setup.source setup.hmac correct setup.joint setup.dh setup.serverDomain
    setup.secretOfSeed setup.wiring seed scalar (primitive setup checks wire route sign seed scalar provider selected)
    (fun point => liftCache (visit setup checks wire route sign seed scalar provider selected point)) control packet authenticated (before, cache)
  have mapped := congrArg (fun distribution => Prod.map id Prod.fst <$> distribution) source
  rw [RegistrationServerProviderCache.native_program] at mapped
  have prepared := congrArg (fun distribution => Prod.map
    (RegistrationServerReferenceSourceClient.restore (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)) id <$> distribution)
    (reference_project setup checks wire route sign seed scalar provider selected packet authenticated (before, cache))
  simp only [Functor.map_map, Prod.map_def, id_eq] at mapped prepared ⊢
  exact prepared.symm.trans mapped

end BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage.reference_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage.reference_project
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage.reference_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage.reference_native
