-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerProviderPrefix

/-! Generic actual Server source preparation permits an arbitrary concrete primitive backend, including the same total candidate-KEM provider used by its reference client. Source restoration keeps the complete auxiliary state and shared cache on every prefix outcome. No real-KEM interpretation or supplied whole-prefix equality is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerProviderStage
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding SourceWiring)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhSecretInputKdf (HmacSha512)
variable {Auxiliary : Type}
abbrev Local (Auxiliary : Type) := RawCtxSharedPrimitive.SharedState Auxiliary

noncomputable def stage (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (Local Auxiliary) ProbComp (RustM agreement.AgreementEffect) := do
  let collected ← simulateQ (PqxdhServerStaticDhSource.prefixImpl domain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationAgreementShared.implementation source primitive)) visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match collected with
  | none => pure (.ok (.Rejected .None))
  | some input => StateT.lift (simulateQ
      (RegistrationServerReferenceSourceClient.consumer source hmac joint dh seed scalar)
      (RegistrationRelatedRoot.client authenticated.binding input))

noncomputable def referenceStage (source : FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (Local Auxiliary) ProbComp (RustM (Option RegistrationServerReferenceRoot.Ready)) := do
  let collected ← simulateQ (PqxdhServerStaticDhSource.prefixImpl domain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationAgreementShared.implementation source primitive)) visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match collected with
  | none => pure (.ok none)
  | some input => StateT.lift (simulateQ
      (RegistrationServerReferenceSourceClient.prepare source joint dh seed scalar)
      (RegistrationServerReferenceRoot.client authenticated.binding input))

noncomputable def familyStage (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :=
  RegistrationRelatedRoot.stage domain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted (RegistrationAgreementShared.implementation source primitive)))
    (fun point => RegistrationRootStage.lift (visit point))
    (RegistrationServerRootCompiler.family hmac joint dh seed scalar) RegistrationAgreementFinish.quiet packet authenticated

/-- Literal private source restoration of the actual reference capability retains every current primitive and provider field. -/
theorem reference_stage (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Local Auxiliary) :
    Prod.map (RegistrationServerReferenceSourceClient.restore (RegistrationServerReferenceSourceClient.roots source joint dh seed scalar)) id <$>
      (referenceStage source joint dh domain seed scalar primitive visit packet authenticated).run before =
      (stage source hmac joint dh domain seed scalar primitive visit packet authenticated).run before := by
  simp only [referenceStage, stage, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => rfl
  | some input =>
      simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]
      have same := congrArg (fun distribution => (fun output => (output, current)) <$> distribution)
        (RegistrationServerReferenceSourceClient.client source hmac joint dh seed scalar authenticated.binding input)
      simpa only [Functor.map_map, Prod.map_def, id_eq] using same

/-- The actual real-family stage drops only private family instrumentation and preserves the entire supplied primitive state and cache. -/
theorem stage_value (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : PqxdhServerRelatedRootConsumer.State (Local Auxiliary)) :
    Prod.map id Prod.snd <$> (familyStage source hmac joint dh domain seed scalar primitive visit packet authenticated).run before =
      (stage source hmac joint dh domain seed scalar primitive visit packet authenticated).run before.2 := by
  simp only [familyStage, RegistrationRelatedRoot.stage, stage, StateT.run_bind, map_bind]
  rw [← RegistrationServerProviderPrefix.prefix_program joint domain (RegistrationAgreementShared.implementation source primitive) visit
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) before, bind_map_left]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => simp only [StateT.run_pure, map_pure]; rfl
  | some input =>
      rw [RegistrationServerProviderPrefix.consumer_program source hmac correct joint dh seed scalar]
      simp only [Prod.map_def, id_eq, StateT.run_lift, bind_pure_comp]

/-- An arbitrary concrete source primitive backend gives the actual extracted native Server agreement, including optional rejection and the populated authentication binding. -/
theorem stage_native (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : Local Auxiliary) :
    (stage source hmac joint dh domain seed scalar primitive visit packet authenticated).run before =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed (RegistrationAgreementShared.implementation source primitive) visit)
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before := by
  rw [← stage_value source hmac correct joint dh domain seed scalar primitive visit packet authenticated (PqxdhJointDhExtractFamily.empty, before)]
  exact RegistrationRootStage.stage_native source hmac correct joint dh domain secretOfSeed wiring seed scalar primitive visit control packet authenticated _

/-- Actual root-free reference preparation restores the complete native agreement for the same arbitrary provider, without a supplied prefix simulation equation. -/
theorem reference_native (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (Local Auxiliary) ProbComp Unit)
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : Local Auxiliary) :
    Prod.map (RegistrationServerReferenceSourceClient.restore (RegistrationServerReferenceSourceClient.roots source joint dh seed scalar)) id <$>
      (referenceStage source joint dh domain seed scalar primitive visit packet authenticated).run before =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed (RegistrationAgreementShared.implementation source primitive) visit)
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before := by
  rw [reference_stage, stage_native source hmac correct joint dh domain secretOfSeed wiring]

end BeaconcryptCore.Computational.RegistrationServerProviderStage
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderStage.reference_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderStage.reference_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderStage.stage_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderStage.stage_value
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderStage.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderStage.stage_native
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderStage.reference_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderStage.reference_native
