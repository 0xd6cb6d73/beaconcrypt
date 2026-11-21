-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceClient
import BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource

/-! Exact post-authentication native Server agreement via the public root-reference preparation. The actual source prefix and every failed optional callback retain the complete local World; only the private family history and redundant outer cache are erased. An open-KEM collector can connect by its separate actual-prefix source law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerRootCompiler (Local Shared)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def legacy (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) : QueryImpl PqxdhJointDhExtractRoot.RootSpec ProbComp :=
  RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar ∘ₛ
    RegistrationNativeRelatedRoot.legacy

private theorem coins (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : ProbComp Value) :
    simulateQ (legacy setup seed scalar) (simulateQ RegistrationServerRootCompiler.coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : legacy setup seed scalar ∘ₛ RegistrationServerRootCompiler.coins =
      QueryImpl.ofLift unifSpec ProbComp := by
    funext query
    simp only [legacy, QueryImpl.compose, RegistrationServerRootCompiler.coins,
      RegistrationNativeRelatedRoot.legacy, simulateQ_spec_query, RegistrationNativeSourceRoot.handler]
    rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- The complete native prefix is recovered from the actual old source compiler, without a whole-prefix simulation premise. -/
theorem collect (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Shared n) :
    Prod.map id Prod.fst <$> simulateQ (legacy setup seed scalar)
        ((RegistrationServerReferencePrefixSource.collect setup checks packet authenticated).run before) =
      (simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run before.1 := by
  have projected := congrArg (simulateQ (legacy setup seed scalar))
    (RegistrationServerReferencePrefixSource.collect_project setup checks packet authenticated before)
  rw [simulateQ_map, coins] at projected
  exact projected

private theorem consume {Result : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp PqxdhServerRelatedRootConsumer.Spec Result) (before : Shared n) :
    simulateQ (legacy setup seed scalar)
        ((simulateQ RegistrationServerRootCompiler.consumer work).run before) =
      (fun output => (output, before)) <$>
        simulateQ (RegistrationServerReferenceSourceClient.consumer setup.source setup.hmac setup.joint setup.dh seed scalar) work := by
  induction work using OracleComp.inductionOn with
  | pure output => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases query with
      | inl query =>
          simp only [RegistrationServerRootCompiler.consumer, StateT.run, simulateQ_map, simulateQ_spec_query, map_bind, bind_map_left,
            RegistrationServerReferenceSourceClient.consumer]
          apply congrArg (fun continuation => legacy setup seed scalar query >>= continuation)
          funext reply
          exact ih reply
      | inr query =>
          simp only [RegistrationServerRootCompiler.consumer, StateT.run_pure, pure_bind,
            simulateQ_pure, RegistrationServerReferenceSourceClient.consumer]
          exact ih ()

noncomputable def stage (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) : StateT (Local n) ProbComp (RustM agreement.AgreementEffect) := do
  let collected ← simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match collected with
  | none => pure (.ok (.Rejected .None))
  | some input =>
      StateT.lift (simulateQ
        (RegistrationServerReferenceSourceClient.consumer setup.source setup.hmac setup.joint setup.dh seed scalar)
        (RegistrationRelatedRoot.client authenticated.binding input))

/-- Private source interpretation of the actual public reference capability preparation. -/
noncomputable def referenceStage (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (Local n) ProbComp (RustM (Option RegistrationServerReferenceRoot.Ready)) := do
  let collected ← simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match collected with
  | none => pure (.ok none)
  | some input => StateT.lift (simulateQ
      (RegistrationServerReferenceSourceClient.prepare setup.source setup.joint setup.dh seed scalar)
      (RegistrationServerReferenceRoot.client authenticated.binding input))

/-- Restoring the public reference capability retains the complete actual native prefix poststate. -/
theorem reference_stage (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Local n) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
        (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)) id <$>
        (referenceStage setup checks seed scalar packet authenticated).run before =
      (stage setup checks seed scalar packet authenticated).run before := by
  simp only [referenceStage, stage, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => rfl
  | some input =>
      simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]
      have same := congrArg (fun distribution => (fun output => (output, current)) <$> distribution)
        (RegistrationServerReferenceSourceClient.client setup.source setup.hmac setup.joint setup.dh
          seed scalar authenticated.binding input)
      simpa only [Functor.map_map, Prod.map, id_eq] using same

set_option maxHeartbeats 1000000 in
/-- Root erasure preserves the actual complete optional source stage and every prefix poststate. -/
theorem stage_value (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Shared n) :
    Prod.map id Prod.fst <$> simulateQ (legacy setup seed scalar)
        ((RegistrationServerRootCompiler.stage setup checks setup.serverDomain packet authenticated).run before) =
      (stage setup checks seed scalar packet authenticated).run before.1 := by
  simp only [RegistrationServerRootCompiler.stage, stage, StateT.run_bind, simulateQ_bind, map_bind]
  change (do
    let collected ← simulateQ (legacy setup seed scalar)
      ((RegistrationServerReferencePrefixSource.collect setup checks packet authenticated).run before)
    Prod.map id Prod.fst <$>
      simulateQ (legacy setup seed scalar)
        ((match collected.1 with
        | none => (pure (RustM.ok (agreement.AgreementEffect.Rejected .None)) :
            StateT (Shared n) (OracleComp PqxdhJointDhExtractRoot.RootSpec) (RustM agreement.AgreementEffect))
        | some input => simulateQ RegistrationServerRootCompiler.consumer (RegistrationRelatedRoot.client authenticated.binding input)).run collected.2)) = _
  rw [← collect setup checks seed scalar packet authenticated before, bind_map_left]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => simp only [StateT.run_pure, simulateQ_pure, map_pure]; rfl
  | some input =>
      rw [consume]
      simp only [Functor.map_map, Prod.map, id_eq, StateT.run_lift, bind_pure_comp]

set_option maxHeartbeats 1000000 in
/-- The reconstructed stage is the literal native SDK agreement phase, with source KDF correctness and converted-identity representation kept explicit. -/
theorem stage_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Local n) :
    (stage setup checks seed scalar packet authenticated).run before =
      (simulateQ (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks representation seed))
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before := by
  have native := RegistrationServerRootCompiler.world_native setup checks representation correct seed scalar
    control packet authenticated (PqxdhJointDhExtractFamily.empty, before)
  rw [RegistrationNativeSourceRoot.interpret_value setup.source setup.hmac correct] at native
  rw [← QueryImpl.simulateQ_compose] at native
  change simulateQ (legacy setup seed scalar)
    ((RegistrationServerRootCompiler.worldStage setup checks setup.serverDomain packet authenticated).run before) = _ at native
  simp only [RegistrationServerRootCompiler.worldStage, StateT.run, simulateQ_map] at native
  have normalized := stage_value setup checks seed scalar packet authenticated (before, before.world.1.primitive.2)
  have projected : Prod.map (id : RustM agreement.AgreementEffect → RustM agreement.AgreementEffect)
      (Prod.fst : Shared n → Local n) =
      (fun result : RustM agreement.AgreementEffect × Shared n => (result.1, result.2.1)) := by
    funext result
    rcases result with ⟨output, current⟩
    rfl
  rw [projected] at normalized
  simp only [StateT.run] at normalized
  rw [normalized] at native
  exact native

/-- The actual root-free preparation restores the literal source agreement and full World on every success and optional rejection. -/
theorem reference_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Local n) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
        (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)) id <$>
        (referenceStage setup checks seed scalar packet authenticated).run before =
      (simulateQ (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks representation seed))
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before := by
  rw [reference_stage, stage_native setup checks representation correct]

end BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.reference_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.reference_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.collect
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.stage_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.stage_value
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.stage_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.reference_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage.reference_native
