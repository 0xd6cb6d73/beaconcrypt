-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartup
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame

/-! The two actual startup samplers share one explicit constructor, ML-generation and World-query skeleton. Their separate accounting laws may erase only the native-call, Env-coin and primitive-uniform counters; all returned credentials, frontend fields and shared caches remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStartupMetric
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeG3MetricWorld (mask)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Spec (n : Nat) (source : RegistrationNativeMldsa.Source) :=
  (Unit →ₒ (Option (PqxdhLiveServerConstruction.Created Unit) × Unit)) +
    ((Unit →ₒ Option (RegistrationNativeMldsa.Credential source)) + WorldSpec n)

noncomputable def program (source : RegistrationNativeMldsa.Source) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) : OracleComp (Spec n source) (Option (RegistrationNativeHiddenStartup.Started source)) := do
  let constructed ← (Spec n source).query (.inl ())
  match constructed.1 with
  | none => pure none
  | some _ =>
      let generated ← (Spec n source).query (.inr (.inl ()))
      match generated with
      | none => pure none
      | some credential =>
          let created := RegistrationServerStartup.publicCreated identity identityIndex serverKeyId
          let _ ← (Spec n source).query (.inr (.inr (.inl created)))
          let digest ← (Spec n source).query (.inr (.inr (.inr (.inl (.inr (.hash (absBytes credential.publicKey)))))))
          let pin : session.ServerAuthenticationPin :=
            ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, serverKeyId⟩,
              credential.publicKey, RegistrationAuthenticationShared.digestArray digest⟩
          let frontend : RegistrationNativePublicFrontend.State source :=
            ⟨RegistrationServerMaterialFrontend.initial created.control pin, [],
              ⟨RegistrationServerRoleBackend.empty, [], [], []⟩, 0⟩
          pure (some ⟨created, ⟨credential, frontend⟩⟩)

noncomputable def actual (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    QueryImpl (Spec n source) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl _ => simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
      (simulateQ coinLift ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()))
  | .inr (.inl _) => simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
      (simulateQ coinLift (RegistrationNativeMldsa.generate source))
  | .inr (.inr query) => CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query

noncomputable def reference (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    QueryImpl (Spec n source) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl _ => PqxdhRecordLiftWorld.sampled
      ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())
  | .inr (.inl _) => PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)
  | .inr (.inr query) => CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query

/-- The explicit skeleton closes to the literal actual guarded startup with its complete result and World poststate. -/
theorem actual_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (actual setup wire route source ensureInit identityIndex serverKeyId) (program source identityIndex serverKeyId identity)).run before =
      (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run before := by
  simp only [program, RegistrationNativeHiddenStartup.start, simulateQ_bind, simulateQ_spec_query,
    actual, StateT.run_bind]
  apply bind_congr
  intro constructed
  cases constructed.1.1 with
  | none => rfl
  | some created =>
      simp only [simulateQ_bind, simulateQ_spec_query, actual, StateT.run_bind]
      apply bind_congr
      intro generated
      cases generated.1 <;> rfl

/-- The reference skeleton retains exactly the original public startup result and its literal unprojected World state. -/
theorem reference_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map (Option.map RegistrationNativeHiddenStartup.Started.native) id <$>
      (simulateQ (reference setup wire route source ensureInit identityIndex serverKeyId) (program source identityIndex serverKeyId identity)).run before =
      (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before := by
  simp only [program, RegistrationNativePublicStartupFrame.startup, simulateQ_bind, simulateQ_spec_query,
    reference, StateT.run_bind, map_bind]
  apply bind_congr
  intro constructed
  cases constructed.1.1 with
  | none => rfl
  | some created =>
      simp only [simulateQ_bind, simulateQ_spec_query, reference, StateT.run_bind, map_bind]
      apply bind_congr
      intro generated
      cases generated.1 with
      | none => rfl
      | some credential =>
          simp only [simulateQ_bind, simulateQ_spec_query, reference, StateT.run_bind, map_bind,
            simulateQ_pure, StateT.run_pure, map_pure]
          apply bind_congr
          intro installed
          apply bind_congr
          intro digest
          rfl

end BeaconcryptCore.Computational.RegistrationNativeStartupMetric
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.actual_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.reference_source
