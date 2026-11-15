-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal
/-! Trusted owner requests and external platform coins share one free language. The actual indexed source dictionary retains the complete World, generated pool, private source state and arbitrary result; only the existing named native view omits separately accounted instrumentation. External coins do not debit native counters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev Spec (n : Nat) (KemSK : Type) := RegistrationNativeBeaconFrontend.Trusted n KemSK + unifSpec

def Allowed : (Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK) query
  | .inr _ => True

noncomputable def sourceHandler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (Spec n KemSK) (StateT (RegistrationNativePublicInterpreter.State n KemSK) ProbComp)
  | .inl query => RegistrationNativePublicSourceTrusted.implementation setup wire route sign seed scalar query
  | .inr query => StateT.lift (unifSpec.query query : ProbComp _)

noncomputable def nativeHandler (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source) :
    QueryImpl (Spec n KemSK) (StateT (RegistrationNativeExperiment.State n KemSK source) ProbComp)
  | .inl query => RegistrationNativeExperiment.trusted setup checks representation created source query
  | .inr query => StateT.lift (unifSpec.query query : ProbComp _)

/-- Each allowed trusted request and each uncounted external draw has the exact same complete source outcome under the named native view. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (query : (Spec n KemSK).Domain) (allowed : Allowed query)
    (frontend : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (fun result => (result.1, project roots scalar frontend result.2)) <$>
      (sourceHandler setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar query).run before =
      Prod.map id nativeView <$>
        (nativeHandler setup checks representation created source query).run (restore roots scalar frontend before) := by
  cases query with
  | inl query => exact RegistrationNativePublicSourceTrusted.query_source setup checks wire route representation created scalar credential roots query allowed (frontend, before)
  | inr query =>
    simp only [sourceHandler, nativeHandler, StateT.run_lift, bind_pure_comp, Functor.map_map,
      Prod.map_def, id_eq, project]

/-- The named view commutes with each exact joint native leaf, including external coins. -/
theorem query_stable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : (Spec n KemSK).Domain) :
    RegistrationStateView.Stable (nativeView (mlSource := source))
      (nativeHandler setup checks representation created source query) := by
  cases query with
  | inl query => exact RegistrationNativeMainViewLift.trusted_input setup checks representation created query
  | inr query =>
    intro before
    simp only [nativeHandler, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, RegistrationNativeMainViewLift.view_idempotent]

/-- Every adaptive joint program preserves the complete result and native source view. The result can include the complete current platform state. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : OracleComp (Spec n KemSK) Value) (allowed : work.AllQueriesSatisfy (Allowed (KemSK := KemSK)))
    (frontend : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (fun result => (result.1, project roots scalar frontend result.2)) <$>
      (simulateQ (sourceHandler setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar) work).run before =
      Prod.map id nativeView <$>
        (simulateQ (nativeHandler setup checks representation created source) work).run (restore roots scalar frontend before) := by
  have stable (tree : OracleComp (Spec n KemSK) Value) := RegistrationStateView.program_stable nativeView
    RegistrationNativeMainViewLift.view_idempotent (nativeHandler setup checks representation created source)
    (query_stable setup checks representation created) tree
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    calc
      _ = (sourceHandler setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar query).run before >>= fun reached =>
        Prod.map id nativeView <$>
          (simulateQ (nativeHandler setup checks representation created source) (next reached.1)).run (project roots scalar frontend reached.2) := by
        apply bind_congr
        rintro ⟨value, after⟩
        exact (ih value (allowed.2 value) after).trans (stable (next value) (restore roots scalar frontend after))
      _ = ((fun result => (result.1, project roots scalar frontend result.2)) <$>
          (sourceHandler setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar query).run before) >>= fun reached =>
        Prod.map id nativeView <$>
          (simulateQ (nativeHandler setup checks representation created source) (next reached.1)).run reached.2 := by rw [bind_map_left]
      _ = (Prod.map id nativeView <$>
          (nativeHandler setup checks representation created source query).run (restore roots scalar frontend before)) >>= fun reached =>
        Prod.map id nativeView <$>
          (simulateQ (nativeHandler setup checks representation created source) (next reached.1)).run reached.2 := by
        rw [query_source setup checks wire route representation created scalar credential roots query allowed.1 frontend before]
      _ = _ := by
        rw [bind_map_left]
        apply bind_congr
        rintro ⟨value, after⟩
        exact (stable (next value) after).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint.query_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint.query_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint.program_source
