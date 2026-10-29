-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter

/-! Only an exposed selected encapsulation changes the private candidate phase. Ordinary routing preserves it through arbitrary actual controllers, including private KEM birth, decapsulation, failed sends and failed authentication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemOpenProvider (State implementation)
open RegistrationNativeOptionalFrame (Keeps)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
local notation "provider" => implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every nonexposed actual source callback retains its private candidate phase, including optional failure replies. -/
theorem query_phase (query : (Spec n mlSource KemSK).Domain)
    (ordinary : ¬ RegistrationNativeKemRouting.IsExposed
      (ambient := RegistrationNativeKemFrontendInterface.Ambient n mlSource) (KemSK := KemSK) query)
    (before after : State n mlSource KemSK) (reply : Option ((Spec n mlSource KemSK).Range query))
    (supported : (reply, after) ∈ support (((provider query).run).run before)) : after.2 = before.2 := by
  rcases query with request | (pool | key)
  · cases phase : before.2 <;> simp only [implementation, RegistrationNativeKemSwitchSource.source,
      phase, RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
      OptionT.run_mk, StateT.run, support_map] at supported
    all_goals obtain ⟨result, _called, returned⟩ := supported; cases returned; rfl
  · cases phase : before.2 <;> simp only [implementation, RegistrationNativeKemSwitchSource.source,
      phase, RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
      OptionT.run_mk, StateT.run, support_map] at supported
    all_goals obtain ⟨result, _called, returned⟩ := supported; cases returned; rfl
  · exact False.elim (ordinary trivial)

/-- An arbitrary actual source program with no exposed getter retains its phase; no source-state or successful-controller premise is supplied. -/
theorem ordinary_program (work : OracleComp (Spec n mlSource KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemRouting.IsExposed
      (ambient := RegistrationNativeKemFrontendInterface.Ambient n mlSource) (KemSK := KemSK)) 0) :
    Keeps Prod.snd provider work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact RegistrationNativeOptionalFrame.pure_keeps Prod.snd provider value
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, following⟩ := bounded
      apply RegistrationNativeOptionalFrame.bind_keeps Prod.snd provider _ _ _
        (fun reply => ih reply (by simpa using following reply))
      intro before after reply supported
      rw [simulateQ_spec_query] at supported
      exact query_phase setup checks wire route representation created credential selected pairs publicKey real
        query (allowed.resolve_right (by omega)) before after (some reply) supported

/-- Routing an arbitrary native frontend through the ordinary public encapsulation service cannot activate or replace a private candidate. -/
theorem routed_program
    (work : OracleComp (RegistrationNativeKemFrontendInterface.Spec n mlSource KemSK) Value) :
    Keeps Prod.snd provider (simulateQ (RegistrationNativeKemRouting.route false) work) :=
  ordinary_program setup checks wire route representation created credential selected pairs publicKey real _
    (RegistrationNativeKemRouting.ordinary_program work)

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase.query_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase.query_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase.ordinary_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase.ordinary_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase.routed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase.routed_program
