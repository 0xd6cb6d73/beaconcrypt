-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenCounter

/-! The typed native frontend uses the actual pool-free ambient service and the private first-getter candidate switch. These local source laws retain its complete state, parsed selector and genuine private table. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemServerState (mask)
open RegistrationNativeKemParsedRouting (Spec)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (source : RegistrationNativeMldsa.Source) (KemSK : Type) :=
  RegistrationNativeKemSwitchSource.Switched (RegistrationNativeKemServerState.State n source) KemSK

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) :
    QueryImpl (Spec n mlSource KemSK) (OptionT (StateT (State n mlSource KemSK) ProbComp)) :=
  RegistrationNativeKemSwitchSource.source setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) selected pairs publicKey real

def counter (before : State n mlSource KemSK) : Nat := before.1.1.parsedAccepts

def nextCounter (query : (Spec n mlSource KemSK).Domain) (before : State n mlSource KemSK) : Nat :=
  match query with
  | .inl request => RegistrationNativeKemOpenCounter.ambientCounter request before.1.1
  | _ => counter before

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)

/-- The source get returns its actual current native context and retains every private phase/table field. -/
theorem get_run (before : State n mlSource KemSK) :
    (((implementation setup checks wire route representation created credential selected pairs publicKey real
      (.inl (.inl (.inl .get)))).run).run before) =
      pure (some (mask before.1.1), ((mask before.1.1, before.1.2), before.2)) := by
  rcases before with ⟨⟨context, privateState⟩, phase⟩
  rw [implementation, RegistrationNativeKemSwitchFacts.ambient_run]
  simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
    RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure]

/-- The source put changes only the explicit context and retains the complete private KEM table and phase. -/
theorem put_run (before : State n mlSource KemSK) (after : RegistrationNativeKemServerState.State n mlSource) :
    (((implementation setup checks wire route representation created credential selected pairs publicKey real
      (.inl (.inl (.inl (.put after))))).run).run before) =
      pure (some (), ((mask after, before.1.2), before.2)) := by
  rcases before with ⟨⟨context, privateState⟩, phase⟩
  rw [implementation, RegistrationNativeKemSwitchFacts.ambient_run]
  simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
    RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure]

/-- Every source query preserves the actual parsed selector except for its explicit native-context put, independently of KEM candidates and optional failures. -/
theorem query_counter (query : (Spec n mlSource KemSK).Domain)
    (before after : State n mlSource KemSK) (reply : Option ((Spec n mlSource KemSK).Range query))
    (supported : (reply, after) ∈ support
      (((implementation setup checks wire route representation created credential selected pairs publicKey real query).run).run before)) :
    counter after = nextCounter query before := by
  rcases query with request | (request | key)
  · rw [implementation, RegistrationNativeKemSwitchFacts.ambient_run, support_map] at supported
    obtain ⟨⟨value, reached⟩, called, returned⟩ := supported
    cases returned
    exact RegistrationNativeKemOpenCounter.other_counter setup checks wire route representation created credential
      request before.1.1 reached value called
  · cases found : before.2 <;> simp only [implementation, RegistrationNativeKemSwitchSource.source,
      found, RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
      RegistrationNativeKemGame.stopped, RegistrationNativeKemCandidateSource.source,
      RegistrationNativeKemGame.combine, OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
    all_goals obtain ⟨result, _called, returned⟩ := supported; cases returned; rfl
  · cases found : before.2 with
    | some phase =>
        simp only [implementation, RegistrationNativeKemSwitchSource.source, found,
          RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
          RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
          OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
        obtain ⟨result, _called, returned⟩ := supported
        cases returned
        rfl
    | none =>
        simp only [implementation, RegistrationNativeKemSwitchSource.source, found,
          OptionT.run_mk, StateT.run, mem_support_bind_iff] at supported
        obtain ⟨pair, _encapsulated, uniform, _sampled, tail⟩ := supported
        split at tail
        · simp only [pure_bind, mem_support_pure_iff] at tail
          cases tail
          rfl
        · rw [mem_support_bind_iff] at tail
          obtain ⟨value, _called, returned⟩ := tail
          simp only [mem_support_pure_iff] at returned
          cases returned
          rfl

end BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider.get_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider.get_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider.put_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider.put_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider.query_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider.query_counter
