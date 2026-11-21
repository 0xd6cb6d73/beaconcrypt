-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts
import BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting

/-! The open candidate provider keeps the real parsed-attempt counter. Only an explicit local-state put can change it; KEM replies, private births, native authentication, retention and records cannot replace the attempt selector. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemServerState (State mask)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def ambientCounter (query : (RegistrationNativeKemParsedRouting.Ambient n mlSource).Domain)
    (before : State n mlSource) : Nat := match query with
  | .inl (.inl (.put after)) => after.parsedAccepts
  | _ => before.parsedAccepts

attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.retain
  RegistrationServerSdkSource.build CborRecordWorldSimulation.guarded

/-- The actual pool-free ambient callbacks retain the parsed-attempt counter except for the literal local-state put. -/
theorem other_counter (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : (RegistrationNativeKemParsedRouting.Ambient n mlSource).Domain)
    (before after : State n mlSource) (reply : (RegistrationNativeKemParsedRouting.Ambient n mlSource).Range query)
    (supported : (reply, after) ∈ support
      ((RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential query).run before)) :
    after.parsedAccepts = ambientCounter query before := by
  rcases query with (request | ordinary) | publicKey
  · cases request <;> simp only [RegistrationNativeKemParsedRouting.other,
      RegistrationNativeKemRouting.publicAmbient, RegistrationNativeKemFrontendInterface.other,
      RegistrationNativeKemServerInterface.other, RegistrationNativeKemServerInterface.server,
      StateT.run, support_map, mem_support_pure_iff] at supported
    all_goals first
      | (cases supported; rfl)
      | (obtain ⟨result, _reached, returned⟩ := supported; cases returned; rfl)
  · cases ordinary with
    | build session application =>
        simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
          RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.server,
          StateT.run, support_map] at supported
        obtain ⟨result, _reached, returned⟩ := supported
        cases returned
        rfl
    | record query =>
        simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
          RegistrationNativeKemFrontendInterface.other] at supported
        rcases query with query | ⟨owner, query⟩
        · simp only [RegistrationNativeKemFrontendInterface.record, RegistrationNativeKemFrontendInterface.world,
            StateT.run, support_map] at supported
          obtain ⟨result, _reached, returned⟩ := supported
          cases returned
          rfl
        · cases query <;> cases found : before.beacons[owner]? <;>
            simp only [RegistrationNativeKemFrontendInterface.record, found,
              RegistrationNativeKemFrontendInterface.world, StateT.run, support_map,
              mem_support_pure_iff] at supported
          all_goals first
            | (cases supported; rfl)
            | (obtain ⟨result, _reached, returned⟩ := supported; cases returned; rfl)
  · simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
      StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨result, _reached, returned⟩ := supported
    cases returned
    rfl

end BeaconcryptCore.Computational.RegistrationNativeKemOpenCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenCounter.other_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenCounter.other_counter
