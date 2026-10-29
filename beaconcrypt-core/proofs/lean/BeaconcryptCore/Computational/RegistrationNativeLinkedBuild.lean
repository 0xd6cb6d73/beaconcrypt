-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology

/-! A peer key-id link denotes its literal successful original build entry, even when another earlier session response has a different key id. No first-build identification is inferred from that link. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeLinkedBuild
open RegistrationNativeInterface (Entry)

private theorem linked_mem (transcript : List PqxdhDeploymentInterface.Entry) (keyId : U64) (session : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.linkOf transcript keyId = some (session, response)) :
    response.keyId = keyId ∧ ∃ payload,
      (⟨.inl (.inr (.build session payload)), some response⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | build index payload =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i matching
              simp only [Option.some.injEq, Prod.mk.injEq] at value
              rcases value with ⟨rfl, rfl⟩
              exact ⟨matching, payload, member⟩
            · cases value
    | _ => cases value
  · cases value

private theorem native_build (entry : Entry) (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (same : entry.erase = (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- The designated key-id link is an actual successful original native build with the same session and response. -/
theorem original (entries : List Entry) (keyId : U64) (session : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.linkOf (entries.map Entry.erase) keyId = some (session, response)) :
    response.keyId = keyId ∧ ∃ payload,
      (⟨.inl (.inr (.build session payload)), some response⟩ : Entry) ∈ entries := by
  obtain ⟨matching, payload, member⟩ := linked_mem (entries.map Entry.erase) keyId session response found
  obtain ⟨native, nativeMember, erased⟩ := List.mem_map.mp member
  exact ⟨matching, payload, native_build native session payload response erased ▸ nativeMember⟩

end BeaconcryptCore.Computational.RegistrationNativeLinkedBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLinkedBuild.original' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLinkedBuild.original
