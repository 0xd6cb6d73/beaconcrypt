-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal

/-! The actual source allocation and pending publication surround the marker-only root continuation. Mutations return only unit and preserve the private native state inside their interpreter; no selected KEM bytes or full post-root state is returned to the executable tail. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail
open PqxdhRegistrationJointKemOpaqueSuffix PqxdhRegistrationJointKemOpaqueClient
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhServerRelatedRootConsumer PqxdhSecretInputKdf
variable {Reader KemSK Result : Type} {ι : Type} {baseSpec : OracleSpec ι}

inductive Mutation (KemSK : Type) where
  | install : GameState KemSK → Mutation KemSK
  | publish : Nat → Returned → Mutation KemSK
abbrev MutationSpec (KemSK : Type) : OracleSpec (Mutation KemSK) := fun _ => Unit
abbrev Spec (Reader KemSK : Type) := PqxdhRegistrationJointKemOpaqueClient.Spec Reader + MutationSpec KemSK

def forward : QueryImpl (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) (OracleComp (Spec Reader KemSK)) :=
  fun query => (Spec Reader KemSK).query (.inl query)

/-- Native bookkeeping performs the same complete replacement and later point update as the source tail; it never returns private post-root state. -/
def mutation : QueryImpl (MutationSpec KemSK) (NativeGame KemSK)
  | .install state => nativeSet state
  | .publish index token =>
      nativeModify fun current => { current with pending := Function.update current.pending index (some token) }

noncomputable def impl (hmac : HmacSha512) (index : Nat) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (Spec Reader KemSK) (NativeGame KemSK)
  | .inl query => romImpl KemSK hmac index candidate query
  | .inr query => mutation query

/-- Forwarding the original marker continuation retains its complete interpreted effects and every adaptive reply. -/
theorem forward_run (hmac : HmacSha512) (index : Nat) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) Result) :
    simulateQ (impl (KemSK := KemSK) hmac index candidate) (simulateQ forward work) =
      simulateQ (romImpl KemSK hmac index candidate) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, forward, impl, ih]

/-- Literal source session allocation, acceptance, root/erase/consume and successful publication, with the KEM slot represented privately by a marker. -/
noncomputable def tail (serverKeyId : U64) (publicIdentity : PublicIdentity)
    (state : GameState KemSK) (collected : Option (Input Reader) × List Pqxdh.Bytes) :
    OracleComp (Spec Reader KemSK) (Option Nat) := do
  let index := state.sessions
  let _ ← (Spec Reader KemSK).query (.inr (.install
    { state with sessions := index + 1, server := { state.server with consumed := collected.2 } }))
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← simulateQ forward (PqxdhRegistrationJointKemOpaqueClient.client state.server.control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input)
      match returned with
      | .ok (some token) => do
          let _ ← (Spec Reader KemSK).query (.inr (.publish index token))
          pure (some index)
      | _ => pure none

/-- The complete actual tail is recovered with its original allocation on failure, root callback, consumed IDs and optional pending publication. The equality is of full native computations. -/
theorem tail_native (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (state : GameState KemSK)
    (collected : Option (Input Reader) × List Pqxdh.Bytes) :
    simulateQ (impl setup.hmac state.sessions candidate) (tail setup.serverKeyId publicIdentity state collected) =
      PqxdhRegistrationJointServerAccept.tail setup publicIdentity state
        (Option.map (materialize candidate) collected.1, collected.2) := by
  simp only [tail, PqxdhRegistrationJointServerAccept.tail, simulateQ_bind, simulateQ_spec_query, impl, mutation]
  apply bind_congr
  intro ignored
  cases collected.1 with
  | none => rfl
  | some input =>
      simp only [Option.map_some, simulateQ_bind,
        forward_run, PqxdhRegistrationJointKemOpaqueClient.client_native]
      apply bind_congr
      intro returned
      cases returned with
      | fail error => rfl
      | div => rfl
      | ok result =>
          cases result <;> simp only [simulateQ_bind, simulateQ_spec_query, impl, mutation, simulateQ_pure]
          rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail.forward_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail.forward_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail.tail_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail.tail_native
