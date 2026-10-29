-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconInitShared

/-! The complete outgoing Init preserves valid chronological ML signing receipts through all three Ed replies, the Beacon fingerprint and Init hash, native signature checks and dynamic encoding. Each Ed reply is retained before source continuation; the actual Init hash supplies the receipt required for the subsequent ML signing attempt. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBeaconInitHistory

open RegistrationBeaconInitExecutor (Spec EdSpec)
open RegistrationBeaconInitShared (State WorldState project implementation worldImplementation)
open RegistrationSigningShared (SignReply)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {Auxiliary Encoded : Type}

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.begin_beacon_init

def signingState (state : State Auxiliary) : RegistrationSigningShared.State := state.2.2
def Cached (state : State Auxiliary) : Prop := RegistrationSigningShared.Cached (signingState state)

theorem hash_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (request : registration.HashRequest)
    (state : State Auxiliary) (cached : Cached state) (result : CtxRomAuth.CtxDigest × State Auxiliary)
    (supported : result ∈ support ((implementation sign ed (.inl (.hash request))).run state)) :
    Cached result.2 ∧ (signingState result.2).2 ((), hashBytes request) = some result.1 := by
  obtain ⟨inner, member, same⟩ := OracleComp.mem_support_map_peel _
    ((RegistrationSigningShared.implementation sign (.hash request)).run (signingState state)) supported
  cases same
  exact ⟨RegistrationSigningShared.hash_cached_state sign request (signingState state) cached inner member,
    (RegistrationSigningShared.hash_cached sign request (signingState state) inner member).2⟩

theorem sign_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (request : registration.MldsaSigningRequest)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (state : State Auxiliary) (cached : Cached state)
    (hashed : (signingState state).2 ((), payload.transcript) = some digest) (result : SignReply × State Auxiliary)
    (supported : result ∈ support ((implementation sign ed (.inl (.sign request payload digest))).run state)) :
    Cached result.2 := by
  obtain ⟨inner, member, same⟩ := OracleComp.mem_support_map_peel _
    ((RegistrationSigningShared.implementation sign (.sign request payload digest)).run (signingState state)) supported
  cases same
  exact RegistrationSigningShared.sign_cached sign request payload digest (signingState state) cached hashed inner member

theorem ed_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (request : registration.Ed25519SigningRequest)
    (state : State Auxiliary) (cached : Cached state) (result : SignReply × State Auxiliary)
    (supported : result ∈ support ((implementation sign ed (.inr request)).run state)) : Cached result.2 := by
  obtain ⟨inner, _member, same⟩ := OracleComp.mem_support_map_peel _ ((ed request).run state.1) supported
  cases same
  exact cached

private theorem pure_cached {Output : Type} (value : Output) (state : State Auxiliary) (cached : Cached state)
    (result : Output × State Auxiliary) (supported : result ∈ support (pure (value, state) : ProbComp _)) :
    Cached result.2 := by
  simp only [support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact cached

private theorem continue_cached {Input : Type}
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (state : State Auxiliary) (cached : Cached state)
    (keeps : ∀ value result, result ∈ support ((simulateQ (implementation sign ed) (next value)).run state) → Cached result.2)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.continueWith action next)).run state)) : Cached result.2 := by
  cases action with
  | ok value => exact keeps value result supported
  | fail error => exact pure_cached _ state cached result supported
  | div => exact pure_cached _ state cached result supported

theorem ready_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded) (pending : registration.BeaconInitReady)
    (state : State Auxiliary) (cached : Cached state)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.ready encode pending)).run state)) : Cached result.2 := by
  apply continue_cached sign ed pending.message _ state cached _ result supported
  intro view output possible
  exact pure_cached _ state cached output possible

theorem signing_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (state : State Auxiliary) (cached : Cached state)
    (hashed : (signingState state).2 ((), payload.transcript) = some digest)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.fromSigning encode payload digest pending)).run state)) : Cached result.2 := by
  apply continue_cached sign ed pending.request _ state cached _ result supported
  intro request output possible
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨signed, member, continued⟩ := possible
  have afterCached := sign_cached sign ed request payload digest state cached hashed signed member
  apply continue_cached sign ed (pending.resume signed.1) _ signed.2 afterCached _ output continued
  intro effect final finalPossible
  cases effect with
  | Ready selected => exact ready_cached sign ed encode selected signed.2 afterCached final finalPossible
  | _ => exact pure_cached _ signed.2 afterCached final finalPossible

theorem fromHash_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (state : State Auxiliary) (cached : Cached state)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.fromHash encode pending)).run state)) : Cached result.2 := by
  apply continue_cached sign ed pending.request _ state cached _ result supported
  intro request output possible
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨hashed, member, continued⟩ := possible
  obtain ⟨afterCached, receipt⟩ := hash_cached sign ed request state cached hashed member
  apply continue_cached sign ed
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray hashed.1))) _ hashed.2 afterCached _ output continued
  intro effect final finalPossible
  cases effect with
  | MldsaSigningRequested selected =>
      exact signing_cached sign ed encode ⟨.beacon, hashBytes request⟩ hashed.1 selected hashed.2
        afterCached receipt final finalPossible
  | _ => exact pure_cached _ hashed.2 afterCached final finalPossible

theorem fingerprint_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) (state : State Auxiliary) (cached : Cached state)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.fromFingerprint encode pending)).run state)) : Cached result.2 := by
  apply continue_cached sign ed pending.request _ state cached _ result supported
  intro request output possible
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨hashed, member, continued⟩ := possible
  have afterCached := (hash_cached sign ed request state cached hashed member).1
  apply continue_cached sign ed
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray hashed.1))) _ hashed.2 afterCached _ output continued
  intro effect final finalPossible
  cases effect with
  | HashRequested selected => exact fromHash_cached sign ed encode selected hashed.2 afterCached final finalPossible
  | _ => exact pure_cached _ hashed.2 afterCached final finalPossible

theorem fromEd_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) (state : State Auxiliary) (cached : Cached state)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.fromEd encode pending)).run state)) : Cached result.2 := by
  rw [RegistrationBeaconInitExecutor.fromEd.eq_def] at supported
  apply continue_cached sign ed pending.request _ state cached _ result supported
  intro request output possible
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨signed, member, continued⟩ := possible
  have afterCached := ed_cached sign ed request state cached signed member
  cases actual : pending.resume signed.1 with
  | fail error =>
      rw [actual] at continued
      exact pure_cached _ signed.2 afterCached output continued
  | div =>
      rw [actual] at continued
      exact pure_cached _ signed.2 afterCached output continued
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next =>
          rw [actual] at continued
          exact fromEd_cached sign ed encode next signed.2 afterCached output continued
      | FingerprintRequested selected =>
          rw [actual] at continued
          exact fingerprint_cached sign ed encode selected signed.2 afterCached output continued
      | _ =>
          rw [actual] at continued
          exact pure_cached _ signed.2 afterCached output continued
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending signed.1 next actual

theorem begin_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize)
    (state : State Auxiliary) (cached : Cached state)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × State Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.begin encode control inputs coins pin mldsa)).run state)) : Cached result.2 := by
  apply continue_cached sign ed (registration.begin_beacon_init control inputs coins pin mldsa) _ state cached _ result supported
  intro effect output possible
  cases effect with
  | Ed25519SigningRequested selected => exact fromEd_cached sign ed encode selected state cached output possible
  | _ => exact pure_cached _ state cached output possible

/-- Every actual World prefix preserves its chronological ML signing receipts through Ed failures and later publication failures. -/
theorem world_cached {n : Nat} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize)
    (state : WorldState n Auxiliary) (cached : Cached (project state))
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × WorldState n Auxiliary)
    (supported : result ∈ support ((simulateQ (worldImplementation sign ed)
      (RegistrationBeaconInitExecutor.begin encode control inputs coins pin mldsa)).run state)) :
    Cached (project result.2) := by
  have projected : (result.1, project result.2) ∈ support ((simulateQ (implementation sign ed)
      (RegistrationBeaconInitExecutor.begin encode control inputs coins pin mldsa)).run (project state)) := by
    rw [← RegistrationBeaconInitShared.program_project sign ed _ state, support_map]
    exact ⟨result, supported, rfl⟩
  exact begin_cached sign ed encode control inputs coins pin mldsa (project state) cached _ projected

end BeaconcryptCore.Computational.RegistrationBeaconInitHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.hash_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.sign_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.sign_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.ed_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.ed_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.ready_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.ready_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.signing_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.signing_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.fromHash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.fromHash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.fingerprint_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.fingerprint_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.fromEd_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.fromEd_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.begin_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.begin_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitHistory.world_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitHistory.world_cached
