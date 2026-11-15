-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds
import BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate

/-! The actual indexed native signing callback extends its current owner's history before returning to the source controller. The history invariant is maintained for rejected callbacks and failed final publication. It is attached to generated owner indices, independently of public-key aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative
open RegistrationNativeIdentityFrontend
open RegistrationNativeBeaconFrontend (Phase)
open RegistrationNativeEdOrigin (Allowed FixedPrekey)
open PqxdhEd25519EufCma (X25519PublicKey Ed25519Signature)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def Fixed (owners : State mlSource) : Prop :=
  ∀ owner ∈ owners, FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory

def At (index : Nat) (prekey : X25519PublicKey) (owners : State mlSource) : Prop :=
  ∀ current, owners[index]? = some current → PqxdhPhase2InputBytes.word current.prekeyPublic = prekey

def Inv (index : Nat) (prekey : X25519PublicKey) (owners : State mlSource) : Prop := At index prekey owners ∧ Fixed owners

def Preserves (invariant : State mlSource → Prop) (work : M n KemSK Auxiliary mlSource Value) : Prop :=
  ∀ owners env result, invariant owners → result ∈ support ((work.run owners).run env) → invariant result.1.2

theorem pure_preserves (invariant : State mlSource → Prop) (value : Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) invariant (pure value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

theorem bind_preserves {Next : Type} (invariant : State mlSource → Prop)
    (work : M n KemSK Auxiliary mlSource Value) (next : Value → M n KemSK Auxiliary mlSource Next)
    (first : Preserves invariant work) (later : ∀ value, Preserves invariant (next value)) :
    Preserves invariant (work >>= next) := by
  intro owners env result prior supported
  rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨value, currentOwners⟩, currentEnv⟩, reached, continued⟩ := supported
  exact later value currentOwners currentEnv result (first owners env _ prior reached) continued

theorem lift_preserves (invariant : State mlSource → Prop)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Preserves invariant (StateT.lift work) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp] at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact prior

theorem simulate_preserves {Query : Type} {spec : OracleSpec Query} (invariant : State mlSource → Prop)
    (implementation : QueryImpl spec (M n KemSK Auxiliary mlSource))
    (allowed : Query → Prop) (step : ∀ query, allowed query → Preserves invariant (implementation query))
    (work : OracleComp spec Value) (bounded : AllQueriesSatisfy work allowed) :
    Preserves invariant (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_preserves invariant value
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_preserves invariant _ _ (step query bounded.1) (fun value => ih value (bounded.2 value))

theorem sample_preserves (invariant : State mlSource → Prop) (work : ProbComp Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) invariant (sample work) := by
  unfold sample
  apply simulate_preserves invariant (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => True)
    (fun _ _ => lift_preserves invariant _)
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem current_inv (index : Nat) (prekey : X25519PublicKey) (owners : State mlSource)
    (change : Owner mlSource → Owner mlSource)
    (same : ∀ current, (change current).prekeyPublic = current.prekeyPublic)
    (fixedChange : ∀ current, PqxdhPhase2InputBytes.word current.prekeyPublic = prekey →
      FixedPrekey (PqxdhPhase2InputBytes.word current.prekeyPublic) current.edHistory →
      FixedPrekey (PqxdhPhase2InputBytes.word (change current).prekeyPublic) (change current).edHistory)
    (prior : Inv index prekey owners) :
    Inv index prekey (match owners[index]? with | none => owners | some current => owners.set index (change current)) := by
  cases found : owners[index]? with
  | none => exact prior
  | some current =>
      obtain ⟨below, _⟩ := List.getElem?_eq_some_iff.mp found
      refine ⟨?_, ?_⟩
      · intro selected selectedAt
        rw [List.getElem?_set_self below] at selectedAt
        cases selectedAt
        simpa only [same] using prior.1 current found
      · intro selected member
        rcases List.mem_or_eq_of_mem_set member with original | rfl
        · exact prior.2 selected original
        · exact fixedChange current (prior.1 current found) (prior.2 current (List.mem_of_getElem? found))

theorem phase_preserves (index : Nat) (prekey : X25519PublicKey) (phase : Phase) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource)
      (Inv index prekey) (updatePhase index phase) := by
  intro owners env result prior supported
  simp only [updatePhase, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact current_inv index prekey owners (fun current => { current with phase }) (fun _ => rfl)
    (fun _ _ fixed => fixed) prior

theorem log_preserves (index : Nat) (prekey : X25519PublicKey)
    (message : Pqxdh.Bytes) (signature : Ed25519Signature) (allowed : Allowed prekey message) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource)
      (Inv index prekey) (logEd index message signature) := by
  intro owners env result prior supported
  simp only [logEd, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  apply current_inv index prekey owners (fun current => { current with edHistory := current.edHistory ++ [.signed message signature] })
    (fun _ => rfl) _ prior
  intro current same fixed
  exact RegistrationNativeEdOrigin.fixed_signed _ _ fixed message signature (same.symm ▸ allowed)

theorem outgoing_preserves (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain)
    (allowed : RegistrationNativeEdSigningBounds.AllowedQuery (PqxdhPhase2InputBytes.word owner.prekeyPublic) query) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (outgoing setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact lift_preserves _ _
    | sign request payload digest =>
        exact pure_preserves _ _
  | inr request =>
      classical
      by_cases matching : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519
      · simp only [outgoing, matching, ite_true]
        refine bind_preserves (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic)) _ _
          (lift_preserves (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic)) _) ?_
        intro signature
        cases signature with
        | none => exact pure_preserves _ _
        | some signature => exact bind_preserves _ _ _ (log_preserves index _ _ signature allowed) (fun _ => pure_preserves _ _)
      · simp only [outgoing, ite_eq_right matching]
        exact pure_preserves _ _



theorem program_preserves {Query : Type} {spec : OracleSpec Query} (invariant : State mlSource → Prop)
    (implementation : QueryImpl spec (M n KemSK Auxiliary mlSource))
    (step : ∀ query, Preserves invariant (implementation query)) (work : OracleComp spec Value) :
    Preserves invariant (simulateQ implementation work) := by
  apply simulate_preserves invariant implementation (fun _ => True) (fun query _ => step query) work
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial,ih⟩

theorem phase_fixed (index : Nat) (phase : Phase) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) Fixed (updatePhase index phase) := by
  intro owners env result prior supported
  simp only [updatePhase,StateT.run_modify,StateT.run_pure,mem_support_pure_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => exact prior
  | some current =>
      intro selected member
      rcases List.mem_or_eq_of_mem_set member with original | rfl
      · exact prior selected original
      · exact prior current (List.mem_of_getElem? found)

theorem authentication_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Preserves (n := n) (Auxiliary := Auxiliary) (mlSource := mlSource) Fixed (authentication setup mlSource query) := by
  cases query with
  | hash request => exact bind_preserves _ _ _ (lift_preserves _ _) (fun _ => pure_preserves _ _)
  | mldsa request | ed25519 request => exact pure_preserves _ _

theorem primitive_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Preserves (n := n) (Auxiliary := Auxiliary) Fixed (primitive setup owner oneTime query) := by
  cases query with
  | convertSecret role => cases role <;> exact pure_preserves _ _
  | dh request => cases role : request.secret_role <;> simp only [primitive,role] <;> exact lift_preserves _ _
  | convertPublic key | generate role | encapsulate key | decapsulate ciphertext => exact lift_preserves _ _

theorem agreement_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Preserves (n := n) (Auxiliary := Auxiliary) Fixed (agreement setup owner oneTime query) := by
  unfold agreement
  refine bind_preserves Fixed _ _ (lift_preserves Fixed _) ?_
  intro _
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request =>
      simp only [agreementCore]
      exact primitive_fixed setup owner oneTime _
  | root request => exact pure_preserves _ _

theorem record_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Preserves (n := n) (Auxiliary := Auxiliary) (mlSource := mlSource) Fixed (record setup wire query) := lift_preserves _ _

theorem abort_fixed (owner : Owner mlSource) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) Fixed (abort owner) :=
  bind_preserves _ _ _ (lift_preserves _ _) (fun _ => pure_preserves _ _)

/-- Actual indexed construction appends only an owner with empty history, through all genuine preparation and birth failures. -/
theorem create_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Preserves (n := n) (Auxiliary := RegistrationServerRoleBackend.State) Fixed (create setup source edPin mlPin keyId) := by
  intro owners env result prior supported
  rw [RegistrationNativeIdentitySourceCreate.create_factor] at supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨⟨reply,current⟩,currentEnv⟩,prepared,continued⟩ := supported
  have same : current=owners := by
    rw [RegistrationNativeIdentitySourcePrepare.prepare_run,support_map] at prepared
    obtain ⟨actual,_possible,equal⟩ := prepared
    exact (congrArg (fun returned => returned.1.2) equal).symm
  cases reply with
  | fail error | div =>
      simp only [StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
      simpa only [same] using prior
  | ok optional => cases optional with
    | none =>
      simp only [StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
      simpa only [same] using prior
    | some selected =>
      rw [RegistrationNativeIdentitySourceCreate.append_program] at continued
      have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ continued
      simp only [mem_support_bind_iff,mem_support_pure_iff] at original
      obtain ⟨born,_born,worldOwner,_world,returned⟩ := original
      cases returned
      intro owner member
      rcases List.mem_append.mp member with old | fresh
      · exact prior owner (same ▸ old)
      · simp only [List.mem_singleton] at fresh
        cases fresh
        exact RegistrationNativeEdOrigin.fixed_empty _

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.pure_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.pure_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.bind_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.bind_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.lift_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.lift_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.simulate_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.simulate_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.sample_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.sample_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.phase_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.phase_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.log_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.log_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.outgoing_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.outgoing_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.program_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.program_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.phase_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.phase_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.authentication_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.authentication_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.primitive_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.primitive_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.agreement_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.agreement_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.record_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.record_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.abort_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.abort_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.create_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative.create_fixed
