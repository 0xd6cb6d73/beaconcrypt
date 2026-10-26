import BeaconcryptCore.Computational.PqxdhProtocolRegistration

/-!
Seven preservation theorems carry the selected Server identity, stored secret getter, fixed sender ID, allocation counter and consumed registration history through every supported generated-prefix execution. RootFields is an explicit relation on exactly those fields read by root generation and acceptance. It is preserved from an initial relation, not constructed by equating the existing Server with the freshly generated target Beacon. The complete reached peer map may evolve and is retained separately; no equality with the fixed root-parameter peer snapshot is claimed.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolServerInvariant

open PqxdhProtocolSelector PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhPrivateSourceCoins
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}
variable {M P I D K A : Type} {S B : Nat}

/-- The actual mixed Server service preserves its fixed identity and metadata on every optional reply. -/
theorem server_step_fields {PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : RawCtxServerRouting.State M P × PrimitiveState)
    (result : RawCtxServerMixed.SourceSpec.Range query × (RawCtxServerRouting.State M P × PrimitiveState))
    (present : result ∈ support ((RawCtxServerMixed.sourceImpl impl senderId route decode query).run state)) :
    result.2.1.server.identity = state.1.server.identity ∧
      result.2.1.server.metadata = state.1.server.metadata := by
  rcases query with ⟨plaintext, kid⟩ | raw
  all_goals simp only [RawCtxServerMixed.sourceImpl, StateT.run, bind_pure_comp, support_map] at present
  all_goals obtain ⟨original, supported, rfl⟩ := present
  all_goals first
    | exact (RawCtxServerSend.sendGame_metadata _ senderId plaintext kid state.1 state.2 original supported).2
    | exact (RawCtxServerRouting.rawGame_preserves_metadata _ route decode raw state.1 state.2 original supported).2

/-- Every indexed native role/public step preserves the actual fixed fields of every Server, including unselected owners. -/
theorem role_step_fields
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (state : RawCtxProtocolRoles.State M P I D K S B × RawCtxSharedPrimitive.SharedState A)
    (result : (RawCtxProtocolRoles.SourceSpec S B).Range query ×
      (RawCtxProtocolRoles.State M P I D K S B × RawCtxSharedPrimitive.SharedState A))
    (present : result ∈ support ((RawCtxProtocolRoles.sourceImpl source writer S B senderId route decode query).run state)) :
    ∀ index, (result.2.1.1 index).server.identity = (state.1.1 index).server.identity ∧
      (result.2.1.1 index).server.metadata = (state.1.1 index).server.metadata := by
  rcases query with server | (beacon | publicQuery)
  all_goals simp only [RawCtxProtocolRoles.sourceImpl, StateT.run, bind_pure_comp, support_map] at present
  all_goals obtain ⟨original, supported, rfl⟩ := present
  case inl =>
    simp only [RawCtxRoleFamily.sourceFamily, bind_pure_comp, support_map] at supported
    obtain ⟨localResult, localSupport, rfl⟩ := supported
    have localFields := server_step_fields _ senderId route decode server.2 _ localResult localSupport
    intro index
    by_cases same : index = server.1
    all_goals simp [Function.update, same, localFields.1, localFields.2]
  all_goals exact fun _ => ⟨rfl, rfl⟩

/-- Record, public and explicit reveal services retain Server identity fields alongside registration controls and consumed IDs. -/
theorem source_step_fields
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query ×
      PqxdhRegistrationProtocolState.State M P I D K A S B)
    (present : result ∈ support
      ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode query).run state)) :
    ∀ index, (result.2.roles.1.1 index).server.identity = (state.roles.1.1 index).server.identity ∧
      (result.2.roles.1.1 index).server.metadata = (state.roles.1.1 index).server.metadata := by
  cases query with
  | inl request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, bind_pure_comp, support_map, Functor.map_map] at present
    obtain ⟨original, supported, rfl⟩ := present
    exact role_step_fields source writer senderId route decode request _ original supported
  | inr request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, pure_bind, support_pure, Set.mem_singleton_iff] at present
    simp only [present, PqxdhRegistrationProtocolState.restore, and_self, implies_true]

/-- Joint identity and CCA calls share the execution without changing any native Server identity field. -/
theorem direct_step_fields
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (query : (Spec baseSpec S B).Domain)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count)
    (result : (Spec baseSpec S B).Range query ×
      (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count))
    (present : result ∈ support
      ((directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret query).run state)) :
    ∀ index, (result.2.1.roles.1.1 index).server.identity = (state.1.roles.1.1 index).server.identity ∧
      (result.2.1.roles.1.1 index).server.metadata = (state.1.roles.1.1 index).server.metadata := by
  cases query with
  | inl request =>
    simp only [directImpl, StateT.run, bind_pure_comp, support_map] at present
    obtain ⟨original, supported, rfl⟩ := present
    exact source_step_fields source writer senderId route decode request state.1 original supported
  | inr request =>
    simp only [directImpl, StateT.run, bind_pure_comp, support_map] at present
    obtain ⟨original, _, rfl⟩ := present
    exact fun _ => ⟨rfl, rfl⟩

/-- Every adaptive mixed prefix preserves all fixed Server identity fields, without restricting its replies or stop point. -/
theorem direct_fields {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (Spec baseSpec S B) Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count)
    (result : Result × (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count))
    (present : result ∈ support ((simulateQ
      (directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret) client).run state)) :
    ∀ index, (result.2.1.roles.1.1 index).server.identity = (state.1.roles.1.1 index).server.identity ∧
      (result.2.1.roles.1.1 index).server.metadata = (state.1.roles.1.1 index).server.metadata := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      have equal := OracleComp.eq_of_mem_support_pure (value, state) present
      rw [equal]
      exact fun _ => ⟨rfl, rfl⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind,
        Set.mem_iUnion, exists_prop] at present
      obtain ⟨intermediate, step, rest⟩ := present
      have first := direct_step_fields source writer senderId route decode attachedVerify primitives
        count baseImpl kem secret query state intermediate step
      have last := ih intermediate.1 intermediate.2 result rest
      exact fun index => ⟨(last index).1.trans (first index).1, (last index).2.trans (first index).2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original generated prefix preserves the Server identity fields jointly with its actual selected native state. -/
theorem program_fields
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup KemSK
      (program.Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)))) × BareState count)
    (present : result ∈ support (privateRun attachedVerify primitives count
      (PqxdhPrivatePhase1Prefix.program baseImpl kem setup
        (selected source writer senderId route decode program initial)))) :
    ∃ output, result.1 = some output ∧ ∀ index,
      (output.context.selection.2.roles.1.1 index).server.identity = (initial.roles.1.1 index).server.identity ∧
      (output.context.selection.2.roles.1.1 index).server.metadata = (initial.roles.1.1 index).server.metadata := by
  rw [PqxdhPrivatePhase1Prefix.program_complete] at present
  simp only [mem_support_bind_iff] at present
  obtain ⟨seed, _, generated, _, selectedResult, selectedSupport, finished⟩ := present
  obtain rfl := eq_of_mem_support_pure _ finished
  rw [selected_complete, support_map] at selectedSupport
  obtain ⟨original, originalSupport, rfl⟩ := selectedSupport
  have preserved := direct_fields source writer senderId route decode attachedVerify primitives count
    baseImpl kem generated.secret _ _ original originalSupport
  exact ⟨_, rfl, preserved⟩


/-- Exactly the native fields read by root generation, binding, replay admission and allocation; peer ratchets remain in the complete reached state. -/
def RootFields (c : Pqxdh.Crypto) (secret : M → Pqxdh.Bytes) (senderId : M → Std.U64)
    (index : Fin S) (server : Pqxdh.ServerState)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) : Prop :=
  secret (state.roles.1.1 index).server.metadata = server.ikSk ∧
    PqxdhRefinement.absBytes (state.roles.1.1 index).server.identity = c.edPub server.ikSk ∧
    (senderId (state.roles.1.1 index).server.metadata).val = server.sid ∧
    (state.controls index).last_key_id.val = server.n ∧
    state.consumed index = server.consumed

theorem reached_root_fields
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup KemSK
      (program.Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)))) × BareState count)
    (present : result ∈ support (privateRun attachedVerify primitives count
      (PqxdhPrivatePhase1Prefix.program baseImpl kem setup
        (selected source writer senderId route decode program initial))))
    (secret : M → Pqxdh.Bytes) (index : Fin S) (server : Pqxdh.ServerState)
    (initialMatch : RootFields source.crypto secret senderId index server initial) :
    ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
      RootFields source.crypto secret senderId index server output.context.selection.2 := by
  obtain ⟨output, outputEq, fields⟩ := program_fields source writer senderId route decode
    setup program initial attachedVerify primitives count baseImpl kem result present
  obtain ⟨other, otherEq, controls, consumed⟩ := program_controls source writer senderId route decode
    setup program initial attachedVerify primitives count baseImpl kem result present
  have same : other = output := Option.some.inj (otherEq.symm.trans outputEq)
  subst other
  refine ⟨PqxdhPrivateRootSource.eraseOutput output, by simp only [outputEq, Option.map_some], ?_⟩
  simpa only [RootFields, PqxdhPrivateRootSource.eraseOutput, PqxdhPrivateRootSource.eraseRetained,
    (fields index).1, (fields index).2, controls, consumed] using initialMatch

end BeaconcryptCore.Computational.PqxdhProtocolServerInvariant

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.server_step_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.server_step_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.role_step_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.role_step_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.source_step_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.source_step_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.direct_step_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.direct_step_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.direct_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.direct_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.program_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.program_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.reached_root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolServerInvariant.reached_root_fields
