-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementExecutor

/-!
Agreement's non-root operations dispatch typed native roles to the selected source primitive backend, retaining its complete auxiliary state. Root HKDF uses the same fixed functional source as initialization and subsequent records, at the actual getter's 192-byte input and 46-byte info. These operations preserve the separate shared CTX cache exactly. Public generation replies alone do not establish secret-handle provenance; that correspondence belongs to the selected role backend and root-family join.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.ProtocolComposition

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationAgreementShared

open RegistrationAgreementExecutor

inductive PrimitiveRequest where
  | convertPublic (key : Array Std.U8 32#usize)
  | convertSecret (role : agreement.DhSecretRole)
  | generate (role : agreement.EphemeralRole)
  | encapsulate (key : core.option.Option (Array Std.U8 1184#usize))
  | decapsulate (ciphertext : core.option.Option (Array Std.U8 1088#usize))
  | dh (request : agreement.DhRequest)

def PrimitiveRequest.toRequest : PrimitiveRequest → Request
  | .convertPublic key => .convertPublic key
  | .convertSecret role => .convertSecret role
  | .generate role => .generate role
  | .encapsulate key => .encapsulate key
  | .decapsulate ciphertext => .decapsulate ciphertext
  | .dh request => .dh request

def PrimitiveSpec : OracleSpec PrimitiveRequest := fun query => Spec (query.toRequest)

def rootResponse (crypto : Pqxdh.Crypto) (request : agreement.RootKdfRequest) : Array Std.U8 32#usize :=
  ⟨(crypto.hkdf (absBytes request.input) (absBytes request.info) 32).map concreteByte,
    by simp [crypto.hkdf_length]⟩

def auxiliary {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) : QueryImpl Spec (StateT Auxiliary ProbComp)
  | .convertPublic key => primitive (.convertPublic key)
  | .convertSecret role => primitive (.convertSecret role)
  | .generate role => primitive (.generate role)
  | .encapsulate key => primitive (.encapsulate key)
  | .decapsulate ciphertext => primitive (.decapsulate ciphertext)
  | .dh request => primitive (.dh request)
  | .root request => pure (.Some (rootResponse source.crypto request))

/-- Only the selected primitive backend owns its auxiliary effects; the existing CTX table is retained verbatim. -/
def implementation {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => (fun inner => (inner.1, (inner.2, state.2))) <$>
    (auxiliary source primitive query).run state.1

theorem root_bytes (crypto : Pqxdh.Crypto) (request : agreement.RootKdfRequest) :
    absBytes (rootResponse crypto request) = crypto.hkdf (absBytes request.input) (absBytes request.info) 32 := by
  simp [rootResponse, absBytes, List.map_map, Function.comp_def]

theorem root_exact {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (request : agreement.RootKdfRequest)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (implementation source primitive (.root request)).run state =
      pure (.Some (rootResponse source.crypto request), state) := by
  rfl

/-- The actual source getter selects the same root input and fixed domain as the record primitives' root adapter. -/
theorem requested_root (crypto : Pqxdh.Crypto) (pending : agreement.RootKdfPending) :
    ∃ request, pending.request = .ok request ∧ rootResponse crypto request =
      RawCtxSourceHkdf.rootResponse crypto ⟨BeaconcryptCore.Refinement.KeyAgreement.candidateInput pending.candidate⟩ := by
  obtain ⟨request, actual, input, info⟩ := BeaconcryptCore.Refinement.KeyAgreement.root_request_refines pending
  refine ⟨request, actual, ?_⟩
  apply Subtype.ext
  simp only [rootResponse, RawCtxSourceHkdf.rootResponse, input, info, absBytes_PQXDH_INFO]

theorem query_cache_unchanged {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (query : Request)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Spec.Range query × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((implementation source primitive query).run state)) :
    result.2.2 = state.2 := by
  change result ∈ support ((fun inner => (inner.1, (inner.2, state.2))) <$>
    (auxiliary source primitive query).run state.1) at supported
  rw [support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

theorem program_cache_unchanged {Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl PrimitiveSpec (StateT Auxiliary ProbComp)) (work : OracleComp Spec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Result × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation source primitive) work).run state)) :
    result.2.2 = state.2 := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, first, rest⟩ := supported
      exact (ih step.1 step.2 result rest).trans
        (query_cache_unchanged source primitive query state step first)

end BeaconcryptCore.Computational.RegistrationAgreementShared

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementShared.root_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementShared.root_bytes
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementShared.root_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementShared.root_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementShared.requested_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementShared.requested_root
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementShared.query_cache_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementShared.query_cache_unchanged
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementShared.program_cache_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementShared.program_cache_unchanged
