import BeaconcryptCore.Computational.PqxdhServerClearedRoot

/-!
The source root helper preserves its actual core-acceptance outcome, shared-secret clearing, fixed root derivation, copied-input clearing and consumed-ID insertion order. The executable client receives only the related-family root reply and returns the full cleared native pending token. Ordinary auxiliary effects and the complete primitive history/cache remain explicit.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer
open PqxdhServerRootPreparation PqxdhServerStaticDhSource PqxdhServerRelatedRootInput PqxdhServerClearedRoot
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointDhExtractRoot
open PqxdhBeaconPhase2Preparation (Word32)

structure Returned where
  root : RootOutput
  pending : pqxdh.PendingServerRegistration

inductive Auxiliary where
  | eraseShared
  | eraseInput
  | consume : pqxdh.RegistrationId → Auxiliary
abbrev AuxSpec : OracleSpec Auxiliary := fun _ => Unit
abbrev Spec := RootSpec + AuxSpec
abbrev State (A : Type) := PqxdhJointDhExtractFamily.State × A

def familyLift : QueryImpl RootSpec (OracleComp Spec) := fun query => Spec.query (.inl query)
def auxLift : QueryImpl AuxSpec (OracleComp Spec) := fun query => Spec.query (.inr query)

/-- Source erasure positions and consumption are explicit callbacks; neither callback receives unavailable input bytes. -/
noncomputable def client {Reader E : Type} (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E PeerEncoding) : OracleComp Spec (RustM (Option Returned)) := by
  classical
  exact do
    let _ ← Spec.query (.inr .eraseShared)
    if ¬ localNonzero input then pure (ok none) else do
      let root ← Spec.query (.inl (.inr (.derive (message input))))
      let _ ← Spec.query (.inr .eraseInput)
      match root with
      | none => pure (ok none)
      | some root => do
          let token := pending binding input
          let _ ← Spec.query (.inr (.consume token.registration_id))
          pure (ok (some ⟨root, token⟩))

def familyImpl {A : Type} (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp)) :
    QueryImpl RootSpec (StateT (State A) ProbComp) := fun query state =>
  (fun result => (result.1, (result.2, state.2))) <$> (family query).run state.1

def auxImpl {A : Type} (aux : QueryImpl AuxSpec (StateT A ProbComp)) :
    QueryImpl AuxSpec (StateT (State A) ProbComp) := fun query state =>
  (fun result => (result.1, (state.1, result.2))) <$> (aux query).run state.2

def impl {A : Type} (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) : QueryImpl Spec (StateT (State A) ProbComp)
  | .inl query => familyImpl family query
  | .inr query => auxImpl aux query

/-- The analysis record uses the same public descriptor; its unavailable coordinate is evaluated only by the native source interpretation. -/
def nativeMessage {Reader E : Type} (input : Inputs Reader E Word32) : PqxdhJointDhExtractFamily.Message :=
  serverMessage (PqxdhPhase2GapDhSource.peer (PqxdhRootTableInitialization.rootArray input.verified.keys.prekey))
    (PqxdhPhase2InputBytes.word input.second) (PqxdhPhase2InputBytes.word input.third)
    (PqxdhPhase2InputBytes.word input.fourth) (PqxdhPhase2InputBytes.word input.kem)

def nativeRoot {A Reader E : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Inputs Reader E Word32) (original : pqxdh.PendingServerRegistration) :
    StateT (State A) ProbComp RootOutput := fun state =>
  pure (PqxdhJointDhExtractRoot.nativeRoot source (absBytes original.root_key_input.bytes),
    (rootState hmac (nativeMessage input) (absBytes original.root_key_input.bytes) state.1, state.2))

/-- Literal core acceptance precedes clearing; successful source derivation clears its input before recording consumption and returning the original full token. -/
noncomputable def source {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (input : Inputs Reader E Word32) :
    StateT (State A) ProbComp (RustM (Option Returned)) := do
  let accepted := accept control binding input
  let _ ← auxImpl aux .eraseShared
  match accepted with
  | .ok (.Err _) => pure (ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Ok (_, original)) => do
      let root ← nativeRoot kdf hmac input original
      let _ ← auxImpl aux .eraseInput
      let _ ← auxImpl aux (.consume original.registration_id)
      pure (ok (some ⟨root, cleared original⟩))

set_option backward.isDefEq.respectTransparency false in
/-- At the exact reached input, the real family reply has the same complete native root and primitive poststate. -/
theorem root_source {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (input : Inputs Reader E PeerEncoding) (original : pqxdh.PendingServerRegistration)
    (address : PqxdhJointDhExtractFamily.input joint dh seed scalar (message input) =
      some (absBytes original.root_key_input.bytes)) :
    familyImpl (A := A) (sourceImpl kdf hmac joint dh seed scalar) (.inr (.derive (message input))) =
      some <$> nativeRoot kdf hmac (concreteInputs joint seed input) original := by
  funext state
  simp only [familyImpl, sourceImpl, sourceRoot, StateT.run, address, map_pure]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Real core acceptance, all rejection paths, clearing and consumption agree with the executable root client, retaining the full cleared token and every primitive state field. -/
theorem client_source {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (aux : QueryImpl AuxSpec (StateT A ProbComp))
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (input : Inputs Reader E PeerEncoding)
    (references : References domain input) :
    simulateQ (impl (sourceImpl kdf hmac joint dh seed scalar) aux) (client binding input) =
      source kdf hmac aux control binding (concreteInputs joint seed input) := by
  classical
  by_cases valid : localNonzero input
  · obtain ⟨original, accepted, fields, address, rid⟩ := accept_success kdf.crypto joint dh domain secretOfSeed wiring
      seed scalar input references valid control binding
    have token := accepted_cleared binding (concreteInputs joint seed input) control original accepted
    rw [pending_materialized] at token
    have tokenRid : (pending binding input).registration_id = original.registration_id :=
      by simpa only [cleared] using congrArg (fun value : pqxdh.PendingServerRegistration => value.registration_id) token.symm
    have rootEq := root_source (A := A) kdf hmac joint dh seed scalar input original address
    simp only [client, source, accepted, not_true_eq_false, valid, if_false,
      simulateQ_bind, simulateQ_spec_query, impl, rootEq]
    simp only [bind_map_left, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, impl, ← token, cleared]
    rw [tokenRid]
    rfl
  · have rejected := accept_failure kdf.crypto joint domain secretOfSeed wiring seed input references valid control binding
    simp only [client, source, rejected, valid, not_false_eq_true, if_true, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, impl]
    rfl

/-- The complete executable raw stage retains the original ordered prefix and performs root processing only after its actual supported success. -/
noncomputable def stage {A Reader E : Type} {joint : Primitives} (domain : PublicDomain joint)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (binding : pqxdh.ServerBinding) (raw : Pqxdh.Bytes) :
    StateT (State A) ProbComp (RustM (Option Returned)) := do
  let input ← simulateQ (prefixImpl domain preImpl visit) (collect raw)
  match input with
  | none => pure (ok none)
  | some input => simulateQ (impl family aux) (client binding input)

noncomputable def nativeStage {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (seed : IdentitySeed)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (raw : Pqxdh.Bytes) : StateT (State A) ProbComp (RustM (Option Returned)) := do
  let input ← simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed preImpl visit) (collect raw)
  match input with
  | none => pure (ok none)
  | some input => source kdf hmac aux control binding input

set_option backward.isDefEq.respectTransparency false in
/-- The whole original raw prefix derives the references consumed by the root simulation; no arbitrary successful-prefix or input-provenance premise is supplied. -/
theorem stage_source {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (raw : Pqxdh.Bytes) :
    stage domain preImpl visit (sourceImpl kdf hmac joint dh seed scalar) aux binding raw =
      nativeStage kdf hmac joint seed preImpl visit aux control binding raw := by
  funext initial
  change (stage domain preImpl visit (sourceImpl kdf hmac joint dh seed scalar) aux binding raw).run initial =
    (nativeStage kdf hmac joint seed preImpl visit aux control binding raw).run initial
  simp only [stage, nativeStage, collect_realization joint domain seed, StateT.run_bind, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨input, final⟩ reached
  cases input with
  | none => rfl
  | some input =>
      have references := collect_references domain preImpl visit raw initial final input reached
      exact congrFun (client_source kdf hmac joint dh domain secretOfSeed wiring seed scalar aux control binding input references) final

/-- The actual family reduction implements the complete source stage under ordinary fixed-HKDF functional correctness; no smallness or authentication premise is used. -/
theorem stage_real {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect kdf hmac) (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (raw : Pqxdh.Bytes) :
    stage domain preImpl visit (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ reduction) aux binding raw =
      nativeStage kdf hmac joint seed preImpl visit aux control binding raw := by
  rw [reduction_step kdf hmac correct]
  exact stage_source kdf hmac joint dh domain secretOfSeed wiring seed scalar preImpl visit aux control binding raw

end BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.root_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.client_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.stage_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.stage_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.stage_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer.stage_real
