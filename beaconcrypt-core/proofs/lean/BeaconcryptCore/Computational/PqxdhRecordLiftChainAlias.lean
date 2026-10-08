-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainHop

/-! The structural reasons why the chain lift needs no aliasing or refusal summand (decision D3 of the takeover plan, recorded in `doc/impl/record-lift-ideal.md`), as theorems. Aliasing: the ordered hybrid replaces labelled callbacks, never byte values; distinct hops idealize distinct coordinates (`hops_injective`), and adjacent hybrids agree at every private service except the lookup of the hop's own coordinate, whatever any output byte is (`adjacent_agree`, `adjacent_query`). Adversary or environment HKDF evaluations at a hidden chain are not an alias event: they run inside the explicit observers of `PqxdhRecordLiftChainHop.hopObserver` and are covered by the standard-model Extract-on-`uniform32` and HMAC-PRF advantages. Refusal: every hidden kernel constructor is total (`kernel_total`), and a hidden installation is admitted or refused by the key-free client from its control state alone, before its single allocation request, whose reply carries no seed byte (`installServer_admission`, `installBeacon_admission`); no chain callback refuses. Finally, a chain target with zero aliasing and refusal terms implies the chain statement with any explicit nonnegative terms (`statement_of_target`), so the explicit summands of `PqxdhRecordLiftIdeal.ChainLiftStatement` can be instantiated at zero without loss. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainOrder
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- No two hops of the ordered hybrid idealize the same labelled callback; no byte comparison is involved. -/
theorem hops_injective {positions : Nat} (left right : Fin (positions * (n * 2)))
    (same : entryAt left = entryAt right) : left = right := by
  have transport : ∀ (first second : Coordinate (Fin n)) (firstBounded : Bounded positions first)
      (secondBounded : Bounded positions second), first = second →
        index first firstBounded = index second secondBounded := by
    intro first second firstBounded secondBounded equal
    subst equal
    rfl
  calc left = index (entryAt left) (at_bounded left) := (index_at left).symm
    _ = index (entryAt right) (at_bounded right) := transport _ _ _ _ same
    _ = right := index_at right

/-- Adjacent hybrids agree at every private service except the lookup of the hop's own coordinate. -/
theorem adjacent_agree {positions : Nat} (step : Fin (positions * (n * 2))) (query : Service n)
    (different : query ≠ .lookup (entryAt step)) :
    PqxdhRecordLiftPrefixPolicy.AgreesAt (selected positions step.val) (selected positions (step.val + 1)) query := by
  rw [PqxdhRecordLiftChainHop.selected_succ step]
  exact PqxdhRecordLiftSeedPolicy.agrees_update _ _ true query different

/-- Adjacent hybrids execute every private service other than the hop's lookup identically, on every private state and with every reply byte retained. -/
theorem adjacent_query {positions : Nat} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (step : Fin (positions * (n * 2))) (query : Service n) (different : query ≠ .lookup (entryAt step))
    (secret : Private n) :
    (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source (selected positions step.val)) setup codec
        query).run secret =
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source (selected positions (step.val + 1))) setup codec
        query).run secret :=
  PqxdhRecordLiftPrefixPolicy.query_agrees setup codec _ _ query (adjacent_agree step query different) secret

/-- Every hidden kernel constructor is total: no seed-dependent refusal or fallback kernel exists. -/
theorem kernel_total (role : Role) (seed : PqxdhRecordLiftSeed.Seed) :
    ∃ kernel, hiddenKernel role seed = RustM.ok kernel :=
  PqxdhRecordLiftWorld.hiddenKernel_total role seed

/-- A hidden Server installation is admitted exactly when the control state admits it, under every reply: refusal depends on no seed, table or primitive state, and the only private request, the allocation, replies with unit. -/
theorem installServer_admission (keyId : Aeneas.Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (control : Control n) (result : Bool × Control n)
    (supported : result ∈ support ((installServer keyId identity ref).run control)) :
    result.1 = true ↔ ∃ server, control.server = some server ∧ server.peers keyId = none ∧
      Unused control .server ref := by
  simp only [installServer, StateT.run] at supported
  split at supported
  · rename_i none
    rw [mem_support_pure_iff] at supported
    subst result
    simp [none]
  · rename_i server found
    split_ifs at supported with admitted
    · cases ref with
      | known kernel =>
          simp only [resolve, pure_bind, mem_support_pure_iff] at supported
          subst result
          exact ⟨fun _ => ⟨server, found, admitted⟩, fun _ => rfl⟩
      | hidden slot =>
          simp only [resolve, bind_assoc, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at supported
          obtain ⟨_, _, rfl⟩ := supported
          exact ⟨fun _ => ⟨server, found, admitted⟩, fun _ => rfl⟩
    · rw [mem_support_pure_iff] at supported
      subst result
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro other same
      rw [found, Option.some.injEq] at same
      subst same
      exact fun missing unused => admitted ⟨missing, unused⟩

/-- A hidden Beacon installation is admitted exactly when the control state admits it, under every reply. -/
theorem installBeacon_admission (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) (control : Control n)
    (result : Bool × Control n) (supported : result ∈ support ((installBeacon owner shell ref).run control)) :
    result.1 = true ↔ BeaconReady control owner ∧ Unused control .beacon ref := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · cases ref with
    | known kernel =>
        simp only [resolve, pure_bind, mem_support_pure_iff] at supported
        subst result
        exact ⟨fun _ => admitted, fun _ => rfl⟩
    | hidden slot =>
        simp only [resolve, bind_assoc, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at supported
        obtain ⟨_, _, rfl⟩ := supported
        exact ⟨fun _ => admitted, fun _ => rfl⟩
  · rw [mem_support_pure_iff] at supported
    subst result
    simp only [Bool.false_eq_true, false_iff]
    exact admitted

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)

/-- A chain target with zero aliasing and refusal terms implies the chain statement with any explicit aliasing and refusal terms: the explicit summands only weaken the bound. -/
theorem statement_of_target (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (reduction : PqxdhRecordLiftIdeal.ChainReduction n) (bills : PqxdhRecordLiftIdeal.ChainBills)
    (target : PqxdhRecordLiftIdeal.ChainLiftTarget setup codec route serverKid bounds n hmac reduction bills)
    (aliasing refusal : PqxdhRecordLiftIdeal.BillInput → ℝ≥0∞) :
    PqxdhRecordLiftIdeal.ChainLiftStatement setup codec route serverKid bounds n hmac reduction bills aliasing
      refusal := by
  obtain ⟨bool, event⟩ := target
  refine ⟨?_, ?_⟩
  · intro correct E X env startup allowance framed mode adversary budget respects decision cost decisionBound
    obtain ⟨bound, billed⟩ := bool correct env startup allowance framed mode adversary budget respects decision cost
      decisionBound
    refine ⟨bound.trans ?_, billed⟩
    simp only [PqxdhRecordLiftIdeal.noTerm, add_zero]
    exact le_add_right (le_add_right le_rfl)
  · intro correct E X env startup allowance framed mode adversary budget respects event'
    obtain ⟨bound, billed⟩ := event correct env startup allowance framed mode adversary budget respects event'
    refine ⟨bound.trans ?_, billed⟩
    simp only [PqxdhRecordLiftIdeal.noTerm, add_zero]
    exact le_add_right (le_add_right le_rfl)

end BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.hops_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.hops_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.adjacent_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.adjacent_agree

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.adjacent_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.adjacent_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.kernel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.kernel_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.installServer_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.installServer_admission

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.installBeacon_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.installBeacon_admission

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.statement_of_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainAlias.statement_of_target
