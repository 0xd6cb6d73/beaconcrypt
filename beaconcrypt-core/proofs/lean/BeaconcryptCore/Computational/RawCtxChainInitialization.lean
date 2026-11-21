import BeaconcryptCore.Computational.RawCtxChainOwner
import BeaconcryptCore.Computational.RawCtxInitializedKdfFamily

/-!
The actual supplied-root initializer uses its own initial45 address, separately from ongoing message48 processing. Its first64 bytes select the exact first32/next32 chain halves, with opposite Beacon and Server orientation. The native zero-counter and empty-slot constructor commutes with the private handle interpretation, retaining the complete RustM result and adding no root draw.

These functional equalities do not assert input secrecy, chain independence, native registration publication or a security hybrid. Handles and supplied roots remain private protocol context. Local full76 evaluation may reserve an unused12-byte suffix and is not free computation. Snapshot, persistence and restoration services are outside the requested proof scope.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainInitialization
open RawCtxSourceChainHandles RawCtxChainInterpretation RawCtxMaterialInterpretation
open PqxdhInitialRatchetComplementarity PqxdhRefinement

/-- Initial64 uses the same first/next projections of the complete76 source expansion. -/
theorem initial_halves {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (parent : Chain Atom) :
    ChainBytesRefines (chainOf source roots (.initialFirst parent))
      (firstHalf (RawCtxSourceHkdf.initialResponse source.crypto
        ⟨(chainOf source roots parent).bytes, ratchet.INITIAL_RATCHET_INFO⟩).bytes) ∧
    ChainBytesRefines (chainOf source roots (.initialSecond parent))
      (secondHalf (RawCtxSourceHkdf.initialResponse source.crypto
        ⟨(chainOf source roots parent).bytes, ratchet.INITIAL_RATCHET_INFO⟩).bytes) := by
  simp only [ChainBytesRefines, firstHalf, secondHalf,
    RawCtxSourceHkdf.initialResponse_bytes, PqxdhRefinement.absBytes_INITIAL_RATCHET_INFO]
  simp [chainOf, PqxdhRefinement.absBytes, List.map_map, Function.comp_def]

/-- The actual zero-counter/empty-slot constructor commutes with both chain and material handles. -/
theorem kernel_new {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (send receive : Chain Atom) :
    ConcreteRatchetKernel.new (chainOf source roots send) (chainOf source roots receive) =
      nativeKernel source roots <$> RefinedRatchet.new (Chain Atom) send receive := by
  simp only [ConcreteRatchetKernel.new, ConcreteRatchetKernel.from_counters, RefinedRatchet.new,
    RefinedRatchet.from_counters, map_bind, bind_assoc]
  congr 1

def initialSend {Atom : Type} (beacon : Bool) (parent : Chain Atom) : Chain Atom :=
  if beacon then .initialSecond parent else .initialFirst parent

def initialReceive {Atom : Type} (beacon : Bool) (parent : Chain Atom) : Chain Atom :=
  if beacon then .initialFirst parent else .initialSecond parent

/-- The original role split selects opposite handles from one actual64/76 expansion. -/
theorem initial_split {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (beacon : Bool) (parent : Chain Atom) :
    pqxdh.split_initial_ratchet_kdf_output
      (RawCtxSourceHkdf.initialResponse source.crypto
        ⟨(chainOf source roots parent).bytes, ratchet.INITIAL_RATCHET_INFO⟩).bytes
      (if beacon then (beaconPending (chainOf source roots parent).bytes).initialization
        else (serverPending (chainOf source roots parent).bytes).initialization) =
      ok ⟨chainOf source roots (initialSend beacon parent), chainOf source roots (initialReceive beacon parent)⟩ := by
  cases beacon with
  | false =>
    obtain ⟨left, right, split, hleft, hright⟩ := splitInitialServer_exact
      (RawCtxSourceHkdf.initialResponse source.crypto
        ⟨(chainOf source roots parent).bytes, ratchet.INITIAL_RATCHET_INFO⟩).bytes
    simpa only [chain_eq_of_refines hleft (initial_halves source roots parent).1,
      chain_eq_of_refines hright (initial_halves source roots parent).2,
      initialSend, initialReceive, Bool.false_eq_true, ite_false, serverPending] using split
  | true =>
    obtain ⟨left, right, split, hleft, hright⟩ := splitInitialBeacon_exact
      (RawCtxSourceHkdf.initialResponse source.crypto
        ⟨(chainOf source roots parent).bytes, ratchet.INITIAL_RATCHET_INFO⟩).bytes
    simpa only [chain_eq_of_refines hleft (initial_halves source roots parent).2,
      chain_eq_of_refines hright (initial_halves source roots parent).1,
      initialSend, initialReceive, ite_true, beaconPending] using split

/-- Initial kernel handles reuse the supplied input; no new root, owner, or independent chain is sampled. -/
def initialHandles {Atom : Type} (beacon : Bool) (parent : Chain Atom) : RustM (HandleKernel Atom) :=
  RefinedRatchet.new (Chain Atom) (initialSend beacon parent) (initialReceive beacon parent)

/-- Both actual extracted role initializers are the complete private-handle constructor at the same supplied root. -/
theorem initial_source {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (beacon : Bool) (parent : Chain Atom) :
    RawCtxInitializedKdfFamily.initialReply source ⟨beacon, (chainOf source roots parent).bytes⟩ =
      nativeKernel source roots <$> initialHandles beacon parent := by
  have split := initial_split source roots beacon parent
  cases beacon <;> simp only [RawCtxInitializedKdfFamily.initialReply, Bool.false_eq_true, ite_false, ite_true,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer_eq,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon_eq,
    pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition] at split ⊢
  all_goals rw [split, bind_tc_ok, kernel_new]
  all_goals rfl

end BeaconcryptCore.Computational.RawCtxChainInitialization

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInitialization.initial_halves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInitialization.initial_halves

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInitialization.kernel_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInitialization.kernel_new

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInitialization.initial_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInitialization.initial_split

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInitialization.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInitialization.initial_source
