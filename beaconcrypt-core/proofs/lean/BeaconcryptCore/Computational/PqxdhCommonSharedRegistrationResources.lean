import BeaconcryptCore.Computational.PqxdhSourceSharedPreparation
import BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds

/-!
The actual common registration builder charges its shared hash and each local allocation/writer callback. All optional failures stay in the query tree. Fixed-HKDF, AEAD, parsing, and serialization remain the actual deterministic source operations; their existing native nine-class ledger is not a claim about machine running time.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources
open PqxdhJointKdfGame CtxRomAuth AdaptiveCtxSharedHash PqxdhAcceptedRegistration
variable {M P I D K A : Type} {S B : Nat}

/-- The hash class charges one commitment; the uniform class charges all three actual probabilistic auxiliary callbacks separately. -/
def cost (hash : Bool) (qPeer qPlaintext qWriter : Nat) : NativeKind → Nat
  | .hash => if hash then 1 else 0
  | .peerReserve => if hash then 0 else qPeer
  | .plaintextReserve => if hash then 0 else qPlaintext
  | .phase2Writer => if hash then 0 else qWriter
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- Literal source callbacks, rather than an opaque registration observer, supply each per-interface resource bound. -/
theorem step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A) (qPeer qPlaintext qWriter : Nat)
    (peerBound : ∀ state, (callbacks.reservePeer.run state).IsTotalQueryBound qPeer)
    (plaintextBound : ∀ size state, ((callbacks.reservePlaintext size).run state).IsTotalQueryBound qPlaintext)
    (writerBound : ∀ fields state, ((callbacks.responseWrite fields).run state).IsTotalQueryBound qWriter)
    (hash : Bool) (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (state : A) :
    ((PqxdhCommonSharedRegistration.compiler source writer callbacks query).run state).IsQueryBoundP
      (HashClass hash) (cost hash qPeer qPlaintext qWriter (nativeKind query)) := by
  rcases query with (request | (input | (bytes | frame))) | query
  all_goals try (cases hash <;> simp [PqxdhCommonSharedRegistration.compiler, RawCtxMixedOwner.sendLift,
    RawCtxSourceSharedRom.native, cost, nativeKind, HashClass, isQueryBoundP_query_iff])
  case inr.false =>
    apply RawCtxSelectiveSharedRom.coins_bound
    cases query <;> simp only [PqxdhSourceAuxiliary.localServer]
    all_goals first | exact peerBound state | exact plaintextBound _ state | exact writerBound _ state | trivial
  case inr.true =>
    cases query <;> exact RawCtxSelectiveSharedRom.coins_no_hash _

/-- The full native nine-class partition sums to one hash or the three separately charged local callback bills. -/
theorem cost_sum (hash : Bool) (qPeer qPlaintext qWriter : Nat) :
    (∑ kind, cost hash qPeer qPlaintext qWriter kind) =
      if hash then 1 else qPeer + qPlaintext + qWriter := by
  have enumeration : (Finset.univ : Finset NativeKind) =
      {.kdf, .aead, .hash, .frameWriter, .identity, .peerReserve, .plaintextReserve, .erase, .phase2Writer} := by decide
  cases hash <;> simp [enumeration, cost, Nat.add_assoc]

/-- The literal accepted common builder pays every actual callback on both successful publication and failed allocation/writing paths. -/
theorem build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A) (qPeer qPlaintext qWriter : Nat)
    (peerBound : ∀ state, (callbacks.reservePeer.run state).IsTotalQueryBound qPeer)
    (plaintextBound : ∀ size state, ((callbacks.reservePlaintext size).run state).IsTotalQueryBound qPlaintext)
    (writerBound : ∀ fields state, ((callbacks.responseWrite fields).run state).IsTotalQueryBound qWriter)
    (hash : Bool) (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    (PqxdhCommonSharedRegistration.build source writer callbacks sender index metadata ready state).IsQueryBoundP
      (HashClass hash) (if hash then 1 else qPeer + qPlaintext + qWriter) := by
  simp only [PqxdhCommonSharedRegistration.build, bind_pure_comp, isQueryBoundP_map_iff]
  have bounded := buildReady_weighted (PqxdhCommonSharedRegistration.compiler source writer callbacks)
    (HashClass hash) (cost hash qPeer qPlaintext qWriter)
    (step source writer callbacks qPeer qPlaintext qWriter peerBound plaintextBound writerBound hash)
    source (PqxdhRegistrationProtocolState.input sender index metadata
      (PqxdhRegistrationProtocolState.consume index ready (PqxdhCommonSharedRegistration.withCache state ∅))).binding ready metadata
    (PqxdhRegistrationProtocolState.input sender index metadata
      (PqxdhRegistrationProtocolState.consume index ready (PqxdhCommonSharedRegistration.withCache state ∅))).state
    (PqxdhRegistrationProtocolState.consume index ready (PqxdhCommonSharedRegistration.withCache state ∅)).primitive.1
  simpa only [cost_sum] using bounded

end BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources.step

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources.cost_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources.cost_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources.build
