import BeaconcryptCore.Computational.PqxdhPhase2OldSource
import BeaconcryptCore.Computational.PqxdhPhase2Selector
import BeaconcryptCore.Computational.PqxdhPhase2KemProvenance
import BeaconcryptCore.Computational.PqxdhPhase2FinishIdentity

/-!
The original adaptive record/public/reveal and identity/CCA source interface gains the actual native Beacon finish operation. The compiler has no generated-state argument and is designed to be fixed before private generation. Its later borrowed interpretation packs the current joint identity state beside the original auxiliary value, retaining one CTX cache and every native role, registration control, consumed identifier and reveal-history field.

These are literal source/ordinary program equalities with the existing optional codec, conversion and local primitive contracts. Reached generated-handle provenance, identity representation, actual generated-driver installation, signing/creation restrictions, complete resource ledgers and cryptographic bounds remain consuming obligations. No selected KEM secret or freshly sampled identity state is an argument to the source compiler, and no storage or restoration service is added.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
open PqxdhPhase2OldSource (packState)
variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev State (M P I D K A : Type) (S B : Nat) :=
  PqxdhRegistrationProtocolState.State M P (IdentityHandle I) D (KemHandle K) A S B
abbrev Spec (baseSpec : OracleSpec ι) (S B : Nat) :=
  PqxdhProtocolSelector.Spec baseSpec S B + PqxdhPhase2LiveFinish.FinishSpec B
abbrev NativeSpec (I D K X Response : Type) :=
  PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D (KemHandle K) (X ⊕ Converted) Response

/-- Actual selected/prior KEM dispatch stays private; the source compiler has no identity seed or selected KEM secret argument. -/
noncomputable def sourceNative
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (NativeSpec I D K X Response) (StateT (SharedState A) (OracleComp (SelectorSpec baseSpec))) :=
  PqxdhPhase2Selector.sourcePre source localImpl ∘ₛ PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode

/-- Every old public request keeps its actual compiler; finish invokes the original native owner on its reached shared state. -/
noncomputable def compiler
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (Spec baseSpec S B) (StateT (State M P I D K A S B) (OracleComp (SelectorSpec baseSpec)))
  | .inl request => PqxdhProtocolSelector.compiler source writer senderId route decode request
  | .inr request => PqxdhPhase2LiveFinish.finishImpl (sourceNative source localImpl) decode request

/-- The complete identity service reply updates only its original identity field in the same packed live state. -/
def identityState {count : Nat} (state : State M P I D K (A × BareState count) S B) (identities : BareState count) :
    State M P I D K (A × BareState count) S B :=
  { state with primitive := ((state.primitive.1.1, identities), state.primitive.2) }

/-- Ordinary finish uses the same complete auxiliary/identity state and the original selected/prior representation. -/
noncomputable def ordinaryNative
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (NativeSpec I D K X Response)
      (StateT (SharedState (A × BareState count)) (OracleComp (MlKemCCAOracleSpec baseSpec))) :=
  PqxdhPhase2SharedIdentity.packed (PqxdhPhase2PreChallenge.pre source
    (borrowedAux attachedVerify primitives count source localImpl)) ∘ₛ
      PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode

/-- Actual old services, current identity/CCA forwarding and native finish share the one reached packed state. -/
noncomputable def ordinary
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (Spec baseSpec S B)
      (StateT (State M P I D K (A × BareState count) S B) (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .inl (.inl request) => StateT.mk fun state =>
      ccaCoins ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode request).run state)
  | .inl (.inr request) => StateT.mk fun state => do
      let result ← (borrowedSelector attachedVerify primitives count request).run state.primitive.1.2
      pure (result.1, identityState state result.2)
  | .inr request => PqxdhPhase2LiveFinish.finishImpl
      (ordinaryNative attachedVerify primitives count source localImpl) decode request

/-- Borrowing the native source handler and packing its actual private state yields the concrete ordinary handler. -/
theorem native_reassociate
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    PqxdhPhase2SharedIdentity.packed
      (((borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count).mapStateTBase
        (sourceNative source localImpl)).flattenStateT) =
      ordinaryNative attachedVerify primitives count source localImpl := by
  funext query state
  simp only [PqxdhPhase2SharedIdentity.packed, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    sourceNative, ordinaryNative, QueryImpl.compose, StateT.run_mk, Functor.map_map]
  rw [PqxdhPhase2Selector.borrowed_complete]
  simpa only [Functor.map_map, PqxdhPhase2SharedIdentity.pack, PqxdhPhase2SharedIdentity.unpack, Prod.mk.eta, StateT.run] using
    PqxdhPhase2SharedIdentity.packed_run
      (PqxdhPhase2PreChallenge.pre source (borrowedAux attachedVerify primitives count source localImpl))
      (PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode query)
      (PqxdhPhase2SharedIdentity.unpack state)

/-- Only the later borrowed interpreter supplies the actual private identity state. -/
noncomputable def borrowed
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (Spec baseSpec S B)
      (StateT (State M P I D K A S B × BareState count) (OracleComp (MlKemCCAOracleSpec baseSpec))) :=
  ((borrowedSelector attachedVerify primitives count).mapStateTBase
    (compiler source writer senderId route decode localImpl)).flattenStateT

/-- Every concrete source request preserves its complete original reply and live state after the actual identity interpreter is installed. -/
theorem compiler_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (Spec baseSpec S B).Domain) (state : State M P I D K A S B) (identities : BareState count) :
    (fun result => (result.1, packState result.2.1 result.2.2)) <$>
      (borrowed attachedVerify primitives count source writer senderId route decode localImpl query).run (state, identities) =
      (ordinary attachedVerify primitives count source writer senderId route decode localImpl query).run
        (packState state identities) := by
  rcases query with ((record | forwarded) | finish)
  case inl.inl =>
    simp only [borrowed, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, compiler,
      StateT.run_mk, ordinary, Functor.map_map]
    change (fun result => (result.1.1, packState result.1.2 result.2)) <$>
      (simulateQ (borrowedSelector attachedVerify primitives count)
        (PqxdhProtocolSelector.coins ((PqxdhRegistrationProtocolState.sourceImpl
          source writer senderId route decode record).run state))).run identities = _
    rw [PqxdhPhase2SourceAux.borrowed_coins]
    have complete := PqxdhPhase2OldSource.registration_schedule source writer senderId route decode
      (liftM ((RawCtxProtocolReveals.SourceSpec S B).query record)) state identities
    simp only [simulateQ_spec_query] at complete
    rw [complete]
    simp only [ccaCoins, simulateQ_map, Functor.map_map]
    exact (simulateQ_map _ _ _).symm
  case inl.inr =>
    simp only [borrowed, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, compiler,
      PqxdhProtocolSelector.compiler, ordinary, StateT.run, StateT.mk, bind_pure_comp]
    change (fun result => (result.1, packState result.2.1 result.2.2)) <$>
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (borrowedSelector attachedVerify primitives count)
          ((fun reply => (reply, state)) <$>
            (liftM ((SelectorSpec baseSpec).query forwarded)))).run identities = _
    rw [simulateQ_map, StateT.run_map, simulateQ_spec_query]
    simp only [Functor.map_map, identityState, packState, PqxdhPhase2SharedIdentity.pack, StateT.run]
    rfl
  case inr =>
    change (fun result => (result.1, packState result.2.1 result.2.2)) <$>
      ((((borrowedSelector attachedVerify primitives count).mapStateTBase
        (PqxdhPhase2LiveFinish.finishImpl (sourceNative source localImpl) decode)).flattenStateT finish).run
        (state, identities)) =
      (PqxdhPhase2LiveFinish.finishImpl (ordinaryNative attachedVerify primitives count source localImpl)
        decode finish).run (packState state identities)
    rw [PqxdhPhase2LiveFinish.finish_interpretation,
      PqxdhPhase2FinishIdentity.finish_reassociate, native_reassociate]

/-- The entire adaptive borrowed source schedule retains its complete result and the same current private state under packing. -/
theorem borrowed_schedule {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S B) Result)
    (state : State M P I D K A S B) (identities : BareState count) :
    (fun result => (result.1, packState result.2.1 result.2.2)) <$>
      (simulateQ (borrowed attachedVerify primitives count source writer senderId route decode localImpl) client).run
        (state, identities) =
      (simulateQ (ordinary attachedVerify primitives count source writer senderId route decode localImpl) client).run
        (packState state identities) := by
  exact map_run_simulateQ_eq_of_query_map_eq _ _ (fun state => packState state.1 state.2)
    (fun query before => compiler_step attachedVerify primitives count source writer senderId route decode localImpl
      query before.1 before.2) client (state, identities)

/-- Execute the fixed source compiler before interpreting identities; the complete original adaptive result becomes the same concrete ordinary schedule at the packed current state. -/
theorem compiler_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S B) Result)
    (state : State M P I D K A S B) (identities : BareState count) :
    (fun result => (result.1.1, packState result.1.2 result.2)) <$>
      (simulateQ (borrowedSelector attachedVerify primitives count)
        ((simulateQ (compiler source writer senderId route decode localImpl) client).run state)).run identities =
      (simulateQ (ordinary attachedVerify primitives count source writer senderId route decode localImpl) client).run
        (packState state identities) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [Functor.map_map, borrowed] using
    borrowed_schedule attachedVerify primitives count source writer senderId route decode localImpl client state identities

end BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.native_reassociate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.native_reassociate

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.compiler_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.borrowed_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.borrowed_schedule

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.compiler_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler.compiler_complete
