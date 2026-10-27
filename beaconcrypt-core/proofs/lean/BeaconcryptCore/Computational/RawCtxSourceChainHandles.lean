import BeaconcryptCore.Computational.RawCtxChainRealization
import BeaconcryptCore.Computational.RawCtxSourceMaterialLabels

/-!
Private chain provenance uses root, first-output and next-output handles. Their fixed-source interpretation executes the same actual76 function; first32 is both a possible initial chain and the material key, second32 is the next chain, and last12 is the nonce. Equal interpreted inputs share the complete output, even for different handles. The supplied root interpretation stays private.

Both direction callbacks execute the actual native KDF request before retaining its next/parent handles. Opening and sealing use unchanged source-selected native arguments and the same complete auxiliary/CTX cache state. Full send and receive equalities discharge the joint callback equations internally for the existing fixed functional HKDF/shared primitive backend. Native optional primitive errors outside that existing functional contract are not covered.

This is a real-source interpretation, not a random-key ideal or an input-hiding result. Recursive interpretation may repeat local HKDF/decoding work; logical callback counts do not make that work free. Handles retain private provenance and must not become network, reveal or snapshot values. Public guesses, initial aliases, actual key/chain disclosures, live retained ancestors, dynamic target-table realization and the security hybrid require their separate explicit treatment.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceChainHandles
open RawCtxMaterialInterpretation RawCtxChainInterpretation RawCtxInterpretedOpening

/-- Private provenance syntax, not bytes, owner identifiers, network values or proof of distinct keys. -/
inductive Chain (Atom : Type) where
  | root : Atom → Chain Atom
  | first : Chain Atom → Chain Atom
  | next : Chain Atom → Chain Atom

/-- Both source projections share the same complete fixed expansion at the interpreted input. -/
noncomputable def chainOf {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain) :
    Chain Atom → RatchetChain
  | .root atom => roots atom
  | .first parent => ⟨(RawCtxInterpretedReceive.decodeResponse
      (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest (chainOf source roots parent)))).2.key.bytes⟩
  | .next parent => (RawCtxInterpretedReceive.decodeResponse
      (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest (chainOf source roots parent)))).1

/-- A material handle names its derivation input; source slots keep their original sequence tags. -/
noncomputable def materialOf {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (parent : Chain Atom) : RatchetMaterial :=
  (RawCtxInterpretedReceive.decodeResponse
    (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest (chainOf source roots parent)))).2

/-- No inverse map or uniqueness premise is needed for the actual source step. -/
theorem source_step {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (parent : Chain Atom) :
    RawCtxInterpretedReceive.decodeResponse
      (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest (chainOf source roots parent))) =
      (chainOf source roots (.next parent), materialOf source roots parent) := rfl

/-- Equal interpreted chain inputs share their entire actual next-chain/material output. -/
theorem source_alias {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (left right : Chain Atom) (same : chainOf source roots left = chainOf source roots right) :
    (chainOf source roots (.next left), materialOf source roots left) =
      (chainOf source roots (.next right), materialOf source roots right) := by
  rw [← source_step, ← source_step, same]

abbrev HandleKernel (Atom : Type) := RefinedRatchet (Chain Atom) (Chain Atom) (Chain Atom)

noncomputable def nativeKernel {Atom : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (entry : HandleKernel Atom) : ConcreteRatchetKernel :=
  ⟨RawCtxChainRealization.kernel (chainOf source roots) (chainOf source roots) (materialOf source roots) entry⟩

noncomputable def receiveNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  (RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter

/-- Execute the actual source callback before retaining its opaque derivation handles. -/
noncomputable def receiveLabels {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec (Chain Atom) (Chain Atom) (Chain Atom)
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl parent => (fun _ => (.next parent, parent)) <$>
      receiveNative source writer (.inl (RawCtxChainSend.nativeRequest (chainOf source roots parent)))
  | .inr pending => receiveNative source writer (.inr (toNative
      (mapOpening (materialOf source roots) (mapOpeningChains (chainOf source roots) (chainOf source roots) pending))))

/-- The concrete functional backend discharges the KDF equation without changing callback state. -/
theorem receive_kdf {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (parent : Chain Atom) :
    RawCtxInterpretedReceive.decodeResponse <$>
      receiveNative (Auxiliary := Auxiliary) source writer (.inl (RawCtxChainSend.nativeRequest (chainOf source roots parent))) =
      (fun reply => (chainOf source roots reply.1, materialOf source roots reply.2)) <$>
        receiveLabels source writer roots (.inl parent) := by
  simp only [receiveLabels, receiveNative, QueryImpl.compose, RawCtxWholeOwner.adapter,
    RawCtxMixedOwner.receiveAdapter, OracleSpec.query, simulateQ_query, Functor.map_map]
  simp [RawCtxSourceMaterialLabels.nativeImpl, RawCtxMixedShared.sharedImpl,
    QueryImpl.compose, RawCtxMixedShared.sharedAdapter, RawCtxSourceOpen.nativeAdapter,
    RawCtxMixedOwner.receiveLift, OracleSpec.query]
  change RawCtxInterpretedReceive.decodeResponse <$>
    (pure (RawCtxSourceHkdf.response source.crypto
      (RawCtxChainSend.nativeRequest (chainOf source roots parent))) :
      StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp RatchetKdfResponse) =
    (fun _ : RatchetKdfResponse => (chainOf source roots (.next parent), materialOf source roots parent)) <$>
      (pure (RawCtxSourceHkdf.response source.crypto
        (RawCtxChainSend.nativeRequest (chainOf source roots parent))) :
        StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp RatchetKdfResponse)
  simp only [map_pure, source_step]

/-- The actual fixed-source receive executes the same requests and complete state with opaque private provenance. -/
theorem receive_source {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (entry : HandleKernel Atom)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (receiveNative (Auxiliary := Auxiliary) source writer)
      (RawCtxOwnerOracle.receive (nativeKernel source roots entry) target context) =
      (fun result => (nativeKernel source roots result.1, result.2)) <$>
        simulateQ (receiveLabels source writer roots) (RawCtxChainReceive.execute entry target context) :=
  RawCtxChainRealization.receive_native (chainOf source roots) (chainOf source roots) (materialOf source roots)
    (receiveLabels source writer roots) (receiveNative source writer)
    (receive_kdf source writer roots) (fun _ => rfl) entry target context

noncomputable def sendNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl (RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  (RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter

/-- Actual send callbacks share the same native KDF branch and fixed expansion as receive. -/
noncomputable def sendLabels {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) :
    QueryImpl (RawCtxChainSend.SendSpec (Chain Atom) (Chain Atom) (Chain Atom)
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl parent => (fun _ => (.next parent, parent)) <$>
      sendNative source writer (.inl (RawCtxChainSend.nativeRequest (chainOf source roots parent)))
  | .inr pending => sendNative source writer (.inr (RawCtxInterpretedSend.nativeSeal
      (RawCtxInterpretedSend.mapSeal (materialOf source roots)
        (RawCtxChainSend.nativeSeal (chainOf source roots) (chainOf source roots) pending))))

/-- Both source directions execute the very same realized primitive request. -/
theorem send_kdf {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (parent : Chain Atom) :
    RawCtxInterpretedReceive.decodeResponse <$>
      sendNative (Auxiliary := Auxiliary) source writer (.inl (RawCtxChainSend.nativeRequest (chainOf source roots parent))) =
      (fun reply => (chainOf source roots reply.1, materialOf source roots reply.2)) <$>
        sendLabels source writer roots (.inl parent) :=
  receive_kdf source writer roots parent

/-- The active source send retains its original optional ciphertext and advanced kernel under private handles. -/
theorem send_source {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (entry : HandleKernel Atom) (context : RawCtxSourceSend.SealContext) :
    simulateQ (sendNative (Auxiliary := Auxiliary) source writer)
      (RawCtxSourceSend.send (nativeKernel source roots entry) context) =
      (fun result => (nativeKernel source roots result.1, result.2)) <$>
        simulateQ (sendLabels source writer roots) (RawCtxChainSend.execute entry context) :=
  RawCtxChainRealization.send_native (chainOf source roots) (chainOf source roots) (materialOf source roots)
    (sendLabels source writer roots) (sendNative source writer)
    (send_kdf source writer roots) (fun _ => rfl) entry context

end BeaconcryptCore.Computational.RawCtxSourceChainHandles

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceChainHandles.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceChainHandles.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceChainHandles.source_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceChainHandles.source_alias

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceChainHandles.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceChainHandles.receive_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceChainHandles.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceChainHandles.receive_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceChainHandles.send_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceChainHandles.send_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceChainHandles.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceChainHandles.send_source
