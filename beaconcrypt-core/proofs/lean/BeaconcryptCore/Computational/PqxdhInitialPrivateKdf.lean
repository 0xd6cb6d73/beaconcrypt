import BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder

/-!
One explicit private record-KDF handler is installed before the registration builder's first send. The original builder, publication, role reinstallation, public operations and reveal history are retained. The actual fixed source instantiation is proved equal to the existing protocol code; alternative selective handlers are comparison interpreters whose security requires the separate evolving-chain reductions. Public HKDF uses the original real backend throughout.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPrivateKdf
open PqxdhJointKdfGame PqxdhInitialBuilderCut
variable {M P I D K A : Type} {S B : Nat}

noncomputable def registration (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl PqxdhServerRegistrationPublication.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl query => (RawCtxMixedShared.sharedImpl fixed.crypto writer kdf ∘ₛ RawCtxMixedOwner.sendLift) query
  | .inr query => aux query

/-- The explicit private record-KDF interpreter specializes exactly to the original registration primitive handler. -/
theorem registration_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    registration fixed writer (RawCtxSourceHkdf.kdfImpl fixed) aux =
      PqxdhRegistrationProtocolState.registrationImpl fixed writer aux := rfl

noncomputable def build (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM ratchet.concrete.ConcreteRatchetKernel)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) ProbComp
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun state =>
  let current := PqxdhRegistrationProtocolState.consume index ready state
  let selected := PqxdhRegistrationProtocolState.input senderId index metadata current
  PqxdhRegistrationProtocolState.reinstall index current <$>
    (simulateQ (registration fixed writer kdf aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (readyBuild fixed initial selected.binding ready metadata selected.state))).run current.primitive

/-- The original fixed private KDF gives the complete existing source builder, including its FIRST send, optional publication and all role/control/cache reinstallation. -/
theorem build_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (initial : RustM ratchet.concrete.ConcreteRatchetKernel)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    build (I := I) (D := D) (K := K) (B := B) fixed writer (RawCtxSourceHkdf.kdfImpl fixed)
      initial aux senderId index metadata ready =
      protocolBuild fixed writer initial aux senderId index metadata ready := rfl

noncomputable def records (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) ProbComp) := fun query state => do
  let result ← (((RawCtxServerServices.backendImpl fixed writer kdf).mapStateTBase
    (RawCtxProtocolReveals.protocolImpl S B senderId route decode)).flattenStateT query).run
      (PqxdhRegistrationProtocolState.project state)
  pure (result.1, PqxdhRegistrationProtocolState.restore state result.2)

/-- The same actual private KDF also specializes exactly to every original adaptive send/raw/public/reveal callback, preserving controls, consumed identifiers, complete role state and original reveal history. -/
theorem records_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    records (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)
      fixed writer (RawCtxSourceHkdf.kdfImpl fixed) senderId route decode =
      PqxdhRegistrationProtocolState.sourceImpl fixed writer senderId route decode := by
  unfold records
  change (fun query state => do
    let result ← (((RawCtxProtocolBackend.backend fixed writer).mapStateTBase
      (RawCtxProtocolReveals.protocolImpl S B senderId route decode)).flattenStateT query).run
        (PqxdhRegistrationProtocolState.project state)
    pure (result.1, PqxdhRegistrationProtocolState.restore state result.2)) = _
  rw [RawCtxProtocolReveals.protocol_interpretation]
  rfl

/-- The exact selected-response initializer hybrid enters this private KDF handler BEFORE the original first ciphertext is produced, with the actual consumed state and erased Ready root. -/
theorem build_supplied (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    simulateQ (PqxdhInitialReplyErasure.supplied response)
      ((PqxdhInitialServiceBuilder.protocolBuild fixed writer aux senderId index metadata ready).run state) =
      (build fixed writer (RawCtxSourceHkdf.kdfImpl fixed) (PqxdhInitialReplyErasure.kernelOf false response)
        aux senderId index metadata (eraseRoot ready)).run state := by
  rw [build_source]
  exact PqxdhInitialSuppliedBuilder.protocol_supplied fixed writer response aux senderId index metadata ready state

/-- Changing the private record derivation interpreter never changes a public HKDF evaluation or its complete shared state. -/
theorem public_hkdf (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (query : PqxdhJointKdfGame.JointKdfViewQuery) (state : RawCtxSharedPrimitive.SharedState A) :
    (((RawCtxServerServices.backendImpl fixed writer kdf ∘ₛ RawCtxServerServices.publicLift)
      (.inr (.inr query))).run state) =
      pure (query.project (PqxdhJointKdf.productionStream fixed.crypto query.address), state) :=
  RawCtxServerServices.public_hkdf fixed writer kdf query state

end BeaconcryptCore.Computational.PqxdhInitialPrivateKdf

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.registration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.registration_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.build_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.records_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.records_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.build_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.build_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.public_hkdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateKdf.public_hkdf
