import BeaconcryptCore.Computational.RawCtxFunctionalPositions

/-!
The complete original finite role and live-read family retains each kernel's original directional roots under a fixed private retained view. All native opening, sealing, writer, commitment-cache and public HKDF effects remain original. Directional roots and their proofs are private annotation; they add no source capability. This exact functional correspondence is a consumer of the support-only final-table replay, not an equality of mutable hybrid distributions with a fixed-function game.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFunctionalFamily
open PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxFunctionalPositions RawCtxMaterialPositions
variable {A : Type}

noncomputable def backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  RawCtxRetainedTable.viewImpl prior (RawCtxProtocolBackend.backend (Auxiliary := A) source writer) ∘ₛ RawCtxSelectiveKdfFamily.compiler

def execute (prior : Prior) : KdfInterpreter := fun request => RawCtxKdfRequestTable.fullResponse (prior (RawCtxKdfRequestTable.address request))

noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  backend (A := A) source writer prior ∘ₛ RawCtxServerServices.nativeLift

noncomputable def opening (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (core.option.Option RawCtxWholeOwner.Decrypted) :=
  ((native (A := A) source writer prior ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter) (.inr pending)

noncomputable def sealing (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : SendSeal RawCtxSourceSend.SealContext) :
    StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option RawCtxSourceSend.Encrypted) :=
  ((native (A := A) source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) (.inr pending)

/-- The private derivation returns the exact complete retained response and leaves the original shared state unchanged. -/
theorem private_response (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (request : SymmetricRatchetKdfRequest) :
    native (A := A) source writer prior (.inl request) = pure (execute prior request) := by
  simp [native, backend, QueryImpl.compose, RawCtxServerServices.nativeLift,
    RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl, OracleSpec.query, execute]

/-- The complete actual receive callback is precisely the fixed-private interpreter with its original stateful opening. -/
theorem receive_handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    bareReceiveImpl (execute prior) (opening (A := A) source writer prior) =
      (native source writer prior ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter := by
  funext query
  cases query with
  | inr pending => rfl
  | inl request =>
    simpa [bareReceiveImpl, QueryImpl.compose, RawCtxWholeOwner.adapter,
      RawCtxMixedOwner.receiveAdapter, RawCtxMixedOwner.receiveLift, RawCtxSourceOpen.nativeAdapter, OracleSpec.query] using
      (private_response (A := A) source writer prior request).symm

/-- The complete actual send callback is precisely the fixed-private interpreter with its original stateful seal and writer. -/
theorem send_handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    bareSendImpl (execute prior) (sealing (A := A) source writer prior) =
      (native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter := by
  funext query
  cases query with
  | inr pending => rfl
  | inl request =>
    simpa [bareSendImpl, QueryImpl.compose, RawCtxSourceSend.adapter,
      RawCtxMixedOwner.sendAdapter, RawCtxMixedOwner.sendLift, RawCtxSourceSeal.nativeAdapter, OracleSpec.query] using
      (private_response (A := A) source writer prior request).symm

variable {AD PT CT M P I D K Result : Type} {S B : Nat}

noncomputable def annotated (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericFamilyLive.impl
    (calls cr (execute prior) (opening (A := A) source writer prior) (sealing source writer prior))
    (backend source writer prior ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader (serverCount := S) (beaconCount := B) Located.kernel)
    sender route decode (PeerMetadata := P) (Identity := I) (DhPair := D) (KemPair := K)

/-- The complete original family program is exactly the same program with private directional-origin certificates on every kernel, preserving all native effects and read history. -/
theorem source (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxGenericFamilyLive.State (Located cr (execute prior)) M P I D K S B) :
    simulateQ (backend (A := A) source writer prior)
        ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run
          (RawCtxGenericFamilyLive.nativeState Located.kernel state)) =
      Prod.map id (RawCtxGenericFamilyLive.nativeState Located.kernel) <$>
        (simulateQ (annotated (A := A) cr source writer prior sender route decode) client).run state := by
  apply RawCtxGenericFamilyNative.live_schedule Located.kernel
    (calls cr (execute prior) (opening source writer prior) (sealing source writer prior))
    (backend source writer prior)
  · intro entry target context
    simpa only [receive_handler, native, Prod.map_def, id_eq] using
      (receive_erase cr (execute prior) (opening (A := A) source writer prior) (sealing source writer prior) entry target context).symm
  · intro entry context
    simpa only [send_handler, native, Prod.map_def, id_eq] using
      (send_erase cr (execute prior) (opening (A := A) source writer prior) (sealing source writer prior) entry context).symm

/-- Unselected kernels remain ordinary native state and carry no origin premise. -/
abbrev Stored (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (prior : Prior) :=
  ConcreteRatchetKernel ⊕ Located cr (execute prior)

def kernel (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (prior : Prior) : Stored cr prior → ConcreteRatchetKernel
  | .inl original => original
  | .inr located => located.kernel

def origins (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (prior : Prior) : Stored cr prior → Option (RatchetChain × RatchetChain)
  | .inl _ => none
  | .inr located => some (located.sendOrigin, located.receiveOrigin)

noncomputable def storedCalls (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    RawCtxChainOwner.Calls (Stored cr prior) (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) where
  receive entry target context := match entry with
    | .inl original => Prod.map Sum.inl id <$>
        simulateQ ((native source writer prior ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
          (RawCtxOwnerOracle.receive original target context)
    | .inr located => Prod.map Sum.inr id <$>
        (calls cr (execute prior) (opening source writer prior) (sealing source writer prior)).receive located target context
  send entry context := match entry with
    | .inl original => Prod.map Sum.inl id <$>
        simulateQ ((native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
          (RawCtxSourceSend.send original context)
    | .inr located => Prod.map Sum.inr id <$>
        (calls cr (execute prior) (opening source writer prior) (sealing source writer prior)).send located context

/-- Ordinary kernels and the selected initialized kernels both retain the same complete native receive without a premise about other owners. -/
theorem stored_receive (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (entry : Stored cr prior) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Prod.map (kernel cr prior) id <$> (storedCalls (A := A) cr source writer prior).receive entry target context =
      simulateQ ((native source writer prior ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (kernel cr prior entry) target context) := by
  cases entry with
  | inl original => simp [storedCalls, kernel, Functor.map_map, Prod.map_def, id_eq]
  | inr located =>
    simpa only [storedCalls, Functor.map_map, Prod.map_def, id_eq, kernel, Function.comp_def, receive_handler] using
      receive_erase cr (execute prior) (opening (A := A) source writer prior) (sealing source writer prior) located target context

/-- Ordinary and selected kernels retain every original send outcome with unchanged native sealing and writer effects. -/
theorem stored_send (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (entry : Stored cr prior) (context : RawCtxSourceSend.SealContext) :
    Prod.map (kernel cr prior) id <$> (storedCalls (A := A) cr source writer prior).send entry context =
      simulateQ ((native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (kernel cr prior entry) context) := by
  cases entry with
  | inl original => simp [storedCalls, kernel, Functor.map_map, Prod.map_def, id_eq]
  | inr located =>
    simpa only [storedCalls, Functor.map_map, Prod.map_def, id_eq, kernel, Function.comp_def, send_handler] using
      send_erase cr (execute prior) (opening (A := A) source writer prior) (sealing source writer prior) located context

noncomputable def storedImpl (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericFamilyLive.impl
    (storedCalls (A := A) cr source writer prior)
    (backend source writer prior ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader (serverCount := S) (beaconCount := B) (kernel cr prior))
    sender route decode (PeerMetadata := P) (Identity := I) (DhPair := D) (KemPair := K)

/-- The complete original family permits origin annotation only on the selected initialized kernels, leaving every other native kernel unrestricted and all public/read effects unchanged. -/
theorem stored_source (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxGenericFamilyLive.State (Stored cr prior) M P I D K S B) :
    simulateQ (backend (A := A) source writer prior)
        ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run
          (RawCtxGenericFamilyLive.nativeState (kernel cr prior) state)) =
      Prod.map id (RawCtxGenericFamilyLive.nativeState (kernel cr prior)) <$>
        (simulateQ (storedImpl (A := A) cr source writer prior sender route decode) client).run state := by
  apply RawCtxGenericFamilyNative.live_schedule (kernel cr prior)
    (storedCalls cr source writer prior) (backend source writer prior)
  · intro entry target context
    simpa only [native, Prod.map_def, id_eq] using (stored_receive (A := A) cr source writer prior entry target context).symm
  · intro entry context
    simpa only [native, Prod.map_def, id_eq] using (stored_send (A := A) cr source writer prior entry context).symm

/-- Every supported actual mutable-table family result has the same full native result/shared state under its final retained private view and the selected-origin annotation. This is support inclusion only. -/
theorem replay (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (primitive : RawCtxSharedPrimitive.SharedState A) (initial : RawCtxSelectiveChainGame.Store)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) ×
      (RawCtxSharedPrimitive.SharedState A × RawCtxSelectiveChainGame.Store))
    (state : RawCtxGenericFamilyLive.State
      (Stored cr (view (PqxdhJointKdf.productionStream source.crypto) result.2.2.1)) M P I D K S B)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B sender route decode client
      (RawCtxGenericFamilyLive.nativeState (kernel cr _) state) primitive initial)) :
    ∃ reached ∈ support (((simulateQ (storedImpl cr source writer
        (view (PqxdhJointKdf.productionStream source.crypto) result.2.2.1) sender route decode) client).run state).run primitive),
      ((reached.1.1, RawCtxGenericFamilyLive.nativeState (kernel cr _) reached.1.2), reached.2) =
        (result.1, result.2.1) := by
  have actual := (RawCtxSelectiveReplay.complete source stage (RawCtxProtocolBackend.backend source writer)
    (RawCtxSelectiveKdfFamily.program S B sender route decode client (RawCtxGenericFamilyLive.nativeState (kernel cr _) state))
    (primitive, initial) result supported).2
  simp only [RawCtxSelectiveKdfFamily.program, ← QueryImpl.simulateQ_compose] at actual
  change (result.1, result.2.1) ∈ support ((simulateQ (backend source writer _)
    ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run
      (RawCtxGenericFamilyLive.nativeState (kernel cr _) state))).run primitive) at actual
  rw [stored_source, StateT.run_map, support_map] at actual
  exact actual

/-- Every actual annotated receive keeps the selected original directional roots; unselected owners remain unannotated. -/
theorem receive_origins (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (entry : Stored cr prior) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Stored cr prior × core.option.Option RawCtxWholeOwner.Decrypted) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support (((storedCalls cr source writer prior).receive entry target context).run state)) :
    origins cr prior result.1.1 = origins cr prior entry := by
  cases entry with
  | inl original =>
    simp only [storedCalls, StateT.run_map, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rfl
  | inr located =>
    simp only [storedCalls, StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    simp only [calls, StateT.run, support_map] at reached
    obtain ⟨certified, _, rfl⟩ := reached
    rfl

/-- Every actual annotated send keeps the same original directional roots even when sealing fails or the counter is exhausted. -/
theorem send_origins (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (entry : Stored cr prior) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Stored cr prior × Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support (((storedCalls cr source writer prior).send entry context).run state)) :
    origins cr prior result.1.1 = origins cr prior entry := by
  cases entry with
  | inl original =>
    simp only [storedCalls, StateT.run_map, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rfl
  | inr located =>
    simp only [storedCalls, StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    simp only [calls, StateT.run, support_map] at reached
    obtain ⟨certified, _, rfl⟩ := reached
    rfl

end BeaconcryptCore.Computational.RawCtxFunctionalFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.private_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.private_response

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.receive_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.receive_handler

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.send_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.send_handler

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.source

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.stored_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.stored_receive

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.stored_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.stored_send

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.stored_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.stored_source

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.replay

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.receive_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.receive_origins

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalFamily.send_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalFamily.send_origins
