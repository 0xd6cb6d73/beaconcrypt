import BeaconcryptCore.Computational.PqxdhInitialGenericProtocol

/-!
Original adaptive record, public and live-reveal requests run on the complete generic protocol state in the same shared primitive monad. The native source instance and the complete representation equation retain all controls, consumed identifiers and actual history. Concrete retained-table receive/send equations are discharged separately below; public HKDF stays in the original public backend.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericRecords
open PqxdhInitialGenericProtocol
variable {Kernel M P I D K A Result : Type} {S B : Nat}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def records
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (State Kernel M P I D K A S B) m) :=
  fun query state => do
    let result ← ((RawCtxGenericFamilyLive.impl calls publicCalls reader senderId route decode query).run state.roles).run state.primitive
    pure (result.1.1, { state with roles := result.1.2, primitive := result.2 })

noncomputable def nativeRecords
    (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) m) :=
  fun query state => do
    let result ← (simulateQ backend ((RawCtxProtocolReveals.protocolImpl S B senderId route decode query).run state.roles)).run state.primitive
    pure (result.1.1, { state with roles := result.1.2, primitive := result.2 })

/-- The whole-state native wrapper is exactly the current source interpreter with the chosen private KDF, including its real public backend. -/
theorem native_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    nativeRecords (P := P) (I := I) (D := D) (K := K) (S := S) (B := B)
      (RawCtxServerServices.backendImpl source writer kdf) senderId route decode =
      PqxdhInitialPrivateKdf.records source writer kdf senderId route decode := by
  funext query state
  simp only [nativeRecords, PqxdhInitialPrivateKdf.records, QueryImpl.flattenStateT,
    QueryImpl.mapStateTBase, PqxdhRegistrationProtocolState.project, PqxdhRegistrationProtocolState.restore,
    StateT.run, StateT.mk, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- The original record operation retains its complete source result and protocol poststate under exact private receive/send interpretation. -/
theorem record_native
    (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (receiveRealized : ∀ entry target context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : State Kernel M P I D K A S B) :
    (nativeRecords backend senderId route decode query).run (native interpret state) =
      Prod.map id (native interpret) <$>
        (records calls (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader interpret)
          senderId route decode query).run state := by
  have complete := congrArg (fun work => work.run state.primitive)
    (RawCtxGenericFamilyNative.live_step interpret calls backend receiveRealized sendRealized senderId route decode query state.roles)
  simp only [StateT.run] at complete
  simp only [records, nativeRecords, native, StateT.run, bind_pure_comp]
  rw [complete]
  simp only [Functor.map, StateT.map, bind_pure_comp, Functor.map_map, native, Prod.map, id_eq]

/-- The full adaptive source schedule preserves every original optional reply and complete state through the same exact native interpretation. -/
theorem schedule_native
    (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (receiveRealized : ∀ entry target context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : State Kernel M P I D K A S B) :
    (simulateQ (nativeRecords backend senderId route decode) client).run (native interpret state) =
      Prod.map id (native interpret) <$>
        (simulateQ (records calls (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader interpret)
          senderId route decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq
    (records calls (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader interpret) senderId route decode)
    (nativeRecords backend senderId route decode) (native interpret)
    (fun query before => (record_native interpret calls backend receiveRealized sendRealized senderId route decode query before).symm)
    client state).symm

/-- The actual complete source schedule enters a generic kernel representation under any mutable backend; the receive and send equations are proved by the concrete native call construction. -/
theorem actual
    (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT (RawCtxSharedPrimitive.SharedState A) m))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    (simulateQ (nativeRecords backend senderId route decode) client).run state =
      Prod.map id (native ConcreteRatchetKernel.mk) <$>
        (simulateQ (records (RawCtxGenericNativeCalls.calls (backend ∘ₛ RawCtxServerServices.nativeLift))
          (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
          senderId route decode) client).run (fromNative ConcreteRatchetKernel.refined state) := by
  simpa only [roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun kernel => by cases kernel; rfl)] using
    schedule_native ConcreteRatchetKernel.mk (RawCtxGenericNativeCalls.calls (backend ∘ₛ RawCtxServerServices.nativeLift))
      backend (RawCtxGenericNativeCalls.receive_realized (backend ∘ₛ RawCtxServerServices.nativeLift))
      (RawCtxGenericNativeCalls.send_realized (backend ∘ₛ RawCtxServerServices.nativeLift))
      senderId route decode client (fromNative ConcreteRatchetKernel.refined state)

end BeaconcryptCore.Computational.PqxdhInitialGenericRecords

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericRecords.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericRecords.native_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericRecords.record_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericRecords.record_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericRecords.schedule_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericRecords.schedule_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericRecords.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericRecords.actual
