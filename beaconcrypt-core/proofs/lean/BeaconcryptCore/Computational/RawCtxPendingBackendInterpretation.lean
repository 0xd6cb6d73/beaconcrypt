import BeaconcryptCore.Computational.RawCtxPendingFamilyNative

/-!
The original enriched pending compiler commutes with an arbitrary lawful backend interpreter. The complete receive/open, send/seal, public and optional read programs are retained. This operational compiler equation permits mutable selective caches and their later retained-view interpretation without assuming equality of arbitrary callbacks or erasing any shared source effects.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation
open RawCtxPendingNativeCalls

private theorem receive_compose {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (native : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp spec))
    (query : (RawCtxInterpretedReceive.ReceiveSpec RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain) :
    simulateQ impl (receive native query) = receive (impl ∘ₛ native) query := by
  simp only [receive, QueryImpl.apply_compose, QueryImpl.simulateQ_compose]

private theorem send_compose {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (native : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp spec))
    (query : (RawCtxInterpretedSend.SendSpec RatchetMaterial RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).Domain) :
    simulateQ impl (send native query) = send (impl ∘ₛ native) query := by
  simp only [send, QueryImpl.apply_compose, QueryImpl.simulateQ_compose]

/-- Interpreting the complete original pending receive/send/public compiler preserves every actual primitive callback in the same lawful monad. -/
theorem pending_compose {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (native : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec)) :
    impl ∘ₛ pending native publicCalls = pending (impl ∘ₛ native) (impl ∘ₛ publicCalls) := by
  have same : impl ∘ₛ original native publicCalls = original (impl ∘ₛ native) (impl ∘ₛ publicCalls) := by
    funext query
    rcases query with (query | query) | ((query | query) | query)
    all_goals simp only [QueryImpl.apply_compose, original]
    all_goals first | exact receive_compose impl native _ | exact send_compose impl native _
  funext query
  simp only [pending, QueryImpl.apply_compose]
  rw [← QueryImpl.simulateQ_compose, same]

/-- The full pending family handler, including its actual optional reader, commutes with the same complete backend interpreter. -/
theorem family_compose {ι : Type} {spec : OracleSpec ι} {serverCount beaconCount : Nat}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (backend : QueryImpl RawCtxServerServices.BackendSpec (OracleComp spec)) :
    impl ∘ₛ (RawCtxPendingFamilyNative.handler (serverCount := serverCount) (beaconCount := beaconCount) backend) =
      RawCtxPendingFamilyNative.handler (impl ∘ₛ backend) := by
  have native : impl ∘ₛ (backend ∘ₛ RawCtxServerServices.nativeLift) =
      (impl ∘ₛ backend) ∘ₛ RawCtxServerServices.nativeLift := by
    funext query
    simp only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
  have publicCalls : impl ∘ₛ (backend ∘ₛ RawCtxServerServices.publicLift) =
      (impl ∘ₛ backend) ∘ₛ RawCtxServerServices.publicLift := by
    funext query
    simp only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
  funext query
  cases query with
  | inl query =>
    have same := congrFun (pending_compose impl (backend ∘ₛ RawCtxServerServices.nativeLift)
      (backend ∘ₛ RawCtxServerServices.publicLift)) query
    rw [native, publicCalls] at same
    exact same
  | inr query =>
    simp only [QueryImpl.apply_compose, RawCtxPendingFamilyNative.handler,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxGenericFamilyRead.nativeReader]
    rfl

/-- Every complete adaptive pending program retains its actual result and all backend effects through the literal compiler composition. -/
theorem program_compose {ι Result : Type} {spec : OracleSpec ι} {serverCount beaconCount : Nat}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (backend : QueryImpl RawCtxServerServices.BackendSpec (OracleComp spec))
    (client : OracleComp (RawCtxPendingFamilyLiveQueries.Spec RatchetChain serverCount beaconCount) Result) :
    simulateQ (RawCtxPendingFamilyNative.handler (impl ∘ₛ backend)) client =
      simulateQ impl (simulateQ (RawCtxPendingFamilyNative.handler backend) client) := by
  rw [← family_compose, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation.pending_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation.pending_compose

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation.family_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation.family_compose

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation.program_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation.program_compose
