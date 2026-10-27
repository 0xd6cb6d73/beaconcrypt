import BeaconcryptCore.Computational.PqxdhInitialBuilderContext
import BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient
import BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext

/-!
A later-parent cut keeps every earlier initializer output as known source state. Subsequent initializer calls use the same original service and map their returned kernels to known labels; they never reuse the new hidden chain as an initializer half. The full post continuation keeps selectors, preparation, application replies, initialization, original reads and all private effects. These are operational representation equations; candidate accounting and reveal masking remain separate consumers.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentPost
open PqxdhInitialPendingPost PqxdhInitialPostContext RawCtxSelectedParentCalls
open RawCtxSelectedFamilyContext RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response Shared Result A N C : Type} {extra : OracleSpec ι} {S B : Nat}

def mapFront {Chain Other : Type} (f : KernelOf Chain → KernelOf Other)
    (before : Front Chain M P I D K S B) : Front Other M P I D K S B :=
  ⟨RawCtxGenericFamilyLive.mapState f before.roles, before.controls, before.consumed⟩

/-- All saved pre-draw kernels are recovered exactly, including every peer, phase and history entry. -/
theorem known_front (target : RootOutput) (before : NativeFront M P I D K S B) :
    mapFront (nativeKernel target) (knownFront before) = before := by
  have kernel : ∀ value : KernelOf RatchetChain, nativeKernel target (knownKernel value) = value := by
    intro value
    simp only [nativeKernel, knownKernel, RawCtxChainInterpretation.mapChains, RawCtxSelectedChain.interpret]
  have phase : ∀ value : RawCtxBeaconLifecycle.Phase D K (KernelOf RatchetChain),
      mapPhase (nativeKernel target) (mapPhase knownKernel value) = value := by
    intro value
    cases value <;> simp only [mapPhase, kernel]
  simp [mapFront, knownFront, RawCtxGenericFamilyLive.mapState, mapRoles, mapServer,
    mapPeer, Option.map_map, Function.comp_def, kernel, mapBeacon, phase]

/-- A finish installs the same role and ticks the same history; the kernel representation is the only changed field. -/
theorem install_map {Chain Other : Type} (f : KernelOf Chain → KernelOf Other) (index : Fin B)
    (before : Front Chain M P I D K S B) (updated : BeaconState (KernelOf Chain) I D K) :
    install index (mapFront f before) (mapBeacon f updated) = mapFront f (install index before updated) := by
  unfold install mapFront RawCtxGenericFamilyLive.mapState mapRoles
  congr 3
  funext other
  by_cases same : other = index
  · subst other
    simp only [Function.update_self]
  · simp only [Function.update_of_ne same]

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
  (target : RootOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RatchetChain)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

noncomputable def nativePrimitive : QueryImpl (RawCtxPendingOwnerQueries.Spec RatchetChain) (Ambient A N C) :=
  fun query => lift (RawCtxSelectedParentNativeCompiler.pending source writer prior entry target query)

noncomputable def labelPrimitive (response : RatchetKdfResponse) :
    QueryImpl (RawCtxPendingOwnerQueries.Spec RawCtxSelectedChain.Slot) (Ambient A N C) :=
  fun query => lift (RawCtxSelectedParentCompiler.pending source writer prior entry response query)

noncomputable def nativeReader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf RatchetChain) S B) (Ambient A N C) :=
  fun query => lift (RawCtxGenericFamilyRead.nativeReader (fun kernel => ⟨kernel⟩) query)

noncomputable def labelReader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf RawCtxSelectedChain.Slot) S B) (Ambient A N C) :=
  fun query => lift (RawCtxGenericFamilyRead.nativeReader (fun kernel => ⟨nativeKernel target kernel⟩) query)

noncomputable def knownInitial (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) :
    Ambient A N C (Option (KernelOf RawCtxSelectedChain.Slot)) :=
  Option.map knownKernel <$> initial secrets

noncomputable def nativeHandler : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (Ambient A N C) :=
  handler (nativePrimitive source writer prior entry target) nativeReader pre application initial selector aux

noncomputable def labelHandler (response : RatchetKdfResponse) :
    QueryImpl (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B) (Ambient A N C) :=
  handler (labelPrimitive source writer prior entry response) (labelReader target) pre application
    (knownInitial initial) selector aux

private theorem native_calls :
    RawCtxGenericOwnerInterpretation.interpretedCalls (nativePrimitive (A := A) (N := N) (C := C) source writer prior entry target)
      RawCtxPendingOwnerQueries.calls = liftCalls (nativeCalls source writer prior entry target) := by
  unfold nativePrimitive
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, simulate_lift, liftCalls,
    RawCtxSelectedParentNativeCompiler.receive_call, RawCtxSelectedParentNativeCompiler.send_call]

private theorem label_calls (response : RatchetKdfResponse) :
    RawCtxGenericOwnerInterpretation.interpretedCalls (labelPrimitive (A := A) (N := N) (C := C) source writer prior entry response)
      RawCtxPendingOwnerQueries.calls = liftCalls (labelCalls source writer prior entry response) := by
  unfold labelPrimitive
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, simulate_lift, liftCalls]
  have h := RawCtxSelectedParentFamilyMap.label_calls (A := A) source writer prior entry response
  exact congrArg (fun calls => liftCalls (N := N) (C := C) calls) h

/-- The actual entire live callback keeps the same complete shared/private/cache state inside the larger post service. -/
theorem native_live : nativeHandler source writer prior entry target pre application initial selector aux ∘ₛ
      liveForward (S := S) (B := B) =
    (fun query => PqxdhInitialBeaconAmbient.lift (RawCtxSelectedParentFamilyMap.nativeLive source writer prior entry target query)) := by
  funext query
  cases query <;> simp [QueryImpl.compose, liveForward, nativeHandler, handler, OracleSpec.query,
    RawCtxPendingFamilyLiveQueries.handler, RawCtxSelectedParentFamilyMap.nativeLive, nativePrimitive, nativeReader]

/-- The label-side live callback uses the same source effects and full native reader for this operational comparison. -/
theorem label_live : labelHandler source writer prior entry target pre application initial selector aux
      (childResponse prior entry target) ∘ₛ liveForward (S := S) (B := B) =
    (fun query => PqxdhInitialBeaconAmbient.lift (RawCtxSelectedParentFamilyMap.labelLive source writer prior entry target query)) := by
  funext query
  cases query <;> simp [QueryImpl.compose, liveForward, labelHandler, handler, OracleSpec.query,
    RawCtxPendingFamilyLiveQueries.handler, RawCtxSelectedParentFamilyMap.labelLive, labelPrimitive, labelReader]

/-- Every original post request preserves the same complete result and state under the concrete retained-parent interpretation. -/
theorem step (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PostSpec extra S B).Domain) (before : LabelFront M P I D K S B) :
    simulateQ (nativeHandler source writer prior entry target pre application initial selector aux)
      ((compiler sender route decode query).run (mapFront (nativeKernel target) before)) =
      Prod.map id (mapFront (nativeKernel target)) <$> simulateQ
        (labelHandler source writer prior entry target pre application initial selector aux (childResponse prior entry target))
        ((compiler sender route decode query).run before) := by
  rcases query with (query | query) | query
  case inr =>
    cases query with
    | finish index raw =>
      unfold nativeHandler labelHandler
      rw [step_interpretation, step_interpretation]
      simp only [interpreted, StateT.run, native_calls, label_calls, mapFront,
        RawCtxGenericFamilyLive.mapState, mapRoles, bind_pure_comp]
      have receiveLaw : ∀ kernel sequence context,
          (liftCalls (N := N) (C := C) (nativeCalls (Auxiliary := A) source writer prior entry target)).receive
            (nativeKernel target kernel) sequence context =
          Prod.map (nativeKernel target) id <$>
            (liftCalls (labelCalls source writer prior entry (childResponse prior entry target))).receive kernel sequence context := by
        intro kernel sequence context
        simp only [liftCalls, receive_map, lift_map]
      have initialLaw : ∀ secrets, initial secrets = Option.map (nativeKernel target) <$> knownInitial initial secrets := by
        intro secrets
        simp [knownInitial, Functor.map_map, Option.map_map, Function.comp_def,
          nativeKernel, knownKernel, RawCtxChainInterpretation.mapChains, RawCtxSelectedChain.interpret]
      rw [PqxdhInitialGenericBeacon.owner_map (nativeKernel target) pre
        (liftCalls (labelCalls source writer prior entry (childResponse prior entry target)))
        (liftCalls (nativeCalls source writer prior entry target)) receiveLaw application
        (knownInitial initial) initial initialLaw]
      simp only [Functor.map_map]
      apply congrArg (fun f => f <$> _)
      funext result
      exact congrArg (fun state => (result.1, state)) (install_map (nativeKernel target) index before result.2)
  case inl.inl =>
    have live := RawCtxSelectedParentFamilyMap.live_program (A := A) source writer prior entry target
      sender route decode ((RawCtxProtocolReveals.SourceSpec S B).query query : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) before.roles
    simp only [RawCtxPendingFamilyLiveTails.program, simulateQ_spec_query, StateT.run] at live
    simp only [compiler, StateT.run, bind_pure_comp, simulateQ_map, ← QueryImpl.simulateQ_compose,
      native_live, label_live, simulate_lift, mapFront]
    rw [live, lift_map]
    simp only [Functor.map_map]
    rfl
  case inl.inr =>
    simp [compiler, StateT.run, selectorForward, OracleSpec.query, nativeHandler, labelHandler, handler,
      Functor.map_map]

/-- The entire original adaptive post schedule retains all optional replies, role fields and private effects after a later-parent cut. -/
theorem program (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PostSpec extra S B) Result) (before : LabelFront M P I D K S B) :
    simulateQ (nativeHandler source writer prior entry target pre application initial selector aux)
      ((simulateQ (compiler sender route decode) client).run (mapFront (nativeKernel target) before)) =
      Prod.map id (mapFront (nativeKernel target)) <$> simulateQ
        (labelHandler source writer prior entry target pre application initial selector aux (childResponse prior entry target))
        ((simulateQ (compiler sender route decode) client).run before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [step]
      simp only [bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

end Interpreter

end BeaconcryptCore.Computational.PqxdhInitialParentPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPost.known_front' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPost.known_front

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPost.install_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPost.install_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPost.native_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPost.native_live

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPost.label_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPost.label_live

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPost.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPost.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentPost.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentPost.program
