import BeaconcryptCore.Computational.PqxdhInitialPostPacking
import BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient

/-!
Actual pending record callbacks lift into one complete shared/private/cache interpreter. The lifted complete source frontend has the same replies and role history; the two additional state components are retained throughout every callback. These literal program equations preserve source work and introduce no target-dependent continuation closure.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingAmbient
open PqxdhInitialBeaconAmbient PqxdhInitialPendingPost
variable {Chain M P I D K A N C Result : Type} {S B : Nat}

/-- The complete actual live record operation commutes with the same ambient lift, including every optional reveal and history update. -/
theorem live
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (Base A))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) (Base A))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B) :
    (RawCtxGenericFamilyLive.impl
      (RawCtxGenericOwnerInterpretation.interpretedCalls (fun request => lift (N := N) (C := C) (primitive request)) RawCtxPendingOwnerQueries.calls)
      (fun request => simulateQ (fun q => lift (N := N) (C := C) (primitive q)) (RawCtxPendingOwnerQueries.publicForward request))
      (fun request => lift (N := N) (C := C) (reader request)) sender route decode query).run before =
      lift (N := N) (C := C) ((RawCtxGenericFamilyLive.impl
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader
        sender route decode query).run before) := by
  rw [← RawCtxPendingFamilyLiveQueries.step_interpretation, ← RawCtxPendingFamilyLiveQueries.step_interpretation]
  have handlers : RawCtxPendingFamilyLiveQueries.handler
      (fun request => lift (N := N) (C := C) (primitive request))
      (fun request => lift (N := N) (C := C) (reader request)) =
      (fun query => lift (N := N) (C := C) (RawCtxPendingFamilyLiveQueries.handler primitive reader query)) := by
    funext request
    cases request <;> rfl
  rw [handlers]
  exact simulate_lift _ _

noncomputable def cacheLive
    (impl : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B) (Base A))) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B)
        (StateT (RawCtxSharedPrimitive.SharedState A) (StateT C ProbComp))) :=
  fun query roles state cache => (fun result => (result, cache)) <$> ((impl query).run roles).run state

noncomputable def selectorLift {ι : Type} {extra : OracleSpec ι}
    (selector : QueryImpl extra (StateT N (StateT C ProbComp))) : QueryImpl extra (Ambient A N C) :=
  fun query before => (fun result => (result.1, (before.1, result.2))) <$> (selector query).run before.2

variable {ι X Response Shared : Type} {extra : OracleSpec ι}

/-- Every explicit pending callback executes inside one ambient state and agrees with the complete original post-state packing. -/
theorem step
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (Base A))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) (Base A))
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf Chain)))
    (selector : QueryImpl extra (StateT N (StateT C ProbComp)))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : PqxdhInitialPostPacking.Full Chain M P I D K A N S B) :
    (((PqxdhInitialPendingPost.interpreted
        (fun request => lift (N := N) (C := C) (primitive request))
        (fun request => lift (N := N) (C := C) (reader request))
        pre application initial (selectorLift selector) sender route decode).flattenStateT query).run before) =
      (PqxdhInitialPostPacking.separated
        (cacheLive (C := C) (RawCtxGenericFamilyLive.impl
          (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
          (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader sender route decode))
        selector (PqxdhInitialGenericBeacon.owner pre
          (RawCtxGenericOwnerInterpretation.interpretedCalls (fun request => lift (N := N) (C := C) (primitive request))
            RawCtxPendingOwnerQueries.calls) application initial decode) query).run before := by
  rcases query with (query | query) | query
  case inl.inl =>
    simp only [QueryImpl.flattenStateT, interpreted, bind_pure_comp]
    simp_rw [live]
    funext cache
    let implementation : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
        (StateT (RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B) (Base A)) :=
      RawCtxGenericFamilyLive.impl
      (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
      (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader
      sender route decode
    let work := (implementation query).run before.1.roles
    let execution := work.run before.2.1
    have lift_run : ((PqxdhInitialBeaconAmbient.lift (N := N) (C := C) work).run before.2).run cache =
        (fun result => ((result.1, (result.2, before.2.2)), cache)) <$> execution := rfl
    have cache_run : (cacheLive (C := C) implementation query before.1.roles before.2.1).run cache =
        (fun result => (result, cache)) <$> execution := rfl
    simp only [PqxdhInitialPostPacking.separated, StateT.run, StateT.mk, bind_pure_comp]
    change (((fun x => (x.1.1, x.1.2, x.2)) <$>
      (((fun a => (a.1, {before.1 with roles := a.2})) <$>
        PqxdhInitialBeaconAmbient.lift work).run before.2)).run cache) =
      (((fun a => (a.1.1, {before.1 with roles := a.1.2}, a.2, before.2.2)) <$>
        cacheLive (C := C) implementation query before.1.roles before.2.1).run cache)
    rw [StateT.run_map, StateT.run_map, StateT.run_map]
    rw [lift_run]
    rw [StateT.run_map, cache_run]
    simp only [Functor.map_map, Function.comp_def]
  case inl.inr =>
    simp only [QueryImpl.flattenStateT, interpreted, PqxdhInitialPostPacking.separated,
      StateT.run, StateT.mk, bind_pure_comp]
    change (fun x => (x.1.1, x.1.2, x.2)) <$>
      ((fun result => ((result.1, before.1), result.2)) <$>
        ((fun result => (result.1, (before.2.1, result.2))) <$> ((selector query).run before.2.2))) = _
    simp only [Functor.map_map]
    rfl
  case inr =>
    cases query with
    | finish index raw =>
      simp only [QueryImpl.flattenStateT, interpreted, PqxdhInitialPostPacking.separated,
        StateT.run, StateT.mk, bind_pure_comp]
      let work := (PqxdhInitialGenericBeacon.owner pre
        (RawCtxGenericOwnerInterpretation.interpretedCalls (fun request => lift (N := N) (C := C) (primitive request))
          RawCtxPendingOwnerQueries.calls) application initial decode raw (before.1.roles.1.2 index)).run before.2
      change (fun x => (x.1.1, x.1.2, x.2)) <$>
        ((fun result => ((result.1.1, install index before.1 result.1.2), result.2)) <$> work) =
        (fun result => (result.1.1, install index before.1 result.1.2, result.2)) <$> work
      simp only [Functor.map_map]


/-- The whole adaptive pending program retains the exact complete original post state inside the shared/private/cache interpreter. -/
theorem schedule
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (Base A))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) (Base A))
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf Chain)))
    (selector : QueryImpl extra (StateT N (StateT C ProbComp)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : PqxdhInitialPostPacking.Full Chain M P I D K A N S B) :
    (simulateQ (PqxdhInitialGenericPost.post
      (PqxdhInitialPostPacking.record (cacheLive (C := C) (RawCtxGenericFamilyLive.impl
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader sender route decode)))
      selector (PqxdhInitialGenericBeacon.owner pre
        (RawCtxGenericOwnerInterpretation.interpretedCalls (fun request => lift (N := N) (C := C) (primitive request))
          RawCtxPendingOwnerQueries.calls) application initial decode)) client).run (PqxdhInitialPostPacking.pack before) =
    (fun result => (result.1.1, PqxdhInitialPostPacking.pack (result.1.2, result.2))) <$>
      (simulateQ (handler (fun request => lift (N := N) (C := C) (primitive request))
        (fun request => lift (N := N) (C := C) (reader request)) pre application initial
        (selectorLift selector) aux) ((simulateQ (compiler sender route decode) client).run before.1)).run before.2 := by
  rw [PqxdhInitialPostPacking.schedule, program_interpretation]
  have handlers :
      (PqxdhInitialPendingPost.interpreted (P := P)
        (fun request => lift (N := N) (C := C) (primitive request))
        (fun request => lift (N := N) (C := C) (reader request))
        pre application initial (selectorLift selector) sender route decode).flattenStateT =
      PqxdhInitialPostPacking.separated
        (cacheLive (C := C) (RawCtxGenericFamilyLive.impl
          (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
          (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader sender route decode))
        selector (PqxdhInitialGenericBeacon.owner pre
          (RawCtxGenericOwnerInterpretation.interpretedCalls (fun request => lift (N := N) (C := C) (primitive request))
            RawCtxPendingOwnerQueries.calls) application initial decode) := by
    funext query state
    exact step primitive reader pre application initial selector sender route decode query state
  rw [← handlers, simulateQ_flattenStateT_run]
  simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq]

end BeaconcryptCore.Computational.PqxdhInitialPendingAmbient

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingAmbient.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingAmbient.live

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingAmbient.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingAmbient.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingAmbient.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingAmbient.schedule
