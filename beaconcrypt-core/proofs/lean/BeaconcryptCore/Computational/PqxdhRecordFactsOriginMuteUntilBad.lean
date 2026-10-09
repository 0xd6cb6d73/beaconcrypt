-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices
import BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal

/-! Exact selected-replay instrumentation through the source service gates. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec hiddenOpening hiddenSealing)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsOriginMuteFamily (NoReplay keyed keyed_agrees)
open PqxdhRecordFactsHashLocal (keyedRawResult)
variable {n : Nat}

/-- The flag reads the actual optional replay plaintext, only at the selected material coordinate. -/
noncomputable def rawBad (target : Label n) (decode : RawDecoder) (label : Label n)
    (bytes : Pqxdh.Bytes) (state : CtxPrivate n) : Bool :=
  if label = target then (keyedRawResult decode label bytes state).1.isSome else false

/-- A false selected raw flag is precisely sufficient for the existing complete keyed-step agreement. -/
theorem raw_noReplay (target : Label n) (decode : RawDecoder) (label : Label n)
    (bytes : Pqxdh.Bytes) (state : CtxPrivate n) (safe : rawBad target decode label bytes state = false) :
    NoReplay decode target (label, .inr bytes) state := by
  intro other equality parsed decoded
  cases equality
  simpa only [rawBad, ite_true, keyedRawResult, PqxdhRecordFactsHashLocal.rawResult, decoded, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using safe

/-- A raw service call agrees on its actual optional plaintext and every state field whenever its flag is false. -/
theorem raw_agrees (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (label : Label n)
    (bytes : Pqxdh.Bytes) (state : CtxPrivate n) (safe : rawBad target decode label bytes state = false) :
    (keyed target modes decode crypto (label, .inr bytes)).run state =
      (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto (label, .inr bytes)).run state :=
  keyed_agrees target modes decode crypto (label, .inr bytes) state
    (raw_noReplay target decode label bytes state safe)

/-- The opening flag follows the original payload, argument and associated-data width gates before inspecting the selected replay result. -/
noncomputable def openingBad (target : Label n) (decode : RawDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) : Bool :=
  match RawCtxFrameDecoding.fromPayload pending.context.frame.payload with
  | none => false
  | some _ =>
    match RawCtxInterpretedArguments.openArguments
        (RawCtxChainInterpretation.mapOpeningChains
          (PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain)
          (PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain) pending) with
    | none => false
    | some input =>
      if width : input.context.associatedData.length = 153 then
        rawBad target decode input.material
          (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
            (PqxdhRecordLiftIdeal.materialAt state.base.chain input.material).2 input.context width)) state
      else false

/-- Only actual opening calls can raise the selected replay-match flag. -/
noncomputable def serviceBad (target : Label n) (decode : RawDecoder)
    (query : Service n) (state : CtxPrivate n) : Bool :=
  match query with
  | .opening pending => openingBad target decode pending state
  | _ => false

/-- The literal hidden opening agrees through every parser gate and through the actual optional plaintext when the opening flag is false. -/
theorem opening_agrees (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (safe : openingBad target decode pending state = false) :
    (simulateQ (keyed target modes decode crypto)
      (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state =
    (simulateQ (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto)
      (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state := by
  unfold hiddenOpening openingBad at *
  split
  · simp_all only [simulateQ_pure, StateT.run_pure]
  · split
    · simp_all only [simulateQ_pure, StateT.run_pure]
    · split
      · simp_all only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
        rw [raw_agrees target modes decode crypto _ _ state safe]
      · simp_all only [simulateQ_pure, StateT.run_pure]

/-- Every nonraw keyed request is identical, including a seal at the selected coordinate. -/
theorem nonraw_agrees (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (label : Label n)
    (request : (unifSpec + CtxAdversarySpec).Domain) (state : CtxPrivate n) :
    (keyed target modes decode crypto (label, .inl request)).run state =
      (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto (label, .inl request)).run state := by
  apply keyed_agrees
  simp [NoReplay]

/-- The literal hidden sealing program agrees on its optional writer output and complete buffer and state, without excluding selected seals. -/
theorem sealing_agrees (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (state : CtxPrivate n) :
    (simulateQ (keyed target modes decode crypto)
      ((hiddenSealing writer state.base.chain replace pending).run state.base.pending)).run state =
    (simulateQ (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto)
      ((hiddenSealing writer state.base.chain replace pending).run state.base.pending)).run state := by
  simp only [hiddenSealing, StateT.run]
  split
  · change (simulateQ (keyed target modes decode crypto) _).run state =
      (simulateQ (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto) _).run state
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [nonraw_agrees target modes decode crypto _ _ state]
    apply bind_congr
    rintro ⟨reply, after⟩
    cases reply <;> simp only [simulateQ_pure, StateT.run_pure]
  · simp only [simulateQ_pure]

/-- Every actual service preserves its complete reply and state between muted and erased handlers until the selected replay flag is raised. -/
theorem service_agrees (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (state : CtxPrivate n) (safe : serviceBad target decode query state = false) :
    (PqxdhRecordFactsOriginMuteServices.interpreter target modes decode crypto base writer replace query).run state =
      (PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter modes decode crypto base writer replace query).run state := by
  simp only [PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose]
  cases query with
  | opening pending =>
      rw [PqxdhRecordFactsPrivateCacheSource.erased_opening]
      exact opening_agrees target modes decode crypto pending state safe
  | sealing pending =>
      rw [PqxdhRecordFactsPrivateCacheSource.erased_sealing]
      exact congrArg (fun work => work >>= fun result =>
        pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } }))
        (sealing_agrees target modes decode crypto writer replace pending state)
  | _ => simp only [PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
      PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
      PqxdhRecordFactsOriginMuteServices.interpreter]

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The comparison specializes to the actual erased source world, with its unchanged counterless base interpreter and universal decoder. -/
theorem erased_agrees (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : Service n) (state : CtxPrivate n)
    (safe : serviceBad target (RawCtxUniversalDecoder.decoder codec.frameRead) query state = false) :
    (PqxdhRecordFactsOriginMuteServices.interpreter target modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace query).run state =
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run state :=
  service_agrees target modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace query state safe

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.raw_noReplay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.raw_noReplay
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.raw_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.raw_agrees
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.opening_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.opening_agrees
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.nonraw_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.nonraw_agrees
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.sealing_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.sealing_agrees
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.service_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.service_agrees
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.erased_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad.erased_agrees
