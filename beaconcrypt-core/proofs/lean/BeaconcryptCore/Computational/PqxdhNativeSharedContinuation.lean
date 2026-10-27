import BeaconcryptCore.Computational.PqxdhNativeSharedPrefix
import BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent

/-! Cached and completed branches of the actual carried source prefix retain their original full continuation on the same ROM. Only proof instrumentation is erased when returning to the original native source state. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhNativeSharedContinuation
open PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

variable {Result : Type}

/-- Every original adaptive callback keeps its complete source state and shared cache throughout the full saved continuation. -/
theorem program (client : OracleComp (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((simulateQ (compiler source writer stage pre application initial selector aux) client).run state)).run cache =
    (simulateQ (PqxdhInitialNativeAudit.handler source writer stage (fun request => localLift (pre request))
      (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
      (fun request => localLift (selector request)) (fun request => localLift (aux request))) client).run (attach state cache) := by
  induction client using OracleComp.inductionOn generalizing state cache with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← step source writer stage pre application initial selector aux query state cache, bind_map_left]
    exact bind_congr fun result => ih result.1.1 result.1.2 result.2

variable {M P Origin : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

abbrev Carried (extra : OracleSpec ι) (M P I D K Result Origin A N C : Type) (S B : Nat) :=
  RawCtxForwardScan.Cut (PqxdhInitialNativeCarried.Context extra M P I D K Result Origin S B)
    (PqxdhInitialNativeCarried.Final M P I D K Result Origin S B) (Local A N C)

/-- The original saved descriptor supplies the exact pending callback and reply continuation; no selected record is reconstructed from output marginals. -/
noncomputable def finish (cut : Carried extra M P I D K Result Origin A N C S B) :
    OracleComp HashSpec (PqxdhInitialNativeCarried.Final M P I D K Result Origin S B × Local A N C) :=
  match cut with
  | .complete result state => pure (result, state)
  | .pending context state => do
      let frame := PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context
      let result ← ((compiler source writer stage pre application initial selector aux) frame.1).run state
      (simulateQ (compiler source writer stage pre application initial selector aux) (frame.2 result.1)).run result.2

/-- Finishing the actual saved source continuation preserves the complete native result and every reached cache entry, while erasing only the additional candidate audit. -/
theorem finish_source (cut : Carried extra M P I D K Result Origin A N C S B) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (attach result.1.2 result.2).1)) <$>
      (simulateQ hashImpl (finish source writer stage pre application initial selector aux mark sender route decode cut)).run cache =
    PqxdhInitialNativeAdjacent.continued source writer mark sender route decode
      (PqxdhInitialNativeAudit.external (fun request => localLift (pre request))
        (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
        (fun request => localLift (selector request)) (fun request => localLift (aux request))) stage
      (PqxdhInitialNativeAuditCarried.eraseCut (RawCtxSharedPrefixScan.restore attach (cut, cache))) := by
  cases cut with
  | complete result state => rfl
  | pending context state =>
    let frame := PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context
    let client : OracleComp (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B)
        (PqxdhInitialNativeCarried.Final M P I D K Result Origin S B) := do
      let answer ← (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B).query frame.1
      frame.2 answer
    have original := congrArg (fun work => Prod.map id Prod.fst <$> work)
      (program source writer stage pre application initial selector aux client state cache)
    rw [PqxdhInitialNativeAudit.program_erase] at original
    simpa only [client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, Functor.map_map,
      Prod.map_def, id_eq, finish, PqxdhInitialNativeAdjacent.continued, RawCtxSharedPrefixScan.restore,
      PqxdhInitialNativeAuditCarried.eraseCut, RawCtxForwardScan.pack, RawCtxPendingMixedPrefix.finish, frame] using original

end BeaconcryptCore.Computational.PqxdhNativeSharedContinuation


/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedContinuation.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedContinuation.program

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedContinuation.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedContinuation.finish_source
