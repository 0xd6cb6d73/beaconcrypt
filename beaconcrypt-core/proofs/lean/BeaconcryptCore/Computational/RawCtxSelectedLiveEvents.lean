import BeaconcryptCore.Computational.RawCtxSelectedLiveAliases
import BeaconcryptCore.Computational.StatefulGoodEvent
import BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation

/-!
The actual direct-disclosure flag may already be set initially. For any event on the complete source result/state, restricting that event to the original final false flag gives exact unconditioned agreement between native and masked live reads. Consequently the alias bound for that restricted event charges only the same masked continuation's full candidate list, retaining all prior entries, rather than charging the probability of a disclosure excluded by the event itself.

No conditional distribution or small-disclosure premise is used. The flag still records only the concrete hidden-current-chain read defined in LiveRead; it is not yet the complete global freshness predicate. Parent-address public projections, earlier root/ancestor knowledge, initial-first32 aliases, additional owners and the reached native uniform cut remain obligations. The actual fixed-source/query scopes of the imported live compiler and alias theorem remain unchanged. Snapshot, persistence and restoration services are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveEvents
open RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveAliases
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- Any full-state event excluding the actually recorded direct exposure has the same unconditioned probability under actual and masked replies. Prior exposure remains excluded. -/
theorem event_good {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount)
    (event : Result × RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount → Prop) :
    Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner (nativeReader target)) client).run state)}[event result ∧ result.2.2 = false] =
    Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner labelRead) client).run state)}[event result ∧ result.2.2 = false] := by
  exact StatefulGoodEvent.event_good _ _
    (agree_good source writer (RawCtxKdfRequestTable.fullResponse output) sender decode owner target)
    (sticky source writer _ sender decode owner (nativeReader target))
    (sticky source writer _ sender decode owner labelRead) client state event

/-- Excluding the recorded direct disclosure removes its additive probability term; alias loss still uses the actual complete masked candidate list. -/
theorem good_alias_bound {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount)
    (event : Result × RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount → Prop) :
    Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner (nativeReader target)) client).run state)}[event result ∧ result.2.2 = false] ≤
    Pr{let result ← (consistentGame source writer output labelRead (RawCtxSelectedQueryTrace.rootVector target)
        sender decode owner client state)}[event result ∧ result.2.2 = false] +
    Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner labelRead) client).run state)}[RawCtxSelectedQueryTrace.rootVector target ∈ result.2.1.1.2.2] := by
  rw [event_good source writer output target sender decode owner client state event]
  refine (AdaptiveCtxPrefixValidation.probEvent_le_add_ofReal_tvDist _
    (consistentGame source writer output labelRead (RawCtxSelectedQueryTrace.rootVector target)
      sender decode owner client state) _).trans ?_
  exact add_le_add le_rfl (by
    simpa only [ENNReal.ofReal_toReal (prEvent_ne_top _)] using
      ENNReal.ofReal_le_ofReal (source_distance source writer output labelRead
        (RawCtxSelectedQueryTrace.rootVector target) sender decode owner client state))

end BeaconcryptCore.Computational.RawCtxSelectedLiveEvents

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveEvents.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveEvents.event_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveEvents.good_alias_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveEvents.good_alias_bound
