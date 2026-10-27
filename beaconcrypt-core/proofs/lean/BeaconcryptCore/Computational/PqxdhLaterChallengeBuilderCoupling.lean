import BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling

/-! Lift the complete source-prefix coupling through the actual initial Builder, with its full result, callback descriptor and native state retained. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling
open PqxdhFirstRecordConfidentiality PqxdhInitialBuilderContext PqxdhInitialPostContext
open PqxdhLaterChallengeCapture PqxdhLaterChallengeBuilderCapture RawCtxForwardScan
variable {ι M P I D K X Response Shared Origin Local : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Outcome := Cut
  (PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Option (Details extra M P I D K Origin S B))
  (Bool × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) Local

/-- Mark a wrapper cut without changing its complete frontend, trace or native state. -/
def liftCut := @cutMap (Capture extra M P I D K Origin S B)
  (PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Option (Details extra M P I D K Origin S B))
  (Bool × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) Local
  (fun tag => (tag.1, some tag.2))

/-- The initial Builder callback is shared; each world appends its literal adversary wrapper. -/
noncomputable def tagged (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (callback : PqxdhInitialOriginContext.Context extra M P I D K BuildResult Origin S B) :=
  (append (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial) callback,
    (none : Option (Details extra M P I D K Origin S B)))

/-- The paired complete runs either share the initial Builder cut, or retain the full paired wrapper outcomes. The latter includes every completed and post-admission execution. -/
noncomputable def Related (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (adversary : BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (left right : Outcome (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B)) : Prop :=
  (∃ callback state, left = .pending (tagged owner number first adversary callback) state ∧
    right = .pending (tagged owner number second adversary callback) state) ∨
  ∃ firstCut secondCut, left = liftCut firstCut ∧ right = liftCut secondCut ∧
    PqxdhLaterChallengeScanCoupling.Related owner number first second firstCut secondCut

variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)

/-- The original actual Builder and wrapper scan with optional request metadata. -/
noncomputable def run (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (AdvSpec extra S B) Bool) (state : Local) :=
  scan PqxdhInitialForwardPost.selected chosen selection impl
    (capturedBuilder mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
    (builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary) state

/-- Factor the complete evaluated source scan at the actual initial Builder result, without imposing success or discarding its pending branch. -/
theorem run_builder (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (AdvSpec extra S B) Bool) (state : Local) :
    run mark origin sender route read index before trace source initial metadata ready impl chosen selection owner number bit adversary state =
      (scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready pure before trace)
        (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route read initial index metadata ready pure before trace) state >>= fun cut =>
          match cut with
          | .complete reply ambient => liftCut <$>
              PqxdhLaterChallengeScanCoupling.run mark sender route read impl chosen selection owner number bit
                (adversary reply.1) PqxdhRecordConfidentialityChallenge.initial reply.2.1 reply.2.2 ambient
          | .pending callback ambient => pure (.pending (tagged owner number bit adversary callback) ambient)) := by
  let liftTag := tagged (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) owner number bit adversary
  have baseCovered := PqxdhInitialOriginForwardBuilder.program_covered (X := X) (Response := Response) source mark origin sender route read
    initial index metadata ready (pure : BuildResult → OracleComp (PostSpec extra S B) BuildResult) before trace
  have headCovered := (covered_tags liftTag PqxdhInitialForwardPost.selected _).mpr baseCovered
  have following := fun reply : BuildResult × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) => (covered_tags (fun tag => (tag.1, some tag.2)) PqxdhInitialForwardPost.selected _).mpr
    (captured_covered (X := X) (Response := Response) mark sender route read owner number bit (adversary reply.1)
      PqxdhRecordConfidentialityChallenge.initial reply.2.1 reply.2.2)
  unfold run capturedBuilder
  change scan _ _ _ _ (RawCtxForwardAnnotation.mapTags liftTag
    (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready pure before trace) >>=
    fun reply => RawCtxForwardAnnotation.mapTags (fun tag => (tag.1, some tag.2))
      (captured mark sender route read owner number bit (adversary reply.1) PqxdhRecordConfidentialityChallenge.initial reply.2.1 reply.2.2)) _ state = _
  rw [PqxdhLaterChallengeCutChronology.native_bind PqxdhInitialForwardPost.selected chosen selection impl _ _ headCovered following
    (builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary) state]
  rw [← native_scan_tags liftTag PqxdhInitialForwardPost.selected chosen selection impl _ baseCovered state, bind_map_left]
  refine bind_congr fun cut => ?_
  cases cut with
  | complete reply ambient =>
      exact (native_scan_tags (fun tag => (tag.1, some tag.2)) PqxdhInitialForwardPost.selected chosen selection impl _
        (captured_covered mark sender route read owner number bit (adversary reply.1)
          PqxdhRecordConfidentialityChallenge.initial reply.2.1 reply.2.2) ambient).symm
  | pending callback ambient => rfl

/-- The full original initial Builder and adaptive source wrapper are coupled without conditioning on a selected cut or successful Builder reply. Every native state and actual callback remains in the paired outputs. -/
theorem coupled (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (adversary : BuildResult → OracleComp (AdvSpec extra S B) Bool) (state : Local) :
    RelTriple (run mark origin sender route read index before trace source initial metadata ready impl chosen selection owner number first adversary state)
      (run mark origin sender route read index before trace source initial metadata ready impl chosen selection owner number second adversary state)
      (Related owner number first second adversary) := by
  rw [run_builder, run_builder]
  refine relTriple_bind (relTriple_refl _) ?_
  rintro cut _ rfl
  cases cut with
  | complete reply ambient =>
      apply relTriple_map
      exact relTriple_post_mono (PqxdhLaterChallengeScanCoupling.coupled mark sender route read impl chosen selection
        owner number first second (adversary reply.1) PqxdhRecordConfidentialityChallenge.initial reply.2.1 reply.2.2 ambient rfl)
        (fun left right related => Or.inr ⟨left, right, rfl, rfl, related⟩)
  | pending callback ambient => exact relTriple_pure_pure (Or.inl ⟨callback, ambient, rfl, rfl⟩)

end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling.run_builder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling.run_builder

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling.coupled
