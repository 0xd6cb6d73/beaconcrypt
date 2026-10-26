import BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost

/-!
The original first Server builder and every later source callback retain the adversary's final target choice. Mapping the final result commutes with the complete original sequence, retaining all role state and installation/publication metadata. These literal program laws connect adaptive final-choice observations to the existing fixed-target source theorem.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveSourceResult
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialPendingPost
variable {ι Chain M P I D K X Response Shared Result Final Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Only the final adversary result is mapped; the original builder response and complete adaptive frontend/publication state are unchanged. -/
theorem sequence_map (source : FixedHkdfSha512NoSaltSource) (initial : RustM (KernelOf Chain))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (observe : Result → Final) (before : Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) :
    (PqxdhInitialOriginPost.sequence (X := X) (Response := Response) source initial mark origin sender route decode index metadata ready
      (fun reply => observe <$> post reply)).run before =
    (fun result => (observe result.1, result.2)) <$> (PqxdhInitialOriginPost.sequence (X := X) (Response := Response)
      source initial mark origin sender route decode index metadata ready post).run before := by
  simp only [PqxdhInitialOriginPost.sequence, StateT.run, simulateQ_map, map_bind]
  apply bind_congr
  intro built
  change ((observe <$> simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (post built.1)).run _) = _
  rw [StateT.run_map]
  rfl

end BeaconcryptCore.Computational.PqxdhAdaptiveSourceResult

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveSourceResult.sequence_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveSourceResult.sequence_map
