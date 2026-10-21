import BeaconcryptCore.Computational.PqxdhInitialRootEventBounds

/-!
The authenticated root reduction is instantiated with the executable source continuation that tests actual publication and freshness. The same complete preparation includes honest unchanged, changed, attacker-owned and rejected candidates. Its uniform-root endpoint is exactly the prepared source sampler used by the initial64 and evolving-chain reductions, including completed branches.

This is a fixed selected-owner and record-position experiment. No caller supplies a final-event equality, root-query cap or continuation simulation. Resource premises describe original source callers and primitive/local callbacks; the concrete root client and every indexed HMAC bill are derived. The joint identity contract covers Ed25519/X25519 correlated use, and ordinary KEM correctness remains an explicit error term.
-/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy
open PqxdhJointKdf
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhPrivateAcceptedRoot
open PqxdhAuthenticatedRootExperiment (Post)
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

noncomputable def accepted (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) : OracleComp (LocalPostSpec baseSpec) Bool :=
  PqxdhInitialRootEventAccepted.target env attachedVerify primitives program post prepared ready selected number ancestors disclosed

noncomputable def actual : ProbComp Bool :=
  PqxdhInitialRootEventExperiment.actual env baseImpl kem attachedVerify primitives program post
    (accepted env attachedVerify primitives program post selected number ancestors disclosed)

/-- The authenticated-root endpoint uses precisely the concrete source-event protocol, not a second sampler chosen by an equality hypothesis. -/
theorem protocol_source :
    PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post
      (accepted env attachedVerify primitives program post selected number ancestors disclosed) =
    PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed := by
  unfold PqxdhInitialRootEventExperiment.protocol PqxdhInitialRootEventAccepted.protocol accepted
  dsimp only
  congr 1
  funext key ciphertext mode root
  cases mode with
  | completed decision => rfl
  | pending prepared ephemeral => cases root <;> rfl

variable (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (qPost : Nat) (postTotal : ∀ choice reply, (post choice reply).IsTotalQueryBound qPost)

noncomputable def loss (hmac : HmacSha512) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) : ℝ :=
  let p := PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
  (PqxdhJointIdentity.advantage primitives
    (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
      (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
  Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
  kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
    (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
  PqxdhCorrelatedExtractFamily.advantage hmac
    (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
  ∑ index ∈ Finset.range (1 + (7 + qPost * 67)),
    (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
      (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))

include c postTotal
/-- The source publication/freshness event reaches the identical prepared uniform-root experiment with explicit authentication, KEM, Extract and HMAC terms and a source-derived root cap. -/
theorem bound
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (actual env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed).boolDistAdvantage
      (PqxdhInitialPreparedSourceInput.uniformRoot env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) ≤
    loss env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed qPost hmac fallback ordinaryFallback := by
  have rootBound := (PqxdhInitialRootEventBounds.reduction_bounds attachedVerify primitives env baseImpl kem program post
    c qPost postTotal selected number ancestors disclosed).2
  have genericRootBound :
      (rootReduction env.source baseImpl kem
        (PqxdhInitialRootEventExperiment.protocol env kem attachedVerify primitives program post
          (accepted env attachedVerify primitives program post selected number ancestors disclosed))).IsQueryBoundP
        IsRoot (1 + (7 + qPost * 67)) := by
    rw [protocol_source]
    exact rootBound
  have result := PqxdhInitialRootEventComposition.authenticated_root_bound env baseImpl kem attachedVerify primitives program post
    (accepted env attachedVerify primitives program post selected number ancestors disclosed)
    compatible adapter functional hmac sourceCorrect c.noSign c.noCreate fallback ordinaryFallback
    (1 + (7 + qPost * 67)) genericRootBound
  have endpoint := PqxdhInitialRootEventAccepted.uniform_source env attachedVerify primitives program post baseImpl kem selected number ancestors disclosed
  simpa only [actual, loss, protocol_source, ProbComp.boolDistAdvantage, endpoint] using result

end BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy.protocol_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy.protocol_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy.bound
