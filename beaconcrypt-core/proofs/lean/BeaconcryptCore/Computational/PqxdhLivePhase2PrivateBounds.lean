import BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot
import BeaconcryptCore.Computational.PqxdhPhase2CcaBounds

/-!
Concrete native private-root execution retains all local callback coins, other-index primitive work and the shared raw hash cache. These syntactic bills keep every optional branch and private decapsulation observation; selected decapsulation and private-root calls are charged separately.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds
open PqxdhLivePhase2PrivateRoot PqxdhKemIndCca PqxdhJointIdentity PqxdhJointKdfGame
open PqxdhPrivateKemSource PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhLivePhase2Aux (Identity LocalSpec)
open PqxdhPhase2DecapsulationRouting (Shared)
variable {ι KemSK D A Response : Type} {baseSpec : OracleSpec ι}

/-- Every real auxiliary callback pays its source coins, shared raw hash or complete other-index primitive program. -/
theorem auxiliary_uniform (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PqxdhLiveKemRouting.PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (qLocal uDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (decapBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (query : (AuxSpec selected D Response).Domain) (state : AuxState A) :
    ((auxiliary primitives kem selected keys source callbacks query).run state).IsQueryBoundP
      IsMlKemUniformQuery (max (max qLocal 64) uDecap) := by
  cases query with
  | localDecapsulation ciphertext handle =>
    simpa only [auxiliary, StateT.run, isQueryBoundP_map_iff] using
      (other_queries kem selected keys handle (PqxdhPhase2InputBytes.ciphertext ciphertext)
        IsMlKemUniformQuery uDecap (fun secret => decapBound secret _)).mono (Nat.le_max_right _ _)
  | privateConversion identity => trivial
  | initial request => trivial
  | dhIdentity identity peer =>
    apply PqxdhPrivateRootQueryBounds.ccaCoins_uniform
    trivial
  | raw request =>
    apply PqxdhPrivateRootQueryBounds.ccaCoins_uniform
    simpa only [PqxdhPhase2SourceAux.rawRun, IsTotalQueryBound, isQueryBound_map_iff] using
      (PqxdhPhase2SourceAux.raw_uniform source request state.1).mono
        (le_trans (Nat.le_max_right qLocal 64) (Nat.le_max_left _ _))
  | _ =>
    apply PqxdhPrivateRootQueryBounds.ccaCoins_uniform
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      (localBound _ state.1.1).mono (le_trans (Nat.le_max_left qLocal 64) (Nat.le_max_left _ _))


/-- Base requests come only from the actual other-index primitive program; source coins and public fixed HKDF use their own interfaces. -/
theorem auxiliary_base (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PqxdhLiveKemRouting.PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (bDecap : Nat)
    (decapBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (query : (AuxSpec selected D Response).Domain) (state : AuxState A) :
    ((auxiliary primitives kem selected keys source callbacks query).run state).IsQueryBoundP
      IsMlKemBaseQuery bDecap := by
  cases query with
  | localDecapsulation ciphertext handle =>
    simpa only [auxiliary, StateT.run, isQueryBoundP_map_iff] using
      other_queries kem selected keys handle (PqxdhPhase2InputBytes.ciphertext ciphertext)
        IsMlKemBaseQuery bDecap (fun secret => decapBound secret _)
  | privateConversion identity => trivial
  | initial request => trivial
  | _ => exact (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ IsMlKemBaseQuery
      (fun _ => by simp [IsMlKemBaseQuery])).mono (Nat.zero_le _)


/-- The complete concrete native owner, including its private attempt history, has at most one selected decapsulation and one private root. Every other primitive and local callback is charged. -/
theorem private_owner_classes (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PqxdhLiveKemRouting.PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (qLocal uDecap bDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (uniformBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (baseBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (challenge : MlKem768Ciphertext) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (state : AuxState A × List (DecapsulationEvent Shared)) :
    PostBounds (privateOwner primitives kem selected keys source callbacks challenge read raw owner state)
      (69 * max (max qLocal 64) uDecap) (69 * bDecap) 1 1 := by
  have clean := PqxdhBeaconPhase2RoutedBounds.owner_classes source challenge
    (auxiliary primitives kem selected keys source callbacks) (max (max qLocal 64) uDecap) bDecap 0
    (auxiliary_uniform primitives kem selected keys source callbacks qLocal uDecap localBound uniformBound)
    (auxiliary_base primitives kem selected keys source callbacks bDecap baseBound)
    (auxiliary_no_selected primitives kem selected keys source callbacks) read raw owner state.1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rw [privateOwner, logged_queries]
  · exact clean.uniforms
  · exact clean.bases
  · simpa only [Nat.mul_zero, Nat.zero_add] using clean.decaps
  · exact clean.privateRoots


/-- Ordinary CCA routing preserves the exact query bill after erasing only added private instrumentation. This is equality of complete programs, not a claim about marginal output distributions. -/
theorem ordinary_owner_queries (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PqxdhLiveKemRouting.PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (state : AuxState A × List (DecapsulationEvent Shared))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (simulateQ (route source challenge supplied)
      (privateOwner primitives kem selected keys source callbacks challenge read raw owner state)).IsQueryBoundP predicate budget ↔
    (simulateQ (route source challenge supplied)
      ((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
        (auxiliary primitives kem selected keys source callbacks))
        (PqxdhBeaconPhase2Shared.owner read raw owner)).run state.1)).IsQueryBoundP predicate budget := by
  have kept := congrArg (simulateQ (route source challenge supplied))
    (privateOwner_erase primitives kem selected keys source callbacks challenge read raw owner state)
  rw [simulateQ_map] at kept
  rw [← kept, isQueryBoundP_map_iff]


/-- The ordinary one-key interpreter retains the same source callback and other-key bills, with at most one permitted selected decapsulation. Private root evaluation adds no oracle request. -/
theorem ordinary_owner_classes (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PqxdhLiveKemRouting.PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (qLocal uDecap bDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (uniformBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (baseBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (state : AuxState A × List (DecapsulationEvent Shared)) :
    let work := simulateQ (route source challenge supplied)
      (privateOwner primitives kem selected keys source callbacks challenge read raw owner state)
    work.IsQueryBoundP IsMlKemUniformQuery (69 * max (max qLocal 64) uDecap) ∧
      work.IsQueryBoundP IsMlKemBaseQuery (69 * bDecap) ∧
      work.IsQueryBoundP IsMlKemLogicalDecapsulationQuery 1 := by
  dsimp only
  simp only [ordinary_owner_queries]
  simpa only [Nat.mul_zero, Nat.zero_add] using
    PqxdhPhase2CcaBounds.owner_classes source challenge supplied
      (auxiliary primitives kem selected keys source callbacks) (max (max qLocal 64) uDecap) bDecap 0
      (auxiliary_uniform primitives kem selected keys source callbacks qLocal uDecap localBound uniformBound)
      (auxiliary_base primitives kem selected keys source callbacks bDecap baseBound)
      (auxiliary_no_selected primitives kem selected keys source callbacks) read raw owner state.1

end BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.auxiliary_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.auxiliary_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.auxiliary_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.auxiliary_base

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.private_owner_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.private_owner_classes

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.ordinary_owner_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.ordinary_owner_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.ordinary_owner_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds.ordinary_owner_classes
