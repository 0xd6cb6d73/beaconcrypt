import BeaconcryptCore.Computational.PqxdhPhase2PreChallenge
import BeaconcryptCore.Computational.PqxdhPhase2SourceAux

/-!
The actual Phase2 compiler can be defined over the public identity/CCA source interface before identity or KEM generation. Borrowing the later identity interpreter retains its complete history and gives exactly the existing ordinary prechallenge compiler. The source program has no identity seed, KEM secret, or freshly sampled private interpreter state argument.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2Selector
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhGeneratedBeaconState (IdentityHandle)
open PqxdhPhase2JointIdentity (Converted)
open PqxdhRootTableInitialization (rootArray)
variable {ι I D K X Response A : Type} {baseSpec : OracleSpec ι}

/-- This executable source compiler is fixed before fresh private generation. -/
noncomputable def sourcePre
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D (Option K) (X ⊕ Converted) Response)
      (StateT (SharedState A) (OracleComp (SelectorSpec baseSpec)))
  | .inl (.decode raw) => sourceAux source localImpl (.decode raw)
  | .inl (.ciphertext response) => sourceAux source localImpl (.ciphertext response)
  | .inl (.ephemeral response) => sourceAux source localImpl (.ephemeral response)
  | .inl (.serverIdentity response) => sourceAux source localImpl (.serverIdentity response)
  | .inl (.publicConversion value) => sourceAux source localImpl (.publicConversion value)
  | .inl (.privateConversion identity) => sourceAux source localImpl (.privateConversion identity)
  | .inl (.decapsulate value none) => StateT.mk fun state =>
      (fun reply => (Option.map rootArray reply, state)) <$>
        (((SelectorSpec baseSpec).query (.inr (.inr (PqxdhPhase2InputBytes.ciphertext value)))) :
          OracleComp (SelectorSpec baseSpec) (Option MlKemSharedSecret))
  | .inl (.decapsulate value (some prior)) => sourceAux source localImpl (.localDecapsulation value prior)
  | .inl (.dhPair pair value) => sourceAux source localImpl (.dhPair pair value)
  | .inl (.dhIdentity identity value) => sourceAux source localImpl (.dhIdentity identity value)
  | .inl (.assignedId response) => sourceAux source localImpl (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => sourceAux source localImpl (.raw query)
  | .inr (.inr (.root input)) => pure (some (RawCtxSourceHkdf.rootResponse source.crypto input))
  | .inr (.inr (.initial request)) => sourceAux source localImpl (.initial request)
  | .inr (.inr (.application response)) => sourceAux source localImpl (.application response)


/-- The later borrowed interpreter changes only state layout and realizes every original source callback. -/
theorem borrowed_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D (Option K) (X ⊕ Converted) Response).Domain)
    (state : SharedState A × BareState count) :
    ((((borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count).mapStateTBase
      (sourcePre source localImpl)).flattenStateT query).run state) =
      ((PqxdhPhase2PreChallenge.pre source
        (borrowedAux attachedVerify primitives count source localImpl) query).run state) := by
  rcases query with (query | (query | query)) <;> cases query <;> try rfl
  case inl.decapsulate value key =>
    cases key with
    | some prior => rfl
    | none =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, sourcePre,
        StateT.run_mk, simulateQ_map, StateT.run_map]
      have forwarded := congrArg (fun action =>
        (fun result => (Option.map rootArray result.1, (state.1, result.2))) <$> action.run state.2)
        (simulateQ_spec_query (borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count)
          (.inr (.inr (PqxdhPhase2InputBytes.ciphertext value))))
      change _ = (fun reply => (reply, state)) <$> (Option.map rootArray <$>
        (((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext value))) :
          OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret)))
      simp only [Functor.map_map, borrowedSelector, StateT.run, bind_pure_comp, Prod.mk.eta] at forwarded ⊢
      exact forwarded

/-- The private identity interpreter is installed after the source compiler has been fixed. -/
theorem borrowed_interpretation
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    ((borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count).mapStateTBase
      (sourcePre source localImpl)).flattenStateT =
      PqxdhPhase2PreChallenge.pre source (borrowedAux attachedVerify primitives count source localImpl) := by
  funext query state
  exact borrowed_step attachedVerify primitives count source localImpl query state

/-- The exact full source continuation is interpreted after its original local execution, retaining both entire private poststates. -/
theorem borrowed_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D
      (Option K) (X ⊕ Converted) Response) Result)
    (state : SharedState A) (identities : BareState count) :
    (simulateQ (borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count)
      ((simulateQ (sourcePre source localImpl) client).run state)).run identities =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (PqxdhPhase2PreChallenge.pre source
          (borrowedAux attachedVerify primitives count source localImpl)) client).run (state, identities) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, borrowed_interpretation]

end BeaconcryptCore.Computational.PqxdhPhase2Selector

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2Selector.borrowed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2Selector.borrowed_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2Selector.borrowed_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2Selector.borrowed_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2Selector.borrowed_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2Selector.borrowed_complete
