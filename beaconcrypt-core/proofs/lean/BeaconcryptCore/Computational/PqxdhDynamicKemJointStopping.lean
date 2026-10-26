import BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
Stopping before an unavailable selected KEM reveal is justified for the actual complete joint identity, local-coin and KEM schedule. Fresh event probabilities retain the full joint state, source result and actual disclosure history. The global protocol freshness predicate must still imply this concrete KEM disclosure condition.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping
open PqxdhKemIndCca
open PqxdhDynamicKemJointSource (State normal)
open PqxdhDynamicKemJointRouter (stopped)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

def Good (state : State KemSK) : Prop := PqxdhDynamicKemStopping.Good state.2

def Discloses (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK) : Prop :=
  match query with
  | .inr (.inr request) => PqxdhDynamicKemStopping.Discloses selected pairs request state.2
  | _ => False

set_option backward.isDefEq.respectTransparency false in
/-- No actual combined source operation removes an earlier selected-key disclosure, including joint signing/DH, identity creation and subsequent compromise. -/
theorem normal_good (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK)
    (result : Option ((PqxdhLiveKemBirth.Spec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl primitives kem selected pairs query).run).run state))
    (good : Good result.2) : Good state := by
  rcases query with joint | (coin | query)
  all_goals simp only [normal, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  all_goals obtain ⟨reply, actual, rfl⟩ := supported
  · exact good
  · exact good
  · exact PqxdhDynamicKemStopping.normal_good baseImpl kem selected pairs query state.2 reply actual good

/-- A successful selected disclosure is precisely a KEM reveal of an already-created handle; joint identity requests and future-index guesses cannot trigger it. -/
theorem discloses_shape (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK)
    (discloses : Discloses selected pairs query state) :
    query = .inr (.inr (.reveal selected)) ∧ ∃ pair, (pairs.take state.2.created)[selected]? = some pair := by
  rcases query with joint | (coin | query)
  · exact False.elim discloses
  · exact False.elim discloses
  · obtain ⟨rfl, pair, found⟩ := PqxdhDynamicKemStopping.discloses_shape selected pairs query state.2 discloses
    exact ⟨rfl, pair, found⟩

set_option backward.isDefEq.respectTransparency false in
/-- Until the exact successful selected disclosure, the complete combined ordinary and stopped callbacks are the same computation. -/
theorem step_agree (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK)
    (allowed : ¬ Discloses selected pairs query state) :
    (((normal baseImpl primitives kem selected pairs query).run).run state) =
      (((stopped baseImpl primitives kem selected pairs query).run).run state) := by
  rcases query with joint | (coin | query)
  · rfl
  · rfl
  · exact congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
      (PqxdhDynamicKemStopping.step_agree baseImpl kem selected pairs query state.2 allowed)

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary adaptive ordinary suffix cannot restore the selected disclosure freshness monitor. -/
theorem schedule_good (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state))
    (good : Good result.2) : Good state := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, tail⟩ := supported
      apply normal_good baseImpl primitives kem selected pairs query state head actual
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
        subst result
        exact good
      · exact ih answer after result tail good

/-- Once an actual selected secret has been returned, every complete output retaining freshness has zero probability, irrespective of the adversary's final decision. -/
theorem bad_output_zero (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK)
    (result : Option Result × State KemSK) (bad : ¬ Good state) (good : Good result.2) :
    Pr{let x ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state}[x = result] = 0 :=
  prEvent_eq_zero_of_not_mem_support _ fun supported =>
    bad (schedule_good baseImpl primitives kem selected pairs client state result supported good)

set_option backward.isDefEq.respectTransparency false in
/-- Stopping before unavailable selected-secret disclosure preserves the exact probability of every complete fresh source output, not merely the adversary's marginal decision. -/
theorem output_good (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK)
    (result : Option Result × State KemSK) (good : Good result.2) :
    Pr{let x ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state}[x = result] =
      Pr{let x ← ((simulateQ (stopped baseImpl primitives kem selected pairs) client).run).run state}[
        x = result] := by
  classical
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      by_cases allowed : ¬ Discloses selected pairs query state
      · rw [step_agree baseImpl primitives kem selected pairs query state allowed]
        refine prEvent_bind_congr _ _ _ _ _ fun head => ?_
        rcases head with ⟨none | answer, after⟩
        · rfl
        · exact ih answer after
      · obtain ⟨rfl, pair, found⟩ := discloses_shape selected pairs query state (not_not.mp allowed)
        simp only [normal, stopped, PqxdhDynamicKemJointRouter.combine, PqxdhDynamicKemStopping.normal,
          PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found, ite_true, map_pure]
        rw [pure_bind, pure_bind]
        simp only [Option.elim_some, Option.elim_none]
        refine (bad_output_zero baseImpl primitives kem selected pairs (next (some pair.2))
          (state.1, PqxdhDynamicKemRouter.record (.reveal selected) (some pair.2) { state.2 with forbiddenReveal := true })
          result (by simp [Good, PqxdhDynamicKemStopping.Good, PqxdhDynamicKemRouter.record]) good).trans ?_
        symm
        refine prEvent_eq_zero_of_not_mem_support _ fun supported => ?_
        change result ∈ support (pure (none, (state.1, { state.2 with forbiddenReveal := true })) : ProbComp _) at supported
        simp only [mem_support_pure_iff] at supported
        subst result
        exact Bool.noConfusion good

/-- Every original event gated by the exact selected-disclosure monitor has identical probability in the ordinary and stopped source, with its full result and history retained. -/
theorem event_good (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK)
    (event : Option Result × State KemSK → Prop) :
    Pr{let result ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state}[
      event result ∧ Good result.2] =
      Pr{let result ← ((simulateQ (stopped baseImpl primitives kem selected pairs) client).run).run state}[
        event result ∧ Good result.2] := by
  classical
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases good : Good result.2
  · simp only [good, and_true, output_good baseImpl primitives kem selected pairs client state result good]
  · simp only [good, and_false, ↓reduceIte]


def Tracked (selected : Nat) (state : State KemSK) : Prop := PqxdhDynamicKemStopping.Tracked selected state.2

set_option backward.isDefEq.respectTransparency false in
/-- The full original combined service preserves the exact monitor derived from successful selected-secret replies in its actual private KEM history. -/
theorem normal_tracked (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK) (tracked : Tracked selected state)
    (result : Option ((PqxdhLiveKemBirth.Spec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl primitives kem selected pairs query).run).run state)) :
    Tracked selected result.2 := by
  rcases query with joint | (coin | query)
  all_goals simp only [normal, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  all_goals obtain ⟨reply, actual, rfl⟩ := supported
  · exact tracked
  · exact tracked
  · exact PqxdhDynamicKemStopping.normal_tracked baseImpl kem selected pairs query state.2 tracked reply actual

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive ordinary execution keeps the monitor equal to its actual complete successful-reveal history. -/
theorem schedule_tracked (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK) (tracked : Tracked selected state)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state)) : Tracked selected result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact tracked
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, tail⟩ := supported
      have trackedAfter := normal_tracked baseImpl primitives kem selected pairs query state tracked head actual
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
        subst result
        exact trackedAfter
      · exact ih answer after trackedAfter result tail

/-- Starting with the actual tracked history, stopping preserves every event gated by absence of an actual successful selected-key disclosure in the original history. The monitor invariant is an operational history equality, not a security premise; empty initialization and the full ordinary schedule establish it. -/
theorem history_event (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK) (trackedBefore : Tracked selected state)
    (event : Option Result × State KemSK → Prop) :
    Pr{let result ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state}[
      event result ∧ result.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) = false] =
      Pr{let result ← ((simulateQ (stopped baseImpl primitives kem selected pairs) client).run).run state}[
        event result ∧ Good result.2] := by
  classical
  calc
    _ = Pr{let result ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state}[
        event result ∧ Good result.2] := by
      refine prEvent_congr_of_support _ _ _ fun result supported => ?_
      have tracked := schedule_tracked baseImpl primitives kem selected pairs client state trackedBefore result supported
      change result.2.2.forbiddenReveal = result.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) at tracked
      simp only [Good, PqxdhDynamicKemStopping.Good, tracked]
    _ = _ := event_good baseImpl primitives kem selected pairs client state event

/-- Starting with the actual empty KEM pool, the complete joint source event is the executable prechallenge CCA event under precisely its successful-disclosure freshness condition. -/
theorem pre_event (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (joint : PqxdhDynamicIdentityPool.SourceState)
    (event : Option Result × State KemSK → Prop) :
    Pr{let result ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run
        (joint, PqxdhDynamicKemRouter.empty)}[
      event result ∧ result.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) = false] =
      Pr{let result ← PqxdhPrivateKemSource.evalKem baseImpl kem secret
          (((simulateQ (PqxdhDynamicKemJointRouter.pre primitives kem selected
            (PqxdhDynamicKemRouter.redact selected pairs)) client).run).run (joint, PqxdhDynamicKemRouter.empty))}[
        event result ∧ Good result.2] := by
  rw [PqxdhDynamicKemJointRouter.pre_program baseImpl primitives kem selected pairs target secret present]
  exact history_event baseImpl primitives kem selected pairs client (joint, PqxdhDynamicKemRouter.empty) rfl event

/-- The ordinary complete joint postchallenge history event has exactly the same probability through the blocked CCA interface on the actual real encapsulation. Every retained earlier joint/KEM field and adaptive continuation remains present. -/
theorem post_event (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (encapsulated : (challenge, candidate) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK) (tracked : Tracked selected state)
    (event : Option Result × State KemSK → Prop) :
    Pr{let result ← ((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state}[
      event result ∧ result.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) = false] =
      Pr{let result ← PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
          (((simulateQ (PqxdhDynamicKemJointRouter.post primitives kem selected
            (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate) client).run).run state)}[
        event result ∧ Good result.2] := by
  rw [PqxdhDynamicKemJointRouter.supported_post baseImpl primitives kem functional correct selected pairs target secret present generated
    challenge candidate encapsulated]
  exact history_event baseImpl primitives kem selected pairs client state tracked event

end BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.normal_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.normal_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.discloses_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.discloses_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.step_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.step_agree
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.schedule_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.bad_output_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.bad_output_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.output_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.output_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.event_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.normal_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.normal_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.schedule_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.schedule_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.history_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.history_event
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.pre_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.pre_event
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.post_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping.post_event
