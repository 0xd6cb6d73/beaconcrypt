-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills

/-! Query bills of the raw-ordinal KEM adversary. `AcceptKemCut.exposeAt` interprets every encapsulation other than the selected one in place, so its hidden encapsulations are charged to the uniform component, and the exposed-encapsulation component counts the single selected hook; after the challenge cut no exposed encapsulation remains. The resulting prechallenge and postchallenge caps are exactly those of `KemReductionBills.adversary_bound`. No existing theorem is modified. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (forward actual commands)
open PqxdhRegistrationJointKemCommands (SourceSpec Budget)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemCutBounds (Count Residual)
open PqxdhRegistrationJointKemCutSupport (ContextBound)
open PqxdhRegistrationJointKemExposedCounts (IsEncapsulation)
open PqxdhRegistrationJointKemProgramBills (Bounds)
open PqxdhRegistrationJointKemPostBills (uniformCap CcaBills)
open PqxdhRegistrationJointKemRawChallenge (preRaw rawScan)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhDynamicKemJointBounds (IsIdentityCreate IsDecapsulation IsUniform)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R Result Next : Type}

/-- `Hides setup hidden exposed`: `hidden` is `exposed` with some of its exposed encapsulation requests interpreted in place by the actual encapsulator, and every other request kept in place. -/
inductive Hides (setup : Setup baseSpec KemSK) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result → Prop
  | pure (result : Result) : Hides setup (pure result) (pure result)
  | keep (query : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Domain)
      (hidden exposed : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Range query →
        OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
      (rest : ∀ answer, Hides setup (hidden answer) (exposed answer)) :
      Hides setup ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query query >>= hidden)
        ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query query >>= exposed)
  | hide (request : PqxdhRegistrationJointKemCut.Request)
      (hidden exposed : PqxdhRegistrationJointKemCut.Reply →
        OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
      (rest : ∀ answer, Hides setup (hidden answer) (exposed answer)) :
      Hides setup (simulateQ forward (actual setup (.inr request)) >>= hidden)
        ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inr request) >>= exposed)

/-- Every program hides nothing of itself. -/
theorem hides_refl (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) : Hides setup work work := by
  induction work using OracleComp.inductionOn with
  | pure result => exact .pure result
  | query_bind query next ih => exact .keep query next next ih

/-- `AcceptKemCut.hide` hides every exposed encapsulation of a program. -/
theorem hides_all (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    Hides setup (PqxdhRegistrationJointAcceptKemCut.hide setup work) work := by
  induction work using OracleComp.inductionOn with
  | pure result => exact .pure result
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [PqxdhRegistrationJointAcceptKemCut.hide, simulateQ_bind, simulateQ_spec_query, actual] at ih ⊢
      exact .keep (.inl query) _ next ih
    | inr request =>
      simp only [PqxdhRegistrationJointAcceptKemCut.hide, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      exact .hide request _ next ih

/-- Hiding is compatible with sequential composition. -/
theorem hides_bind (setup : Setup baseSpec KemSK)
    {hidden exposed : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result}
    {hiddenNext exposedNext : Result → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Next}
    (first : Hides setup hidden exposed) (rest : ∀ result, Hides setup (hiddenNext result) (exposedNext result)) :
    Hides setup (hidden >>= hiddenNext) (exposed >>= exposedNext) := by
  induction first with
  | pure result => simpa only [pure_bind] using rest result
  | keep query hidden exposed _ ih =>
    simp only [bind_assoc]
    exact .keep query _ _ ih
  | hide request hidden exposed _ ih =>
    simp only [bind_assoc]
    exact .hide request _ _ ih

/-- Bound transfer: if the exposed program has at most `n` requests of a private class and at most `h` exposed encapsulations, and each actual encapsulation has at most `c` requests of that class, then the hiding program has at most `n + c * h` requests of that class. -/
theorem hides_bound (setup : Setup baseSpec KemSK)
    (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate]
    {hidden exposed : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result}
    (hides : Hides setup hidden exposed) (n h c : Nat)
    (bounded : exposed.IsQueryBoundP (Count (KemSK := KemSK) predicate) n)
    (encapsulations : exposed.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) h)
    (primitive : ∀ request, (actual setup (.inr request)).IsQueryBoundP predicate c) :
    hidden.IsQueryBoundP (Count (KemSK := KemSK) predicate) (n + c * h) := by
  induction hides generalizing n h with
  | pure result => trivial
  | keep query hidden exposed _ ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded encapsulations ⊢
    cases query with
    | inl query =>
      have plain : ¬ IsEncapsulation (KemSK := KemSK) (.inl query) := fun absurd => absurd
      refine ⟨bounded.1.imp_right (fun positive => by omega), fun answer => ?_⟩
      have rest := ih answer _ h (bounded.2 answer)
        (by simpa only [ite_eq_right plain] using encapsulations.2 answer)
      apply rest.mono
      by_cases counted : Count (KemSK := KemSK) predicate (.inl query)
      · have positive : 0 < n := bounded.1.resolve_left (not_not.mpr counted)
        rw [ite_eq_left counted, ite_eq_left counted]
        omega
      · rw [ite_eq_right counted, ite_eq_right counted]
    | inr request =>
      have uncounted : ¬ Count (KemSK := KemSK) predicate (.inr request) := fun absurd => absurd
      have hook : IsEncapsulation (KemSK := KemSK) (.inr request) := trivial
      have positive : 0 < h := encapsulations.1.resolve_left (not_not.mpr hook)
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      refine ⟨Or.inl uncounted, fun answer => ?_⟩
      have rest := ih answer n remaining (by simpa only [ite_eq_right uncounted] using bounded.2 answer)
        (by simpa only [ite_eq_left hook, Nat.add_one_sub_one] using encapsulations.2 answer)
      rw [ite_eq_right uncounted]
      apply rest.mono
      rw [Nat.mul_succ]
      omega
  | hide request hidden exposed _ ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded encapsulations
    have uncounted : ¬ Count (KemSK := KemSK) predicate (.inr request) := fun absurd => absurd
    have hook : IsEncapsulation (KemSK := KemSK) (.inr request) := trivial
    have positive : 0 < h := encapsulations.1.resolve_left (not_not.mpr hook)
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    have total := isQueryBoundP_bind
      (PqxdhRegistrationJointKemExposedCounts.forward_bound _ (Count (KemSK := KemSK) predicate) c (primitive request))
      (fun answer _ => ih answer n remaining (by simpa only [ite_eq_right uncounted] using bounded.2 answer)
        (by simpa only [ite_eq_left hook, Nat.add_one_sub_one] using encapsulations.2 answer))
    apply total.mono
    rw [Nat.mul_succ]
    omega

/-- `exposeAt` hides every encapsulation of the fully exposed command compiler on the tagged client except the selected one. -/
theorem exposeAt_hides (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    Hides setup
      (PqxdhRegistrationJointAcceptKemCut.exposeAt setup codec checks identityIndex publicIdentity observe work
        index owners state)
      (commands setup codec checks identityIndex publicIdentity
        (observe <$> PqxdhRegistrationJointAcceptCutTag.tag work index) owners state) := by
  rw [PqxdhRegistrationJointAcceptCutTag.tag, map_bind, PqxdhRegistrationJointAcceptCutSource.commands_bind]
  unfold PqxdhRegistrationJointAcceptKemCut.exposeAt
  apply hides_bind setup (hides_all setup _)
  rintro ⟨⟨cut, after⟩, native⟩
  cases cut with
  | complete result =>
    have same : commands setup codec checks identityIndex publicIdentity
        (observe <$> PqxdhRegistrationJointAcceptCutTag.tagFinish (.complete result)) after native =
        pure ((observe (result, none), after), native) := by
      simp [PqxdhRegistrationJointAcceptCutTag.tagFinish, commands]
    dsimp only
    rw [same]
    exact .pure _
  | pending raw next =>
    have finish : observe <$> PqxdhRegistrationJointAcceptCutTag.tagFinish (.pending raw next) =
        PqxdhRegistrationJointAcceptCut.finish (.pending raw (PqxdhRegistrationJointAcceptKemCut.tagged observe raw next)) := by
      simp only [PqxdhRegistrationJointAcceptCutTag.tagFinish, PqxdhRegistrationJointAcceptCut.finish,
        map_bind, Functor.map_map]
      rfl
    dsimp only
    rw [finish, PqxdhRegistrationJointAcceptCutSource.pending_command]
    exact hides_bind setup (hides_refl setup _) (fun answer => hides_all setup _)

/-- The four exposed-program allowances of `exposeAt`: generated identity requests and logical decapsulations within the source caps, all uniform work within the existing native allowance plus one actual encapsulation per raw accept for the hidden encapsulations, and at most one exposed encapsulation. -/
theorem exposeAt_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK) :
    Bounds (PqxdhRegistrationJointAcceptKemCut.exposeAt setup codec checks identityIndex publicIdentity observe work
        index owners state)
      (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) 1 := by
  have tagged : ∀ source, (observe <$> PqxdhRegistrationJointAcceptCutTag.tag work index).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source) :=
    fun source => (isQueryBoundP_map_iff _ _ _).mpr
      (PqxdhRegistrationJointAcceptCutTag.tag_bound work index _ _ (certified source))
  have exposed := PqxdhRegistrationJointKemProgramBills.commands setup codec checks caps bounded identityIndex
    publicIdentity _ budget tagged owners state
  have hides := exposeAt_hides setup codec checks identityIndex publicIdentity observe work index owners state
  constructor
  · have result := hides_bound setup
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .identityCreate) hides _ _ 0
      (by simpa only [PqxdhRegistrationJointKemProgramBills.creates_class] using exposed.creates) exposed.encaps
      (fun request => PqxdhRegistrationJointKemCutInterpreted.encaps_private setup request .identityCreate (by decide))
    simpa only [PqxdhRegistrationJointKemProgramBills.creates_class, Nat.zero_mul, Nat.add_zero] using result
  · have result := hides_bound setup
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .decapsulate) hides _ _ 0
      (by simpa only [PqxdhRegistrationJointKemProgramBills.decaps_class] using exposed.decaps) exposed.encaps
      (fun request => PqxdhRegistrationJointKemCutInterpreted.encaps_private setup request .decapsulate (by decide))
    simpa only [PqxdhRegistrationJointKemProgramBills.decaps_class, Nat.zero_mul, Nat.add_zero] using result
  · exact hides_bound setup _ hides _ _ _ exposed.uniform exposed.encaps
      (PqxdhRegistrationJointKemCutInterpreted.encaps_uniform setup caps bounded)
  · exact PqxdhRegistrationJointAcceptKemCut.exposeAt_bound setup codec checks identityIndex publicIdentity observe
      work index owners state

/-- A reached pending KEM cut leaves at most `cap - 1` exposed encapsulations in its saved continuation, for every reply: the cut itself is one exposed encapsulation. -/
theorem residual_hook (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) (index cap : Nat)
    (bounded : work.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) cap)
    (cut : PqxdhRegistrationJointKemCut.Cut KemSK Result)
    (reached : cut ∈ support (PqxdhRegistrationJointKemCut.scan setup work index)) :
    Residual (IsEncapsulation (KemSK := KemSK)) (cap - 1) cut := by
  induction work using OracleComp.inductionOn generalizing index cut cap with
  | pure result =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl query =>
      rw [PqxdhRegistrationJointKemCut.scan_other, mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      have plain : ¬ IsEncapsulation (KemSK := KemSK) (.inl query) := fun absurd => absurd
      exact ih answer index cap (by simpa only [ite_eq_right plain] using bounded.2 answer) cut reached
    | inr request =>
      cases index with
      | zero =>
        rw [PqxdhRegistrationJointKemCut.scan_target] at reached
        obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
        have hook : IsEncapsulation (KemSK := KemSK) (.inr request) := trivial
        exact fun reply => by simpa only [ite_eq_left hook] using bounded.2 reply
      | succ index =>
        rw [PqxdhRegistrationJointKemCut.scan_prior, mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        exact ih answer index cap ((bounded.2 answer).mono (by split_ifs <;> omega)) cut reached

/-- The executable raw-ordinal prephase supplies the saved all-reply continuation allowance of every residual fact of its scanned program, independently of the challenge key and of every oracle reply. -/
theorem preRaw_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (challengeKey : MlKem768PublicKey)
    (predicate : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat)
    (residual : ∀ created : PqxdhRegistrationJointServerBirth.ClientCreated Unit, ∀ cut,
      cut ∈ support (rawScan setup codec checks decision work index created) → Residual predicate cap cut)
    (context : Context KemSK A Bool count)
    (reached : context ∈ support
      (preRaw setup codec checks ensureInit supplied decision work runtime count selected index challengeKey)) :
    ContextBound predicate cap context := by
  unfold preRaw at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨⟨born, after⟩, _, reached⟩ := reached
  cases born with
  | none =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    trivial
  | some created =>
    rw [mem_support_bind_iff] at reached
    obtain ⟨others, _, reached⟩ := reached
    rw [mem_support_bind_iff] at reached
    obtain ⟨⟨cut, state⟩, scanned, reached⟩ := reached
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    cases cut with
    | none => trivial
    | some cut =>
      exact residual created cut (PqxdhRegistrationJointKemCutSupport.successful_support _ _ _ state cut scanned)

/-- Every valid saved raw-ordinal context has all four source-derived continuation certificates: generated identity requests, logical decapsulations and uniform work within the `exposeAt` allowances, and no exposed encapsulation left after the challenge cut. -/
theorem saved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (context : PqxdhRegistrationJointKemRawCertified.Saved setup codec checks ensureInit supplied decision work
      runtime count selected index) :
    PqxdhRegistrationJointKemSavedBills.Certificate context.2.val (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) 0 := by
  have bills (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :=
    exposeAt_bills setup codec checks caps bounded created.server.server.metadata.identityIndex
      created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) work budget certified index []
      (PqxdhRegistrationJointInitializedAccept.initial created)
  constructor
  · exact preRaw_bound setup codec checks ensureInit supplied decision work runtime count selected index context.1
      _ _ (fun created cut reached => PqxdhRegistrationJointKemCutBounds.residual setup _ 0 _ _
        (bills created).creates cut reached) context.2.val context.2.property
  · exact preRaw_bound setup codec checks ensureInit supplied decision work runtime count selected index context.1
      _ _ (fun created cut reached => PqxdhRegistrationJointKemCutBounds.residual setup _ 0 _ _
        (bills created).decaps cut reached) context.2.val context.2.property
  · exact preRaw_bound setup codec checks ensureInit supplied decision work runtime count selected index context.1
      _ _ (fun created cut reached => PqxdhRegistrationJointKemCutBounds.residual setup _ 0 _ _
        (bills created).uniform cut reached) context.2.val context.2.property
  · exact preRaw_bound setup codec checks ensureInit supplied decision work runtime count selected index context.1
      _ _ (fun created cut reached => residual_hook setup _ 0 1 (bills created).encaps cut reached)
      context.2.val context.2.property

/-- The postchallenge uniform allowance with every hidden encapsulation charged to the uniform component and no exposed encapsulation left is exactly the allowance of the encapsulation-ordinal adversary. -/
theorem uniform_cap (caps : KemCaps) (qCreate qD qUniform qEncap : Nat) :
    uniformCap caps qCreate qD (qUniform + caps.encapsCost * qEncap) 0 = uniformCap caps qCreate qD qUniform qEncap := by
  simp only [uniformCap, Nat.mul_zero, Nat.add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Every postchallenge context of the proof-carrying raw-ordinal adversary has the same explicit source-derived caps as the encapsulation-ordinal adversary, for arbitrary challenge keys, ciphertexts and candidate secrets. -/
theorem adversary_post (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (transcript : MlKemChallengeTranscript
      (PqxdhRegistrationJointKemRawCertified.Saved setup codec checks ensureInit supplied decision work runtime count
        selected index))
    (candidate : MlKemSharedSecret) :
    CcaBills ((PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work
        runtime count selected index).postChallenge transcript candidate)
      (uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) := by
  have bill := PqxdhRegistrationJointKemPostBills.post_bound setup caps bounded count selected transcript.context.2.val
    transcript.publicKey transcript.ciphertext candidate _ _ _ _
    (saved setup codec checks caps bounded ensureInit supplied decision work runtime count selected index budget
      certified transcript.context)
  rw [uniform_cap] at bill
  constructor
  · simpa only [PqxdhRegistrationJointKemRawCertified.adversary, isQueryBoundP_map_iff] using bill.uniform
  · simpa only [PqxdhRegistrationJointKemRawCertified.adversary, isQueryBoundP_map_iff] using bill.base
  · simpa only [PqxdhRegistrationJointKemRawCertified.adversary, isQueryBoundP_map_iff] using bill.decaps

/-- The raw-ordinal KEM scan inherits every private request cap of the actual source command program of the decision client, and its uniform cap pays every actual encapsulation in addition to the native allowance. -/
theorem scan_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (index : Nat) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :
    PqxdhRegistrationJointKemCutInterpreted.Bills (rawScan setup codec checks decision work index created)
      (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) := by
  have tagged : ∀ source, (PqxdhRegistrationJointAcceptCutTag.decideTag decision <$>
      PqxdhRegistrationJointAcceptCutTag.tag work index).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source) :=
    fun source => (isQueryBoundP_map_iff _ _ _).mpr
      (PqxdhRegistrationJointAcceptCutTag.tag_bound work index _ _ (certified source))
  have actualBills := PqxdhRegistrationJointKemCutInterpreted.actual_bills setup caps bounded _ _ _ _ _
    (PqxdhRegistrationJointKemProgramBills.commands setup codec checks caps bounded
      created.server.server.metadata.identityIndex created.publicIdentity _ budget tagged []
      (PqxdhRegistrationJointInitializedAccept.initial created))
  have finished (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
      (bound : (simulateQ (actual setup) (commands setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision <$>
          PqxdhRegistrationJointAcceptCutTag.tag work index) []
        (PqxdhRegistrationJointInitializedAccept.initial created))).IsQueryBoundP predicate cap) :
      (rawScan setup codec checks decision work index created).IsQueryBoundP predicate cap := by
    apply PqxdhRegistrationJointKemCutBounds.bind_prefix _ (PqxdhRegistrationJointKemCut.finish setup)
    rw [rawScan, PqxdhRegistrationJointKemCut.scan_finish, PqxdhRegistrationJointAcceptKemCut.exposeAt_commands]
    exact bound
  exact ⟨finished _ _ actualBills.creates, finished _ _ actualBills.decaps, finished _ _ actualBills.uniform⟩

/-- Full raw-ordinal prephase uniform allowance, including failed initialization and all locally reserved pairs; it is the allowance of `KemPreBills.uniform`. -/
theorem pre_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target).IsQueryBoundP
      IsMlKemUniformQuery ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + uniformCap caps (budget (.inl 1)) (budget (.inl 5))
          (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))) := by
  unfold preRaw
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
    (PqxdhRegistrationJointServerBirth.client_uniform setup ensureInit qInit initBound setup.serverKeyId supplied _))
  rintro ⟨(_ | created), after⟩ _
  · simp
  · apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
      (PqxdhLiveKemSelection.family_uniform _ caps.keygenCost count
        (PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded)))
    intro others _
    have bills := scan_bills setup codec checks caps bounded decision work budget certified index created
    simpa only [uniformCap, bind_pure_comp, isQueryBoundP_map_iff] using
      PqxdhDynamicKemJointBounds.pre_uniform setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _ _ _
        bills.creates bills.uniform bills.decaps (after.1.1, PqxdhDynamicKemRouter.empty)
        caps.decapsUniform (PqxdhRegistrationJointKemCosts.local_uniform setup caps bounded)

/-- Local constructor and reservation work of the raw-ordinal prephase have no external nonuniform CCA query; every such query comes from the routed raw-ordinal scan. -/
theorem pre_excluded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inl (.inl coin))) (q : Nat)
    (suffix : ∀ created joint others,
      ((((simulateQ (PqxdhDynamicKemJointRouter.pre setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others))
        (rawScan setup codec checks decision work index created)).run).run
          (joint, PqxdhDynamicKemRouter.empty))).IsQueryBoundP predicate q) :
    (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target).IsQueryBoundP
      predicate q := by
  unfold preRaw
  rw [← Nat.zero_add q]
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
  rintro ⟨(_ | created), after⟩ _
  · simp
  · rw [← Nat.zero_add q]
    apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
    intro others _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using suffix created after.1.1 others

/-- The raw-ordinal prephase has at most `qFinish` logical CCA decapsulation queries. -/
theorem pre_decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (budget (.inl 5)) :=
  pre_excluded setup codec checks ensureInit supplied decision work runtime count selected index target
    IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) _
    (fun created joint others => PqxdhDynamicKemJointBounds.pre_decaps setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _
      (scan_bills setup codec checks caps bounded decision work budget certified index created).decaps
      (joint, PqxdhDynamicKemRouter.empty))

/-- The raw-ordinal prephase retains every local decapsulation base query, at most `decapsBase * qFinish`. -/
theorem pre_base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (preRaw setup codec checks ensureInit supplied decision work runtime count selected index target).IsQueryBoundP
      IsMlKemBaseQuery (caps.decapsBase * budget (.inl 5)) :=
  pre_excluded setup codec checks ensureInit supplied decision work runtime count selected index target
    IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) _
    (fun created joint others => PqxdhDynamicKemJointBounds.pre_base setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _
      (scan_bills setup codec checks caps bounded decision work budget certified index created).decaps
      (joint, PqxdhDynamicKemRouter.empty) IsMlKemBaseQuery
      (fun _ => by simp [IsMlKemBaseQuery]) (fun _ => by simp [IsMlKemBaseQuery])
      caps.decapsBase (PqxdhRegistrationJointKemCosts.local_base setup caps bounded))

/-- Forward support annotation leaves every raw-ordinal prephase resource bound unchanged at every public challenger key. -/
theorem annotated_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : (preRaw setup codec checks ensureInit supplied decision work runtime count selected index
      target).IsQueryBoundP predicate cap) :
    (PqxdhRegistrationJointKemRawCertified.annotatedPre setup codec checks ensureInit supplied decision work runtime
      count selected index target).IsQueryBoundP predicate cap := by
  rw [← PqxdhRegistrationJointKemRawCertified.prefix_erase setup codec checks ensureInit supplied decision work
    runtime count selected index target] at bounded
  exact (isQueryBoundP_map_iff _ _ _).mp bounded

set_option backward.isDefEq.respectTransparency false in
/-- The exact proof-carrying raw-ordinal adversary is bounded on every prechallenge key, every valid saved context and every postchallenge reply, with exactly the caps of `KemReductionBills.adversary_bound`: prechallenge uniform `(qInit + 32g) + (keygenCost * count + V)`, base `decapsBase * qFinish` and `qFinish` logical decapsulations; postchallenge uniform `V`, base `decapsBase * qFinish` and `qFinish` logical decapsulations, where `V = uniformCap caps qCreate qFinish (OpenUniform.total caps budget) qAccept`. The separate phase caps conservatively sum to at most twice `qFinish` logical requests. -/
theorem adversary_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (budget : Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
      count selected index).MakesAtMostQueries
      ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + uniformCap caps (budget (.inl 1)) (budget (.inl 5))
          (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3))))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5))
      (uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) := by
  constructor
  · intro target
    refine ⟨?_, ?_, ?_⟩
    · exact annotated_bound setup codec checks ensureInit supplied decision work runtime count selected index target
        _ _ (pre_uniform setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget
          certified runtime count selected index target)
    · exact annotated_bound setup codec checks ensureInit supplied decision work runtime count selected index target
        _ _ (pre_base setup codec checks caps bounded ensureInit supplied decision work budget certified runtime
          count selected index target)
    · exact annotated_bound setup codec checks ensureInit supplied decision work runtime count selected index target
        _ _ (pre_decapsulations setup codec checks caps bounded ensureInit supplied decision work budget certified
          runtime count selected index target)
  · intro transcript candidate
    have bills := adversary_post setup codec checks caps bounded ensureInit supplied decision work runtime count
      selected index budget certified transcript candidate
    exact ⟨bills.uniform, bills.base, bills.decaps⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_all

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.hides_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.exposeAt_hides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.exposeAt_hides

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.exposeAt_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.exposeAt_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.residual_hook' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.residual_hook

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.preRaw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.preRaw_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.saved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.saved

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.uniform_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.uniform_cap

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.adversary_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.adversary_post

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.scan_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.scan_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_excluded

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_decapsulations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.pre_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.annotated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.annotated_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.adversary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills.adversary_bound
