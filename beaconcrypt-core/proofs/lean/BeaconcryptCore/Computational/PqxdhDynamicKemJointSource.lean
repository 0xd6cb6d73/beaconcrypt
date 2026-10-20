import BeaconcryptCore.Computational.PqxdhDynamicKemStopping

/-!
The actual joint identity, private coin and indexed KEM service is retained while adding the selected disclosure monitor. Bounded reservations are activated by the original creation queries and project to the original private source pool. The monitor does not turn ordinary compromise into a protocol rejection.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemJointSource
open PqxdhKemIndCca PqxdhDynamicKemRouter
open PqxdhLiveKemBirth (PoolSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

abbrev State (KemSK : Type) := PqxdhDynamicIdentityPool.SourceState × PqxdhDynamicKemRouter.State KemSK

def project (pairs : List (MlKem768PublicKey × KemSK)) (state : State KemSK) : PqxdhLiveKemBirth.State KemSK :=
  (state.1, sourcePool pairs state.2)

/-- Actual joint-seed operations and local random choices keep their source order and full state. Only the KEM callback adds the private disclosure monitor. -/
def normal (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) :
    QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OptionT (StateT (State KemSK) ProbComp)) := fun query =>
  OptionT.mk fun state => match query with
  | .inl query => (fun result => (some result.1, (result.2, state.2))) <$>
      (PqxdhDynamicIdentityPool.lazyImpl primitives query).run state.1
  | .inr (.inl query) => (fun result => (some result, state)) <$> (unifSpec.query query : ProbComp _)
  | .inr (.inr query) => (fun result => (result.1, (state.1, result.2))) <$>
      (((PqxdhDynamicKemStopping.normal baseImpl kem selected pairs query).run).run state.2)

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary private reveal, including the selected secret and missing handles, projects to the actual source service without changing its returned optional value or full history. -/
theorem reveal_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (state : PqxdhDynamicKemRouter.State KemSK) (index : Nat) :
    (fun result => (result.1, sourcePool pairs result.2)) <$>
      (((PqxdhDynamicKemStopping.normal baseImpl kem selected pairs (.reveal index)).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (PqxdhLiveKemBirth.poolImpl baseImpl kem (.reveal index)).run (sourcePool pairs state) := by
  cases found : (pairs.take state.created)[index]? <;>
    simp only [PqxdhDynamicKemStopping.normal, OptionT.run_mk, StateT.run, PqxdhLiveKemBirth.poolImpl,
      sourcePool, found, map_pure, record, PqxdhLiveKemBirth.record, Option.map_none, Option.map_some]

set_option backward.isDefEq.respectTransparency false in
/-- An affordable actual joint/private request is exactly the original reserved source operation after erasing only the monitor and reconstructing its private pool. -/
theorem step_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK)
    (room : state.2.created + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((normal baseImpl primitives kem selected pairs query).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (PqxdhLiveKemReservation.reserved baseImpl primitives kem pairs query).run (project pairs state) := by
  rcases query with joint | (coin | query)
  · simp only [normal, OptionT.run_mk, StateT.run, PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, Functor.map_map, project, Prod.map_def, id_eq]
  · rfl
  · cases query with
    | create =>
      have before : state.2.created < pairs.length := by simpa only [PqxdhLiveKemReservation.IsCreate, ite_true] using Nat.lt_of_succ_le room
      have found : pairs[state.2.created]? = some pairs[state.2.created] := List.getElem?_eq_some_iff.mpr ⟨before, rfl⟩
      simp only [normal, PqxdhDynamicKemStopping.normal, source, OptionT.run_mk, StateT.run,
        found, map_pure, PqxdhLiveKemReservation.reserved, project, sourcePool, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt before)]
      exact congrArg (fun result => (pure (some result.1, (state.1, result.2)) : ProbComp _))
        (PqxdhDynamicKemSource.created_pool pairs state.2 pairs[state.2.created] found)
    | decapsulate index ciphertext =>
      have same := congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
        (PqxdhDynamicKemSource.decapsulation_source baseImpl kem selected pairs state.2 index ciphertext)
      simpa only [normal, OptionT.run_mk, StateT.run, PqxdhDynamicKemStopping.normal,
        PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, Functor.map_map, project, Prod.map_def, id_eq] using same
    | reveal index =>
      have same := congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
        (reveal_source baseImpl kem selected pairs state.2 index)
      simpa only [normal, OptionT.run_mk, StateT.run, PqxdhLiveKemReservation.reserved,
        PqxdhLiveKemBirth.impl, Functor.map_map, project, Prod.map_def, id_eq] using same

/-- An affordable source request cannot produce the artificial outer reservation failure. Ordinary optional rejection remains inside its actual reply. -/
theorem step_answer (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK)
    (room : state.2.created + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((PqxdhLiveKemBirth.Spec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl primitives kem selected pairs query).run).run state)) :
    result.1.isSome = true := by
  have mapped : (result.1, project pairs result.2) ∈ support
      (Prod.map id (project pairs) <$> (((normal baseImpl primitives kem selected pairs query).run).run state)) :=
    by simpa only [support_map, Prod.map_def, id_eq] using Set.mem_image_of_mem (Prod.map id (project pairs)) supported
  rw [step_source baseImpl primitives kem selected pairs query state room] at mapped
  simp only [support_map, Set.mem_image] at mapped
  obtain ⟨reply, _, same⟩ := mapped
  exact congrArg (fun value => value.1.isSome) same.symm

set_option backward.isDefEq.respectTransparency false in
/-- Joint identity and local-coin effects cannot activate KEM slots; creation alone spends the exact original allowance, even after a successful selected reveal. -/
theorem step_capacity (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : State KemSK)
    (clear : state.2.exhausted = false)
    (room : state.2.created + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((PqxdhLiveKemBirth.Spec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl primitives kem selected pairs query).run).run state)) :
    result.2.2.exhausted = false ∧
      result.2.2.created ≤ state.2.created + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) := by
  rcases query with joint | (coin | query)
  · simp only [normal, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact ⟨clear, Nat.le_refl _⟩
  · simp only [normal, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact ⟨clear, Nat.le_refl _⟩
  · simp only [normal, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, supported, rfl⟩ := supported
    have isCreation : PqxdhLiveKemReservation.IsCreate (KemSK := KemSK) (.inr (.inr query) : (PqxdhLiveKemBirth.Spec KemSK).Domain) ↔
        PqxdhDynamicKemSource.IsCreation query := by cases query <;> rfl
    simpa only [isCreation] using PqxdhDynamicKemStopping.normal_step_capacity baseImpl kem selected pairs query state.2 clear
      (by simpa only [isCreation] using room) reply supported

set_option backward.isDefEq.respectTransparency false in
/-- The complete bounded adaptive joint/private source has the original reserved source program, including every ordinary selected-secret reply, full joint seed/log state and complete KEM pool history. Only the added monitor and inaccessible future reservation are projected away. -/
theorem program_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qCreate : Nat)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate) (state : State KemSK)
    (clear : state.2.exhausted = false) (room : state.2.created + qCreate ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (simulateQ (PqxdhLiveKemReservation.reserved baseImpl primitives kem pairs) client).run (project pairs state) := by
  induction client using OracleComp.inductionOn generalizing qCreate state with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    have affordable : state.2.created + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length := by
      split_ifs with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega
    have sameHead := congrArg (fun work => work >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun reply =>
          (fun output => (some output.1, output.2)) <$>
            (simulateQ (PqxdhLiveKemReservation.reserved baseImpl primitives kem pairs) (next reply)).run result.2))
      (step_source baseImpl primitives kem selected pairs query state affordable)
    simp only [bind_map_left, Prod.map_def, id_eq, Option.elim_some] at sameHead
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
      map_bind]
    refine Eq.trans ?_ sameHead
    apply bind_congr_of_forall_mem_support
    rintro ⟨answer, after⟩ supported
    have present := step_answer baseImpl primitives kem selected pairs query state affordable (answer, after) supported
    have capacity := step_capacity baseImpl primitives kem selected pairs query state clear affordable (answer, after) supported
    dsimp only at capacity
    cases answer with
    | none => exact False.elim (Bool.noConfusion present)
    | some answer =>
      have tailRoom : after.2.created + (if PqxdhLiveKemReservation.IsCreate query then qCreate - 1 else qCreate) ≤ pairs.length := by
        split_ifs at capacity ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      exact ih answer _ (bounded.2 answer) after capacity.1 tailRoom

/-- The complete source uniform-query allowance is preserved by the actual oracle-program equality. Joint identity work and local source coins are not declared free. -/
theorem program_uniform (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (qCreate qUniform : Nat)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate)
    (state : State KemSK) (clear : state.2.exhausted = false) (room : state.2.created + qCreate ≤ pairs.length) :
    (((simulateQ (normal baseImpl primitives kem selected pairs) client).run).run state).IsTotalQueryBound qUniform ↔
      ((simulateQ (PqxdhLiveKemReservation.reserved baseImpl primitives kem pairs) client).run
        (project pairs state)).IsTotalQueryBound qUniform := by
  have same := congrArg (fun work => work.IsTotalQueryBound qUniform)
    (program_source baseImpl primitives kem selected pairs client qCreate bounded state clear room)
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using same.to_iff

set_option backward.isDefEq.respectTransparency false in
/-- The actual on-demand source starting with its empty KEM pool is equal to drawing the chosen creation first and running the complete monitored joint source. Every earlier joint-identity field and adaptive continuation is retained. -/
theorem selected_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (count : Nat) (selected : Fin (count + 1))
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) (count + 1))
    (joint : PqxdhDynamicIdentityPool.SourceState) :
    EvalDistEq
      ((fun result => (some result.1, result.2)) <$>
        (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) client).run (joint, PqxdhLiveKemBirth.empty))
      (do
        let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen
        let others ← PqxdhLiveKemSelection.sampleFamily
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen) count
        let pairs := List.ofFn (selected.insertNth chosen others)
        Prod.map id (project pairs) <$>
          (((simulateQ (normal baseImpl primitives kem selected.val pairs) client).run).run (joint, empty))) := by
  have same := (PqxdhLiveKemSelection.source_target_first baseImpl primitives kem client count selected bounded
      (joint, PqxdhLiveKemBirth.empty)).map
    (fun result : Result × PqxdhLiveKemBirth.State KemSK => (some result.1, result.2))
  refine same.trans ?_
  simp only [map_bind, PqxdhLiveKemBirth.empty, List.nil_append]
  refine EvalDistEq.bind_right _ fun chosen => ?_
  refine EvalDistEq.bind_right _ fun others => ?_
  have equal := (program_source baseImpl primitives kem selected.val (List.ofFn (selected.insertNth chosen others))
    client (count + 1) bounded (joint, empty) rfl (by simp [empty])).symm
  simp only [project, sourcePool, empty, List.take_zero] at equal ⊢
  rw [equal]

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.selected_source_vcvioLegacy :
    ∀ {ι : Type} {baseSpec : OracleSpec.{0, 0} ι} {KemSK Result : Type} (baseImpl : @QueryImpl.{0, 0, 0} ι baseSpec ProbComp) (primitives : BeaconcryptCore.Computational.PqxdhJointIdentity.Primitives) (kem : @BeaconcryptCore.Computational.PqxdhKemIndCca.MlKemScheme ι baseSpec KemSK) (client : @OracleComp.{0, 0, 0} (Sum.{0, 0} (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.PoolQuery) (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhLiveKemBirth.Query)) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.Spec KemSK) Result) (count : Nat) (selected : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (bounded : @OracleComp.IsQueryBoundP.{0} (Sum.{0, 0} (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.PoolQuery) (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhLiveKemBirth.Query)) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.Spec KemSK) Result client (@BeaconcryptCore.Computational.PqxdhLiveKemReservation.IsCreate KemSK) (@BeaconcryptCore.Computational.PqxdhLiveKemReservation.instDecidablePredDomainSumNatPoolQueryQuerySpecIsCreate KemSK) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (joint : BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.SourceState),
      @Eq.{1} (SPMF.{0} (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK))) (@evalSPMF.{0, 0} ProbComp (@instMonadLiftTOfMonadLift.{0, 0, 0, 0} ProbComp PMF.{0} SPMF.{0} SPMF.instMonadLiftPMF.{0} (@PFunctor.FreeM.instMonadLiftTPMF.{0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec) (@OracleSpec.IsUniformSpec.toIsProbabilitySpec.{0, 0} Nat unifSpec OracleSpec.instIsUniformSpecNatUnifSpec))) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) (@Functor.map.{0, 0} ProbComp (@PFunctor.FreeM.instFunctor.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)) (Prod.{0, 0} Result (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) (fun (result : Prod.{0, 0} Result (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) => @Prod.mk.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) (@Option.some.{0} Result (@Prod.fst.{0, 0} Result (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) result)) (@Prod.snd.{0, 0} Result (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) result)) (@StateT.run.{0, 0} (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) ProbComp Result (@simulateQ.{0, 0, 0} (Sum.{0, 0} (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.PoolQuery) (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhLiveKemBirth.Query)) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.Spec KemSK) (StateT.{0, 0} (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) ProbComp) (@StateT.instMonad.{0, 0} (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) ProbComp (@PFunctor.FreeM.instMonad.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec))) (@BeaconcryptCore.Computational.PqxdhLiveKemBirth.impl ι baseSpec KemSK baseImpl primitives kem) Result client) (@Prod.mk.{0, 0} BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.SourceState (BeaconcryptCore.Computational.PqxdhLiveKemBirth.Pool KemSK) joint (@BeaconcryptCore.Computational.PqxdhLiveKemBirth.empty KemSK)))))
        (@evalSPMF.{0, 0} ProbComp (@instMonadLiftTOfMonadLift.{0, 0, 0, 0} ProbComp PMF.{0} SPMF.{0} SPMF.instMonadLiftPMF.{0} (@PFunctor.FreeM.instMonadLiftTPMF.{0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec) (@OracleSpec.IsUniformSpec.toIsProbabilitySpec.{0, 0} Nat unifSpec OracleSpec.instIsUniformSpecNatUnifSpec))) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK))
          (@Bind.bind.{0, 0} ProbComp (@PFunctor.FreeM.instBind.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)) (Prod.{0, 0} BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) (@simulateQ.{0, 0, 0} (Sum.{0, 0} Nat ι) (@HAdd.hAdd.{1, 1, 1} (OracleSpec.{0, 0} Nat) (OracleSpec.{0, 0} ι) (OracleSpec.{0, 0} (Sum.{0, 0} Nat ι)) (@OracleSpec.instHAddSum.{0, 0, 0} Nat ι) unifSpec baseSpec) ProbComp (@PFunctor.FreeM.instMonad.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)) (@BeaconcryptCore.Computational.PqxdhInitializerSecrecy.kemAmbientImpl ι baseSpec baseImpl) (Prod.{0, 0} BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK) (@KEMScheme.keygen.{0} (@OracleComp.{0, 0, 0} (Sum.{0, 0} Nat ι) (@HAdd.hAdd.{1, 1, 1} (OracleSpec.{0, 0} Nat) (OracleSpec.{0, 0} ι) (OracleSpec.{0, 0} (Sum.{0, 0} Nat ι)) (@OracleSpec.instHAddSum.{0, 0, 0} Nat ι) unifSpec baseSpec)) (@PFunctor.FreeM.instMonad.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} (Sum.{0, 0} Nat ι) (@HAdd.hAdd.{1, 1, 1} (OracleSpec.{0, 0} Nat) (OracleSpec.{0, 0} ι) (OracleSpec.{0, 0} (Sum.{0, 0} Nat ι)) (@OracleSpec.instHAddSum.{0, 0, 0} Nat ι) unifSpec baseSpec))) BeaconcryptCore.Computational.PqxdhKemIndCca.MlKemSharedSecret BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768Ciphertext kem)) fun (chosen : Prod.{0, 0} BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK) =>
            @Bind.bind.{0, 0} ProbComp (@PFunctor.FreeM.instBind.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)) (Fin count → BeaconcryptCore.Computational.PqxdhLiveKemReservation.Pair KemSK) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) (@BeaconcryptCore.Computational.PqxdhLiveKemSelection.sampleFamily KemSK (@simulateQ.{0, 0, 0} (Sum.{0, 0} Nat ι) (@HAdd.hAdd.{1, 1, 1} (OracleSpec.{0, 0} Nat) (OracleSpec.{0, 0} ι) (OracleSpec.{0, 0} (Sum.{0, 0} Nat ι)) (@OracleSpec.instHAddSum.{0, 0, 0} Nat ι) unifSpec baseSpec) ProbComp (@PFunctor.FreeM.instMonad.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)) (@BeaconcryptCore.Computational.PqxdhInitializerSecrecy.kemAmbientImpl ι baseSpec baseImpl) (BeaconcryptCore.Computational.PqxdhLiveKemReservation.Pair KemSK) (@KEMScheme.keygen.{0} (@OracleComp.{0, 0, 0} (Sum.{0, 0} Nat ι) (@HAdd.hAdd.{1, 1, 1} (OracleSpec.{0, 0} Nat) (OracleSpec.{0, 0} ι) (OracleSpec.{0, 0} (Sum.{0, 0} Nat ι)) (@OracleSpec.instHAddSum.{0, 0, 0} Nat ι) unifSpec baseSpec)) (@PFunctor.FreeM.instMonad.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} (Sum.{0, 0} Nat ι) (@HAdd.hAdd.{1, 1, 1} (OracleSpec.{0, 0} Nat) (OracleSpec.{0, 0} ι) (OracleSpec.{0, 0} (Sum.{0, 0} Nat ι)) (@OracleSpec.instHAddSum.{0, 0, 0} Nat ι) unifSpec baseSpec))) BeaconcryptCore.Computational.PqxdhKemIndCca.MlKemSharedSecret BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768Ciphertext kem)) count) fun (others : Fin count → BeaconcryptCore.Computational.PqxdhLiveKemReservation.Pair KemSK) =>
              have pairs := @List.ofFn.{0} (Prod.{0, 0} BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.insertNth.{1} count (fun (a : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) => Prod.{0, 0} BeaconcryptCore.Computational.PqxdhKemIndCca.MlKem768PublicKey KemSK) selected chosen others);
              @Functor.map.{0, 0} ProbComp (@PFunctor.FreeM.instFunctor.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK)) (Prod.{0, 0} (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK)) (@Prod.map.{0, 0, 0, 0} (Option.{0} Result) (Option.{0} Result) (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.State KemSK) (@id.{1} (Option.{0} Result)) (@BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.project KemSK pairs)) (@StateT.run.{0, 0} (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK) ProbComp (Option.{0} Result) (@OptionT.run.{0, 0} (StateT.{0, 0} (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK) ProbComp) Result (@simulateQ.{0, 0, 0} (Sum.{0, 0} (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.PoolQuery) (Sum.{0, 0} Nat BeaconcryptCore.Computational.PqxdhLiveKemBirth.Query)) (BeaconcryptCore.Computational.PqxdhLiveKemBirth.Spec KemSK) (OptionT.{0, 0} (StateT.{0, 0} (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK) ProbComp)) (@OptionT.instMonad.{0, 0} (StateT.{0, 0} (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK) ProbComp) (@StateT.instMonad.{0, 0} (BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.State KemSK) ProbComp (@PFunctor.FreeM.instMonad.{0, 0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec)))) (@BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.normal ι baseSpec KemSK baseImpl primitives kem (@Fin.val (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) selected) pairs) Result client)) (@Prod.mk.{0, 0} BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.SourceState (BeaconcryptCore.Computational.PqxdhDynamicKemRouter.State KemSK) joint (@BeaconcryptCore.Computational.PqxdhDynamicKemRouter.empty KemSK))))) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.selected_source

end BeaconcryptCore.Computational.PqxdhDynamicKemJointSource

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.reveal_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.reveal_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.step_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.step_answer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.step_answer
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.step_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.step_capacity
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.program_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemJointSource.selected_source
