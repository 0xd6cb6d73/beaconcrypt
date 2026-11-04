-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt
/-! The original agreement source sampler and actual opaque primitive results determine the ephemeral observation. The source executor and the private capture retain one random computation and caller RNG; normality is derived from the existing individual source primitive contracts. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
open AdapterPublicAgreementInterpreter (Capture)
open AdapterPublicAgreementFields (Keys)
private theorem map_apply {State X Y :Type} {m :Type→Type} [Monad m] [LawfulMonad m]
    (function :X→Y) (work :StateT State m X) (before :State) :
    (function <$>work) before=(fun result=>(function result.1,result.2)) <$>work before :=
  StateT.run_map _ _ _

private theorem pure_apply {State X :Type} {m :Type→Type} [Monad m] (value :X) (before :State) :
    (pure value :StateT State m X) before=pure (value,before) :=rfl

private theorem bind_apply {State X Y :Type} {m :Type→Type} [Monad m]
    (work :StateT State m X) (next :X→StateT State m Y) (before :State) :
    (work >>=next) before=(do let result←work before;next result.1 result.2) :=rfl

private theorem set_apply {State :Type} {m :Type→Type} [Monad m] (value before :State) :
    (set value :StateT State m PUnit) before=pure (PUnit.unit,value) :=rfl

private theorem modify_apply {State :Type} {m :Type→Type} [Monad m] (function :State→State) (before :State) :
    (modify function :StateT State m PUnit) before=pure (PUnit.unit,function before) :=rfl

private theorem rust_map_lift {X Y :Type} {m :Type→Type} [Monad m] [LawfulMonad m]
    (function :X→Y) (work :m X) :function <$>RustT.lift work=RustT.lift (function <$>work) :=by
  apply RustT.ext
  change ((RustM.ok <$>work) >>=fun result=>match result with
    | .ok value=>pure (RustM.ok (function value))
    | .fail error=>pure (RustM.fail error)
    | .div=>pure RustM.div)=_
  simp only [bind_map_left,bind_pure_comp,RustT.run_lift,Functor.map_map]

variable {n :Nat} {KemSK P A B I R Error :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)
local notation "BaseM"=>StateT (Backend n KemSK) ProbComp

noncomputable def transform (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :RustT ProbComp A) :RustT PhysicalM A :=
  AdapterPublicAgreementOracleInterpretation.transform coins (RegistrationNativePlatformPublicAdapterCrypto.transform work)

noncomputable def sample (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :ProbComp A) :PhysicalM A :=
  fun before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterCrypto.world (KemSK:=KemSK) (PqxdhRecordLiftWorld.sampled work)).run before)

theorem transform_lift (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :ProbComp A) :
    transform (n:=n) (KemSK:=KemSK) coins (RustT.lift work)=RustT.lift (sample coins work) :=by
  apply RustT.ext
  funext before
  unfold transform sample AdapterPublicAgreementOracleInterpretation.transform RegistrationNativePlatformInterpret.state
    RegistrationNativePlatformPublicAdapterCrypto.transform RegistrationNativePlatformPublicAdapterCrypto.world
    AdapterPublicAgreementCountedRust.counted
  simp only [RustT.run_lift,StateT.run]
  simp only [map_apply,simulateQ_map,Functor.map_map]
  have mapped:=congrArg (fun computation=>(fun result :RustM A×PqxdhRecordLiftWorld.State n=>
      (result.1,{before with world:=result.2})) <$>simulateQ coins computation)
    (RegistrationAgreementSampledState.sampled_map RustM.ok work before.world)
  simp only [simulateQ_map,Functor.map_map] at mapped
  exact mapped

theorem pure_transform (coins :QueryImpl unifSpec (StateT P ProbComp)) (value :A) :
    transform (n:=n) (KemSK:=KemSK) coins (pure value)=pure value :=by
  have first :RegistrationNativePlatformPublicAdapterCrypto.transform (n:=n) (KemSK:=KemSK) (pure value)=pure value :=
    RegistrationNativePlatformPublicAdapterCrypto.translation.lawful.map_pure value
  exact (congrArg (AdapterPublicAgreementOracleInterpretation.transform coins) first).trans
    (AdapterPublicAgreementOracleInterpretation.transform_pure coins value)

theorem sample_map (coins :QueryImpl unifSpec (StateT P ProbComp)) (function :A→B) (work :ProbComp A) :
    sample (n:=n) (KemSK:=KemSK) coins (function <$>work)=function <$>sample coins work :=by
  funext before
  unfold sample RegistrationNativePlatformPublicAdapterCrypto.world
  simp only [StateT.run]
  rw [map_apply]
  have mapped:=congrArg (fun computation=>(fun result :B×PqxdhRecordLiftWorld.State n=>
      (result.1,{before with world:=result.2})) <$>simulateQ coins computation)
    (RegistrationAgreementSampledState.sampled_map function work before.world)
  simp only [simulateQ_map,Functor.map_map] at mapped
  simp only [simulateQ_map,Functor.map_map]
  exact mapped

theorem sample_pure (coins :QueryImpl unifSpec (StateT P ProbComp)) (value :A) :
    sample (n:=n) (KemSK:=KemSK) coins (pure value)=pure value :=by
  funext before
  change simulateQ coins ((fun result :A×PqxdhRecordLiftWorld.State n=>(result.1,{before with world:=result.2})) <$>
    (PqxdhRecordLiftWorld.sampled (pure value)).run before.world)=pure (value,before)
  rw [RegistrationAgreementSampledState.sampled_pure,map_pure,simulateQ_pure]

theorem sample_bind (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :ProbComp A) (next :A→ProbComp B) :
    sample (n:=n) (KemSK:=KemSK) coins (work >>=next)=(sample coins work >>=fun value=>sample coins (next value)) :=by
  funext before
  change simulateQ coins ((fun result :B×PqxdhRecordLiftWorld.State n=>(result.1,{before with world:=result.2})) <$>
    (PqxdhRecordLiftWorld.sampled (work >>=next)).run before.world)=_
  rw [RegistrationAgreementSampledState.sampled_bind]
  simp only [map_bind,simulateQ_bind,simulateQ_map]
  unfold sample RegistrationNativePlatformPublicAdapterCrypto.world
  simp only [StateT.run,bind_apply,simulateQ_map,bind_map_left]

theorem observe_lift (mark :Backend n KemSK→RustM A→Backend n KemSK) (work :PhysicalM A) :
    RegistrationNativePlatformPublicAdapterAcceptObserver.observe mark (RustT.lift work)=
      RustT.lift (fun before=>(fun result=>(result.1,mark result.2 (.ok result.1))) <$>work.run before) :=by
  apply RustT.ext
  apply StateT.ext
  intro before
  apply StateT.ext
  intro previous
  rw [RegistrationNativePlatformPublicAdapterAcceptObserver.observe_run]
  simp only [RustT.run_lift,StateT.run_map,Functor.map_map]
  simp only [StateT.run,map_apply,Functor.map_map]

theorem sample_facts (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :ProbComp A)
    (before :Backend n KemSK) (previous :P) (result :(A×Backend n KemSK)×P)
    (supported :result∈support (((sample coins work).run before).run previous)) :
    result.1.1∈support work ∧result.1.2.auxiliary=before.auxiliary :=by
  have sourceReached :result.1∈support ((RegistrationNativePlatformPublicAdapterCrypto.world (KemSK:=KemSK)
      (PqxdhRecordLiftWorld.sampled work)).run before) :=by
    apply OracleComp.support_simulateQ_run'_subset coins _ previous
    rw [StateT.run'_eq,support_map]
    exact ⟨result,supported,rfl⟩
  simp only [RegistrationNativePlatformPublicAdapterCrypto.world,StateT.run,support_map] at sourceReached
  obtain ⟨worldResult,worldSupport,same⟩:=sourceReached
  have equal :result.1=(worldResult.1,{before with world:=worldResult.2}):=same.symm
  rw [equal]
  refine ⟨?_,rfl⟩
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp,support_map] at worldSupport
  obtain ⟨counted,countedSupport,matched⟩:=worldSupport
  have valueEq :worldResult.1=counted.1:=congrArg Prod.fst matched.symm
  rw [valueEq]
  apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin work before.world.primitive.1.uniform
  rw [StateT.run'_eq,support_map]
  exact ⟨counted,countedSupport,rfl⟩

variable [material :PublicWrapperPlatform.Material] [ed :AdapterInitEdPrimitive.Operations]
variable [original :CryptoOperations (RustT ProbComp)]

theorem original_program (coins :QueryImpl unifSpec (StateT P ProbComp))
    (generator :rand_core.TryCryptoRng R Error) (keys :Keys)
    (work :OracleComp RegistrationAgreementExecutor.Spec A) (before :Capture R) :
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterCryptoPlatform.operations coins original
    (simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys) work).run before=
      transform coins ((simulateQ (AdapterPublicAgreementInterpreter.handler (m:=ProbComp) generator keys) work).run before) :=by
  let :AdapterPublicAgreementMonadMap.Transformation ProbComp BaseM:=RegistrationNativePlatformPublicAdapterCrypto.translation
  have first:=AdapterPublicAgreementOracleInterpretation.program coins
    (RegistrationNativePlatformPublicAdapterCrypto.operations (n:=n) (KemSK:=KemSK) original) generator keys work before
  have second:=AdapterPublicAgreementMonadInterpreter.program (left:=ProbComp) (right:=BaseM) generator keys work before
  exact first.trans (congrArg (AdapterPublicAgreementOracleInterpretation.transform coins) second)

variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (generator :rand_core.TryCryptoRng R Error)
variable (model :AdapterPublicAgreementPrimitiveModel.Model (m:=ProbComp) generator setup checks view)

 theorem original_normal (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (work :OracleComp RegistrationAgreementExecutor.Spec A) (before :Capture R) :
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterCryptoPlatform.operations coins original
    (simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys) work).run before=
      RustT.lift (sample coins ((simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys) work).run before)) :=by
  exact (original_program (n:=n) (KemSK:=KemSK) coins generator keys work before).trans
    ((congrArg (transform (n:=n) (KemSK:=KemSK) coins)
      (AdapterPublicAgreementPrimitiveModel.program model keys work before)).trans (transform_lift coins _))

include model in
theorem public_key (coins :QueryImpl unifSpec (StateT P ProbComp)) (key :beaconcrypt_crypto.crypto_kx.PublicKey) :
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
    CryptoOperations.kxPublicBytes (m:=RustT PhysicalM) key=pure (view.kxPublic key) :=by
  change transform coins (original.kxPublicBytes key)=_
  rw [model.getters.publicKey,pure_transform]

theorem generation (coins :QueryImpl unifSpec (StateT P ProbComp)) (rng :R) :
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
    AdapterPublicAgreementFields.generate (m:=PhysicalM) generator rng=RustT.lift (do
      let scalar←sample coins model.sample
      modify (fun before :Backend n KemSK=>{before with auxiliary:=⟨some scalar⟩})
      pure (core.option.Option.Some (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)),
        core.option.Option.Some (model.generation.realize scalar rng).1,(model.generation.realize scalar rng).2)) :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  change AdapterPublicAgreementFields.generate (m:=PhysicalM) generator rng=_
  rw [AdapterPublicAgreementPrimitiveFields.generation (m:=PhysicalM)]
  change (do
    let (result,nextRng)←RegistrationNativePlatformPublicAdapterAcceptObserver.observe
      (RegistrationNativePlatformPublicAdapterAcceptObserver.generated view)
      (transform coins (original.kxGenerate generator rng))
    match result with
    | .Err _=>pure (core.option.Option.None,core.option.Option.None,nextRng)
    | .Ok pair=>do
      let bytes←CryptoOperations.kxPublicBytes pair.public_key
      pure (core.option.Option.Some bytes,core.option.Option.Some pair,nextRng))=_
  rw [model.generation.operation,transform_lift,observe_lift,sample_map]
  simp only [public_key setup checks view generator model coins]
  apply RustT.ext
  apply StateT.ext
  intro before
  apply StateT.ext
  intro previous
  simp only [RustT.run_bind,RustT.run_lift,StateT.run_bind,StateT.run_modify,
    StateT.run_map,bind_map_left,map_pure,bind_pure_comp,Functor.map_map]
  simp only [StateT.run,map_apply,bind_map_left,
    RegistrationNativePlatformPublicAdapterAcceptObserver.generated,model.generation.privateView,model.generation.publicView,
    RustT.run_pure]
  simp only [pure_apply,bind_pure_comp]

theorem generated_capture (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (role :agreement.EphemeralRole) (captured :Capture R) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     ((AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys (.generate role)).run captured :
       RustT PhysicalM (core.option.Option AdapterPublicAgreementFields.Array32×Capture R)))=
    RustT.lift (do
      let scalar←sample coins model.sample
      modify (fun before :Backend n KemSK=>{before with auxiliary:=⟨some scalar⟩})
      pure (core.option.Option.Some (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)),
        {captured with rng:=(model.generation.realize scalar captured.rng).2, ephemeral:=core.option.Option.Some (model.generation.realize scalar captured.rng).1})) :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  simp only [AdapterPublicAgreementInterpreter.handler,StateT.run_bind,StateT.run_get,StateT.run_lift,pure_bind]
  rw [generation setup checks view generator model coins]
  simp only [StateT.run_set,StateT.run_pure,map_pure,bind_pure_comp,rust_map_lift]
  apply congrArg RustT.lift
  simp only [map_bind,Functor.map_map]

 theorem nongenerate_capture (keys :Keys) (request :RegistrationAgreementExecutor.Request)
    (different :∀role,request≠.generate role) (before :Capture R)
    (result :RegistrationAgreementExecutor.Spec.Range request×Capture R)
    (supported :result∈support ((AdapterPublicAgreementPrimitiveModel.implementation model keys request).run before)) :
    result.2.ephemeral=before.ephemeral :=by
  cases request with
  | generate role=>exact False.elim (different role rfl)
  | encapsulate input=>
    simp [AdapterPublicAgreementPrimitiveModel.implementation,StateT.run_bind,StateT.run_get,
      StateT.run_lift,StateT.run_set] at supported
    obtain ⟨reply,rng,_possible,same⟩:=supported
    cases same
    rfl
  | convertPublic key | convertSecret role | decapsulate input | dh request | root request=>
    simp [AdapterPublicAgreementPrimitiveModel.implementation,StateT.run_map,StateT.run_lift,
      StateT.run_modify,StateT.run_pure,StateT.run_get] at supported
    first
    | cases supported;rfl
    | obtain ⟨inner,_possible,same⟩:=supported;cases same;rfl

def install (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (captured :Capture R)
    (before :Backend n KemSK) :Backend n KemSK :=
  {before with auxiliary:=AdapterPublicAgreementServerWorld.project view captured}

omit original in
theorem sample_install (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :ProbComp A)
    (captured :Capture R) (before :Backend n KemSK) (previous :P) :
    ((sample coins work).run (install view captured before)).run previous=
      (fun result=>((result.1.1,install view captured result.1.2),result.2)) <$>
        ((sample coins work).run before).run previous :=by
  simp only [sample,RegistrationNativePlatformPublicAdapterCrypto.world,install,StateT.run,simulateQ_map]
  simp only [map_apply,Functor.map_map]

theorem nongenerate_source (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (request :RegistrationAgreementExecutor.Request) (different :∀role,request≠.generate role) (before :Capture R) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys request).run before)=
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterCryptoPlatform.operations coins original
     (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys request).run before) :=by
  cases request with
  | generate role=>exact False.elim (different role rfl)
  | convertPublic _ | convertSecret _ | encapsulate _ | decapsulate _ | dh _ | root _=>rfl

theorem query (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (request :RegistrationAgreementExecutor.Request) (captured :Capture R) (before :Backend n KemSK)
    (related :before.auxiliary=AdapterPublicAgreementServerWorld.project view captured) (previous :P) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     (((AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys request).run captured).run.run before).run previous)=
    (fun result=>((RustM.ok result.1.1,install view result.1.1.2 result.1.2),result.2)) <$>
      ((sample coins ((AdapterPublicAgreementPrimitiveModel.implementation model keys request).run captured)).run before).run previous :=by
  by_cases generated :∃role,request=RegistrationAgreementExecutor.Request.generate role
  · obtain ⟨role,rfl⟩:=generated
    have first:=congrArg (fun work :RustT PhysicalM (core.option.Option AdapterPublicAgreementFields.Array32×Capture R)=>
      (work.run.run before).run previous)
      (generated_capture (n:=n) (KemSK:=KemSK) setup checks view generator model coins keys role captured)
    refine first.trans ?_
    change ((RustT.lift (do
      let scalar←sample coins model.sample
      modify (fun state :Backend n KemSK=>{state with auxiliary:=⟨some scalar⟩})
      pure (core.option.Option.Some (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)),
        {captured with rng:=(model.generation.realize scalar captured.rng).2, ephemeral:=core.option.Option.Some (model.generation.realize scalar captured.rng).1}))).run.run before).run previous=_
    have modelEq :((AdapterPublicAgreementPrimitiveModel.implementation model keys (.generate role)).run captured :
        ProbComp (core.option.Option AdapterPublicAgreementFields.Array32×Capture R))=
      (fun scalar=>(core.option.Option.Some (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)),
        {captured with rng:=(model.generation.realize scalar captured.rng).2, ephemeral:=core.option.Option.Some (model.generation.realize scalar captured.rng).1})) <$>model.sample :=by
      simp [AdapterPublicAgreementPrimitiveModel.implementation,StateT.run_bind,StateT.run_get,StateT.run_lift,
        StateT.run_set]
    rw [modelEq,sample_map]
    simp [RustT.run_lift,StateT.run_map,StateT.run_bind,StateT.run_modify,
      install,AdapterPublicAgreementServerWorld.project,model.generation.privateView]
  · have different :∀role,request≠.generate role:=fun role same=>generated ⟨role,same⟩
    have first:=congrArg (fun work :RustT PhysicalM (RegistrationAgreementExecutor.Spec.Range request×Capture R)=>
        (work.run.run before).run previous)
      (nongenerate_source (n:=n) (KemSK:=KemSK) view generator coins keys request different captured)
    have normal:=original_normal (n:=n) (KemSK:=KemSK) setup checks view generator model coins keys
      (RegistrationAgreementExecutor.Spec.query request) captured
    simp only [simulateQ_spec_query] at normal
    have second:=congrArg (fun work :RustT PhysicalM (RegistrationAgreementExecutor.Spec.Range request×Capture R)=>
        (work.run.run before).run previous) normal
    change _=_ at first
    rw [first.trans second,RustT.run_lift,StateT.run_map]
    simp only [StateT.run_map]
    rw [map_eq_bind_pure_comp,map_eq_bind_pure_comp]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro result supported
    obtain ⟨possible,auxiliary⟩:=sample_facts coins _ before previous result supported
    have cap:=nongenerate_capture setup checks view generator model keys request different captured result.1.1 possible
    have same :install view result.1.1.2 result.1.2=result.1.2:=by
      have projectSame :AdapterPublicAgreementServerWorld.project view result.1.1.2=
          AdapterPublicAgreementServerWorld.project view captured:=by
        change (⟨_root_.Option.map (fun key=>view.kxSecret key.secret_key) result.1.1.2.ephemeral⟩ :RegistrationServerRoleBackend.State)=_
        rw [cap]
        rfl
      unfold install
      rw [projectSame,←related,←auxiliary]
    dsimp only [Function.comp_def]
    rw [same]

theorem program (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (work :OracleComp RegistrationAgreementExecutor.Spec A) (captured :Capture R) (before :Backend n KemSK)
    (related :before.auxiliary=AdapterPublicAgreementServerWorld.project view captured) (previous :P) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     (((simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys) work).run captured).run.run before).run previous)=
    (fun result=>((RustM.ok result.1.1,install view result.1.1.2 result.1.2),result.2)) <$>
      ((sample coins ((simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys) work).run captured)).run before).run previous :=by
  induction work using OracleComp.inductionOn generalizing captured before previous with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,RustT.run_pure,sample_pure]
    simp only [map_pure]
    have same :install view captured before=before:=by
      unfold install
      rw [←related]
    rw [same]
  | query_bind request next ih=>
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,RustT.run_bind]
    rw [query setup checks view generator model coins keys request captured before related previous]
    simp only [bind_map_left]
    simp only [sample_bind,StateT.run_bind]
    simp only [map_bind]
    apply bind_congr
    intro result
    rw [ih result.1.1.1 result.1.1.2 (install view result.1.1.2 result.1.2) rfl result.2]
    rw [sample_install]
    simp only [Functor.map_map,install]

include model in
theorem captured (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (work :OracleComp RegistrationAgreementExecutor.Spec A) (rng :R) (before :Backend n KemSK)
    (empty :before.auxiliary=RegistrationServerRoleBackend.empty) (previous :P) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     (((simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys)
       (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng,.None,.None⟩).run.run before).run previous)=
    (fun result=>((result.1.1,match result.1.1 with
      | .ok value=>install view value.2 result.1.2
      | .fail _ | .div=>result.1.2),result.2)) <$>
      ((RegistrationNativePlatformPublicAdapterAcceptReceipt.capture coins generator keys work rng).run before).run previous :=by
  have normal :((RegistrationNativePlatformPublicAdapterAcceptReceipt.capture coins generator keys work rng).run before).run previous=
      (fun result=>((RustM.ok result.1.1,result.1.2),result.2)) <$>
        ((sample coins ((simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys)
          (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng,.None,.None⟩)).run before).run previous :=by
    unfold RegistrationNativePlatformPublicAdapterAcceptReceipt.capture
    rw [RegistrationNativePlatformPublicAdapterCrypto.captured_source,AdapterPublicAgreementPrimitiveModel.program model keys]
    change ((transform coins (RustT.lift _)).run.run before).run previous=_
    rw [transform_lift,RustT.run_lift,StateT.run_map,StateT.run_map]
  rw [normal,Functor.map_map]
  exact program setup checks view generator model coins keys (RegistrationAgreementQueryTrace.trace work [])
    ⟨rng,.None,.None⟩ before empty previous

theorem trace_erasure (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (work :OracleComp RegistrationAgreementExecutor.Spec A) (captured :Capture R) :
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
    (fun result=>(result.1.1,result.2)) <$>
      (simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys)
        (RegistrationAgreementQueryTrace.trace work [])).run captured=
      (simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys) work).run captured :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  have erased:=congrArg (fun tree=>
    (simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys) tree).run captured)
    (RegistrationAgreementQueryTrace.erasure work [])
  simpa only [simulateQ_map,StateT.run_map] using erased

theorem execute_trace (coins :QueryImpl unifSpec (StateT P ProbComp)) (keys :Keys)
    (control :pqxdh.ServerState) (status :pqxdh.RegistrationStatus) (authenticated :registration.AuthenticatedInit) (rng :R) :
    let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
    (do let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control status authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m:=RustT PhysicalM) generator phase keys rng)=
      (do let ((effect,_journal),after)←(simulateQ (AdapterPublicAgreementInterpreter.handler (m:=PhysicalM) generator keys)
          (RegistrationAgreementQueryTrace.trace (RegistrationAgreementExecutor.server control status authenticated) [])).run ⟨rng,.None,.None⟩
          let completed←AdapterRecordRequestMonad.liftRust effect
          pure (completed,after.rng)) :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  dsimp only
  rw [AdapterPublicAgreementSourceEntries.server (m:=PhysicalM) generator keys control status authenticated rng]
  unfold AdapterPublicAgreementSourceEntries.run
  rw [←trace_erasure view generator coins keys (RegistrationAgreementExecutor.server control status authenticated) ⟨rng,.None,.None⟩]
  rw [bind_map_left]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.transform_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.transform_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.pure_transform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.pure_transform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.observe_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.observe_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_facts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.original_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.original_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.original_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.original_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.public_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.generation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.generated_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.generated_capture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.nongenerate_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.nongenerate_capture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.sample_install

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.nongenerate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.nongenerate_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.captured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.trace_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.trace_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.execute_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.execute_trace
