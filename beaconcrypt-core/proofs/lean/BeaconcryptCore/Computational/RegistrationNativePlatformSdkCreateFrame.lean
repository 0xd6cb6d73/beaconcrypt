-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame
import BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant
import BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth
import BeaconcryptCore.Refinement.AdapterPublicMaterialFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Trusted Owner)
variable {n : Nat} {I KemSK A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

def Keys (before after : PqxdhLiveKemBirth.Pool KemSK) : Prop :=
  ∀(index : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey×KemSK),before.keys[index]?=some pair → after.keys[index]?=some pair

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
theorem phase_keys (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before after : PqxdhLiveKemBirth.Pool KemSK) (owner : Owner source)
    (stored : beaconcrypt_public_wrapper.beacon.BeaconState) (world : Option PqxdhRecordLiftBeacon.Phase)
    (held : AdapterPublicWrapperState.Phase view before owner stored world) (keys : Keys before after) :
    AdapterPublicWrapperState.Phase view after owner stored world := by
  cases stored <;>cases phase:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,phase] at held ⊢
  all_goals first
    | exact held
    | exact ⟨held.1,held.2.1,⟨held.2.2.1.1,keys _ _ held.2.2.1.2⟩,held.2.2.2⟩
    | exact ⟨held.1,held.2.1,held.2.2.1,⟨held.2.2.2.1.1,keys _ _ held.2.2.2.1.2⟩,held.2.2.2.2⟩

theorem material_keys (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (before after : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (held : AdapterPublicWrapperState.Beacon view joint before self owner world) (keys : Keys before after) :
    AdapterPublicWrapperState.Beacon view joint after self owner world :=
  ⟨held.identityPublic,held.identitySecret,held.pin,held.serverPublic,held.identifier,
    phase_keys view before after owner self.state world held.phase keys⟩

omit material ed in
theorem trusted_keys (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (Trusted n KemSK).Domain) (before : Native) (result : (Trusted n KemSK).Range query×Native)
    (supported : result∈support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    Keys before.pool result.2.pool := by
  have step:=RegistrationNativeKemBirthInvariant.trusted_step setup checks representation created source query before result.2 result.1 supported
  exact RegistrationNativeKemBirthPool.lookup_step setup.baseImpl setup.kem before.pool result.2.pool step

omit material ed in
def Allowed : (Trusted n KemSK).Domain → Prop
  | .inl (.inl _) | .inl (.inr (.hash _)) | .inl (.inr (.appendOwner ..)) | .inr _=>True
  | _=>False

omit material ed in
def Frame (before after : Native) : Prop :=
  RegistrationNativePlatformSdkServerFrame.image after=RegistrationNativePlatformSdkServerFrame.image before ∧
  before.server.world.world.1.owners <+: after.server.world.world.1.owners ∧ Keys before.pool after.pool

omit material ed in
private theorem safe_frame (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (Trusted n KemSK).Domain) (safe : RegistrationNativeWorldOwnerFrame.Safe query)
    (before : Native) (result : (Trusted n KemSK).Range query×Native)
    (supported : result∈support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    Frame before result.2 := by
  refine ⟨RegistrationNativePlatformSdkServerFrame.trusted setup checks representation created query safe before result supported,?_,trusted_keys setup checks representation created query before result supported⟩
  rw [RegistrationNativeWorldOwnerFrame.trusted setup checks representation created query safe before result supported]

omit material ed in
theorem query (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (Trusted n KemSK).Domain) (allowed : Allowed query)
    (before : Native) (result : (Trusted n KemSK).Range query×Native)
    (supported : result∈support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    Frame before result.2 := by
  cases query with
  | inr lower=>exact safe_frame setup checks representation created (.inr lower) trivial before result supported
  | inl effect=>cases effect with
    | inl coin=>exact safe_frame setup checks representation created (.inl (.inl coin)) trivial before result supported
    | inr capability=>cases capability with
      | hash bytes=>exact safe_frame setup checks representation created (.inl (.inr (.hash bytes))) trivial before result supported
      | appendOwner sender identity phase=>
        have keys:=trusted_keys setup checks representation created (.inl (.inr (.appendOwner sender identity phase))) before result supported
        simp only [RegistrationNativeExperiment.trusted,RegistrationNativeExperiment.world,RegistrationNativeExperiment.server,
          PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run,map_pure,support_pure,Set.mem_singleton_iff] at supported
        cases supported
        exact ⟨rfl,List.prefix_append _ _,keys⟩
      | _=>exact allowed.elim

omit material ed in
theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Trusted n KemSK) A) (allowed : AllQueriesSatisfy work (Allowed (n:=n) (KemSK:=KemSK)))
    (before : Native) (result : A×Native)
    (supported : result∈support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    Frame before result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨rfl,⟨[],by simp⟩,fun _ _ found=>found⟩
  | query_bind request next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩:=supported
    have first:=query setup checks representation created request allowed.1 before middle called
    have later:=ih middle.1 (allowed.2 middle.1) middle.2 result continued
    exact ⟨later.1.trans first.1,first.2.1.trans later.2.1,fun index pair found=>later.2.2 index pair (first.2.2 index pair found)⟩
section SourceSyntax
open RegistrationNativeBeaconFrontend
open RegistrationNativeHiddenAllocationCore (mapped)
variable {Auxiliary : Type}
private def Safe (predicate : (Trusted n KemSK).Domain → Prop)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) : Prop :=
  ∀owners environment,AllQueriesSatisfy ((work.run owners).run environment) predicate
omit material ed in
private theorem pure_safe (predicate : (Trusted n KemSK).Domain → Prop) (value : A) :
    Safe (source:=source) (Auxiliary:=Auxiliary) predicate (pure value) := by
  intro owners environment
  simp only [StateT.run_pure]
  trivial
omit material ed in
private theorem bind_safe (predicate : (Trusted n KemSK).Domain → Prop)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (next : A → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary B)
    (first : Safe predicate work) (later : ∀value,Safe predicate (next value)) : Safe predicate (work>>=next) := by
  intro owners environment
  rw [StateT.run_bind,StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners environment) fun middle=>later middle.1.1 middle.1.2 middle.2
omit material ed in
private theorem effect_safe (predicate : (Trusted n KemSK).Domain → Prop)
    (request : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (allowed : predicate (.inl request)) :
    Safe (source:=source) (Auxiliary:=Auxiliary) predicate (effect request) := by
  intro owners environment
  simp only [effect,StateT.run_lift,StateT.run_map,bind_pure_comp,Functor.map_map]
  exact mapped _ _ predicate ((allQueriesSatisfy_query_iff _ _).mpr allowed)
omit material ed in
private theorem sample_safe (predicate : (Trusted n KemSK).Domain → Prop)
    (coins : ∀coin,predicate (.inl (.inl coin))) (work : ProbComp A) :
    Safe (source:=source) (Auxiliary:=Auxiliary) predicate (sample work) := by
  induction work using OracleComp.inductionOn with
  | pure value=>exact pure_safe predicate value
  | query_bind query next ih=>
    simp only [sample,simulateQ_bind,simulateQ_spec_query]
    exact bind_safe predicate _ _ (effect_safe predicate _ (coins query)) ih

omit material ed in
theorem prepare_safe (predicate : (Trusted n KemSK).Domain → Prop)
    (coins : ∀coin,predicate (.inl (.inl coin))) (hashes : ∀bytes,predicate (.inl (.inr (.hash bytes))))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    AllQueriesSatisfy (((prepare (n:=n) (KemSK:=KemSK) source edPin mlPin keyId).run owners).run environment) predicate := by
  have _hashes := hashes
  have safe : Safe (source:=source) (Auxiliary:=Auxiliary) predicate (prepare (n:=n) (KemSK:=KemSK) source edPin mlPin keyId) := by
    rw [RegistrationNativeBeaconCreateProgram.prepare_program]
    unfold RegistrationNativeBeaconCreateProgram.program
    apply bind_safe predicate _ _ (sample_safe predicate coins _)
    intro identity
    exact bind_safe predicate _ _ (sample_safe predicate coins _) fun _=>pure_safe predicate _
  exact safe owners environment

omit material ed in
theorem create_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    AllQueriesSatisfy (((create setup source edPin mlPin keyId).run owners).run environment) (Allowed (n:=n) (KemSK:=KemSK)) := by
  rw [RegistrationNativeBeaconBirth.create_program]
  apply allQueriesSatisfy_bind (prepare_safe _ (fun _=>trivial) (fun _=>trivial) edPin mlPin keyId owners environment)
  rintro ⟨⟨earlier,current⟩,env⟩
  cases earlier with
  | fail error | div=>trivial
  | ok optional=>cases optional with
    | none=>trivial
    | some prepared=>
      dsimp only
      rw [RegistrationNativeBeaconBirth.append_program]
      apply allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial)
      intro born
      apply allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial)
      intro worldOwner
      trivial
end SourceSyntax

omit material ed in
theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Native) (result : RustM (Option Nat)×Native)
    (supported : result∈support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    Frame before result.2 := by
  simp only [RegistrationNativeExperiment.beacon,StateT.run,mem_support_bind_iff] at supported
  obtain ⟨middle,called,returned⟩:=supported
  simp only [support_pure,Set.mem_singleton_iff] at returned
  cases returned
  exact program setup checks representation created _ (create_safe setup edPin mlPin keyId _ _) before middle called

omit material ed in
def Roster (before : RegistrationNativeBeaconFrontend.State source) (reply : RustM (Option Nat))
    (after : RegistrationNativeBeaconFrontend.State source) : Prop :=
  match reply with
  | .ok (some index)=>index=before.length ∧∃owner,after=before++[owner]
  | _=>after=before

omit material ed in
private theorem source_support {Private Value Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT Private ProbComp)) (work : OracleComp spec Value)
    (before : Private) (result : Value×Private)
    (supported : result∈support ((simulateQ implementation work).run before)) : result.1∈support work := by
  apply OracleComp.support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq,support_map]
  exact ⟨result,supported,rfl⟩

omit material ed in
theorem appended (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (sender : U64) (identity : Std.Array U8 32#usize) (phase : PqxdhRecordLiftInterface.InactivePhase)
    (before : Native) (result : Nat×Native)
    (supported : result∈support ((RegistrationNativeExperiment.trusted setup checks representation created source
      (.inl (.inr (.appendOwner sender identity phase)))).run before)) :
    result.1=before.server.world.world.1.owners.length ∧
      result.2.server.world.world.1.owners=before.server.world.world.1.owners++[.inactive phase] := by
  simp only [RegistrationNativeExperiment.trusted,RegistrationNativeExperiment.world,RegistrationNativeExperiment.server,
    PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run,map_pure,support_pure,Set.mem_singleton_iff] at supported
  cases supported
  exact ⟨rfl,rfl⟩

omit material ed in
theorem layout_source {Auxiliary : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (environment : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : Native) (allocated : before.server.world.world.1.owners.length=owners.length)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed owners)
    (result : ((RustM (Option Nat)×RegistrationNativeBeaconFrontend.State source)×RegistrationWorldAgreementCompiler.EnvState Auxiliary)×Native)
    (supported : result∈support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run environment)).run before)) :
    Roster owners result.1.1.1 result.1.1.2 ∧
      result.2.server.world.world.1.owners.length=result.1.1.2.length ∧
      RegistrationNativeHiddenAllocationOwners.NativeIndexed result.1.1.2 := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,earlier,continued⟩:=supported
  have unchanged:=RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners environment middle.1
    (source_support _ _ before middle earlier)
  have worldSame:=RegistrationNativeWorldOwnerFrame.program setup checks representation created _
    (prepare_safe _ (fun _=>trivial) (fun _=>trivial) edPin mlPin keyId owners environment) before middle earlier
  have leadingLength:middle.2.server.world.world.1.owners.length=middle.1.1.2.length := by
    rw [worldSame,unchanged,allocated]
  have leadingIndexed:RegistrationNativeHiddenAllocationOwners.NativeIndexed middle.1.1.2 := by
    rw [unchanged]
    exact indexed
  cases selected:middle.1.1.1 with
  | fail error | div=>
    simp only [selected,simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at continued
    cases continued
    exact ⟨unchanged,leadingLength,leadingIndexed⟩
  | ok optional=>cases optional with
    | none=>
      simp only [selected,simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at continued
      cases continued
      exact ⟨unchanged,leadingLength,leadingIndexed⟩
    | some prepared=>
      simp only [selected] at continued
      obtain ⟨born,afterBorn,worldOwner,afterAppend,generated,appendedAt,returned⟩:=
        RegistrationNativeBeaconBirth.append_supported setup source
          (RegistrationNativeExperiment.trusted setup checks representation created source) edPin keyId prepared.pin
          prepared.identity prepared.prekey middle.1.1.2 middle.1.2 middle.2 result continued
      have kemSame:=RegistrationNativeWorldOwnerFrame.trusted setup checks representation created
        (.inr (.inr (.inl .create))) trivial middle.2 (born,afterBorn) generated
      have appendReceipt:=appended setup checks representation created keyId edPin .fresh afterBorn (worldOwner,afterAppend) appendedAt
      cases returned
      refine ⟨?_,?_,?_⟩
      · simp only [Roster,unchanged]
        exact ⟨trivial,_,rfl⟩
      · rw [appendReceipt.2,List.length_append,List.length_singleton,kemSame,leadingLength]
        simp only [List.length_append,List.length_singleton]
      · apply RegistrationNativeHiddenAllocationOwners.append _ _ leadingIndexed
        change worldOwner=middle.1.1.2.length
        exact appendReceipt.1.trans ((congrArg List.length kemSame).trans leadingLength)

omit material ed in
theorem layout (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Native) (allocated : before.server.world.world.1.owners.length=before.beacons.length)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (result : RustM (Option Nat)×Native)
    (supported : result∈support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    Roster before.beacons result.1 result.2.beacons ∧
      result.2.server.world.world.1.owners.length=result.2.beacons.length ∧
      RegistrationNativeHiddenAllocationOwners.NativeIndexed result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon,StateT.run,mem_support_bind_iff] at supported
  obtain ⟨middle,called,returned⟩:=supported
  simp only [support_pure,Set.mem_singleton_iff] at returned
  cases returned
  exact layout_source setup checks representation created edPin mlPin keyId before.beacons
    (RegistrationWorldAgreementCompiler.erase before.server.world) before allocated indexed middle called

omit material ed in
private theorem roster_lookup (before after : RegistrationNativeBeaconFrontend.State source)
    (reply : RustM (Option Nat)) (shape : Roster before reply after)
    (index : Nat) (owner : Owner source) (found : before[index]?=some owner) : after[index]?=some owner := by
  cases reply with
  | fail error | div=>rw [shape];exact found
  | ok optional=>cases optional with
    | none=>rw [shape];exact found
    | some target=>
      obtain ⟨_same,current,extended⟩:=shape
      rw [extended,List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
      exact found

theorem old_material [PublicWrapperPlatform.Platform]
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (before after : Native) (reply : RustM (Option Nat)) (frame : Frame before after)
    (shape : Roster before.beacons reply after.beacons)
    (allocated : before.server.world.world.1.owners.length=before.beacons.length)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (index : Nat) (owner : Owner source) (found : before.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (held : AdapterPublicWrapperState.Beacon view joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?) :
    after.beacons[index]?=some owner ∧
      AdapterPublicWrapperState.Beacon view joint after.pool self owner after.server.world.world.1.owners[owner.worldOwner]? := by
  have address:=indexed index owner found
  have bound:index<before.server.world.world.1.owners.length := by
    rw [allocated]
    exact (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨suffix,extended⟩:=frame.2.1
  have sameSlot:after.server.world.world.1.owners[owner.worldOwner]?=before.server.world.world.1.owners[owner.worldOwner]? := by
    rw [←extended,address,List.getElem?_append_left bound]
  refine ⟨roster_lookup before.beacons after.beacons reply shape index owner found,?_⟩
  rw [sameSlot]
  exact material_keys view joint before.pool after.pool self owner _ held frame.2.2

omit material ed in
theorem platform {P : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Native) (previous : P) (allocated : before.server.world.world.1.owners.length=before.beacons.length)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (result : (RustM (Option Nat)×Native)×P)
    (supported : result∈support (((RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))).run before).run previous)) :
    Frame before result.1.2 ∧ Roster before.beacons result.1.1 result.1.2.beacons ∧
      result.1.2.server.world.world.1.owners.length=result.1.2.beacons.length ∧
      RegistrationNativeHiddenAllocationOwners.NativeIndexed result.1.2.beacons := by
  have called:=RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 supported
  exact ⟨native setup checks representation created edPin mlPin keyId before result.1 called,
    layout setup checks representation created edPin mlPin keyId before allocated indexed result.1 called⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.phase_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.phase_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.material_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.material_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.trusted_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.trusted_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.prepare_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.prepare_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.create_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.create_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.appended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.appended

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.layout_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.layout_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.layout

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.old_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.old_material

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame.platform
