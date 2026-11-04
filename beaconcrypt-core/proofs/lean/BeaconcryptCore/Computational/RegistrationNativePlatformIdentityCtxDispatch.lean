-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild
/-! Every actual non-Beacon callback uses the same explicit CTX backend, private context and persistent platform. Accept and build retain their literal source SDK and all other cases retain the actual dynamic ordinary frame dictionary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret project)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned native oldBefore)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def context (query : TypedSpec.Domain) (owners : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativePlatformCtxContext.M n KemSK Platform (TypedSpec.Range query) :=
  match query with
  | .inr (.accept packet) => RegistrationNativePlatformCtxAccept.accept setup checks reserveRegistration source.verify representation created packet
  | .inr (.build handle application) => RegistrationNativePlatformCtxBuild.build setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
      keys failure allocation erased (RegistrationNativeMldsa.owned source credential) helper writer reservePeer handle application
  | query => RegistrationNativePlatformCtxCommands.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route
      (owners.map (fun selected => selected.worldOwner)) query

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.command

/-- All non-Beacon cases recover the exact literal Context callback, with individual source obligations discharged rather than assumed. -/
theorem context_source (query : TypedSpec.Domain) (allowed : RegistrationNativePlatformIdentityAmbient.nonBeacon query)
    (owners : RegistrationNativeIdentityFrontend.State source) (before : RegistrationNativePlatformCtxContext.Full n KemSK Platform) :
    Prod.map id RegistrationNativePlatformCtxContext.realize <$>
      (RegistrationNativePlatformCtxContext.interpret (context setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query owners)).run before =
      (RegistrationNativePlatformIdentityMainAmbient.command setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query owners).run (RegistrationNativePlatformCtxContext.realize before) := by
  cases query with
  | inl coin => apply RegistrationNativePlatformCtxCommands.runtime_source; trivial
  | inr query => cases query with
    | create edPin mlPin keyId | bundle index | finish index packet => cases allowed
    | accept packet => apply RegistrationNativePlatformCtxAccept.runtime_source
    | build handle application => apply RegistrationNativePlatformCtxBuild.runtime_source
    | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw =>
      apply RegistrationNativePlatformCtxCommands.runtime_source
      trivial

noncomputable def step (query : TypedSpec.Domain) : M n KemSK Platform source (TypedSpec.Range query) := fun before =>
  (RegistrationNativePlatformIdentityCtxOrdinary.ordinary
    (context setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before.1.beacons)).run before

omit primitive in
private theorem owners_view (pool : PqxdhDynamicIdentityPool.SourceState) (owners : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativeIdentityRealization.owners (RegistrationNativeIdentityCompiler.poolView pool) owners =
      RegistrationNativeIdentityRealization.owners pool owners := rfl

omit primitive in
private theorem ordinary_native (joint : PqxdhJointIdentity.Primitives)
    (left : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (right : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp A)
    (law : ∀ current, Prod.map id RegistrationNativePlatformCtxContext.realize <$>
      (RegistrationNativePlatformCtxContext.interpret left).run current = right.run (RegistrationNativePlatformCtxContext.realize current))
    (before : Full n KemSK Platform source) :
    Prod.map id native <$> (interpret joint (RegistrationNativePlatformIdentityCtxOrdinary.ordinary left)).run before =
      Prod.map id RegistrationNativePlatformIdentityMain.project <$>
        (RegistrationNativePlatformIdentityMain.interpret joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary right)).run (oldBefore before) := by
  have actual := RegistrationNativePlatformIdentityCtxOrdinary.ordinary_source joint left before
  rw [law] at actual
  have mapped := congrArg (fun distribution => Prod.map id RegistrationNativePlatformIdentityMain.project <$> distribution) actual
  have prior := RegistrationNativePlatformIdentityMainOrdinary.ordinary_source joint right (oldBefore before)
  calc
    _ = (fun result => (result.1,
      (RegistrationNativeIdentityMainOrdinary.attach (RegistrationNativeIdentityRealization.owners before.2.1 before.1.1.beacons) result.2.1, result.2.2))) <$>
      right.run (RegistrationNativePlatformCtxContext.realize ((before.1.1.context, before.1.2), before.2.2)) := by
        simpa only [Functor.map_map, native, RegistrationNativePlatformIdentityCtxOrdinary.attach,
          RegistrationNativePlatformIdentityMain.project, RegistrationNativeIdentityMainSource.project,
          RegistrationNativeIdentityMainOrdinary.attach, owners_view, Prod.map_def, id_eq] using mapped
    _ = _ := by
      simpa only [oldBefore, RegistrationNativePlatformCtxContext.realize] using prior.symm

/-- Each actual non-Beacon runtime callback restores every native owner, private KEM row, cost and external poststate. -/
theorem step_source (query : TypedSpec.Domain) (allowed : RegistrationNativePlatformIdentityAmbient.nonBeacon query)
    (before : Full n KemSK Platform source) :
    Prod.map id native <$> (interpret setup.joint (step setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential keys failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer query).run (native before).1).run (native before).2 := by
  have first := ordinary_native setup.joint
    (context setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before.1.1.beacons)
    (RegistrationNativePlatformIdentityMainAmbient.command setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before.1.1.beacons)
    (context_source setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query allowed before.1.1.beacons) before
  exact first.trans (RegistrationNativePlatformIdentityMainAmbient.step_source setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query allowed (oldBefore before))

omit primitive in
/-- Arbitrary shared-CTX ordinary work cannot create, delete or expose any generated identity row. -/
theorem ordinary_owned (joint : PqxdhJointIdentity.Primitives)
    (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (before : Full n KemSK Platform source) (result : A × Full n KemSK Platform source)
    (owned : Owned joint before)
    (reached : result ∈ support ((interpret joint (RegistrationNativePlatformIdentityCtxOrdinary.ordinary work)).run before)) :
    Owned joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id project) reached
  rw [← support_map, RegistrationNativePlatformIdentityCtxOrdinary.ordinary_source, support_map] at viewed
  obtain ⟨inner, _supported, equal⟩ := viewed
  have retained : RegistrationNativePlatformIdentityMainOwned.Owned joint (RegistrationNativePlatformIdentityCtxOrdinary.attach before inner).2 := owned
  have shifted := congrArg (fun output => RegistrationNativePlatformIdentityMainOwned.Owned joint output.2) equal
  have carried : RegistrationNativePlatformIdentityMainOwned.Owned joint (project result.2) := shifted ▸ retained
  exact carried

/-- The actual ambient dispatcher preserves genuine ownership on every success or failure. -/
theorem step_owned (query : TypedSpec.Domain) (before : Full n KemSK Platform source)
    (result : TypedSpec.Range query × Full n KemSK Platform source) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (step setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)).run before)) :
    Owned setup.joint result.2 :=
  ordinary_owned setup.joint (context setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query before.1.1.beacons) before result owned reached
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.context_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.context_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.step_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.ordinary_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.ordinary_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.step_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch.step_owned
