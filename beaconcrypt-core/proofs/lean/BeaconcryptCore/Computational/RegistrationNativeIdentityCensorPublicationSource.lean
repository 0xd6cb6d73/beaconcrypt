-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrekeySource

/-! The complete literal Main publication dictionary closes to the actual original Core begin with the same mutable source writer. No current hash/signature callback or external writer equation is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
variable {n : Nat} {I KemSK Platform E A B Q : Type} {base : OracleSpec I} {spec : OracleSpec Q} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "external(" work ")" => Main (RegistrationNativePlatformIdentityProgram.external work)
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))
local notation "callback(" censored ")" => (fun query => source(censored, action(query)))
local notation "encoder(" censored ")" => (fun fields => source(censored, external(RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)))

private theorem external_pure (value : A) : external((pure value : StateT Platform ProbComp A)) = pure value := by
  funext before
  change (external((pure value : StateT Platform ProbComp A))).run before = (pure value : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A).run before
  rw [RegistrationNativeIdentityCensorExternalSource.native setup checks representation created]
  simp only [StateT.run_pure, simulateQ_pure, map_pure]

private theorem external_bind (work : StateT Platform ProbComp A) (next : A → StateT Platform ProbComp B) :
    external(work >>= next) = (do let value ← external(work); external(next value)) := by
  funext before
  change (external(work >>= next)).run before = ((do let value ← external(work); external(next value)) : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource B).run before
  simp only [RegistrationNativeIdentityCensorExternalSource.native, StateT.run_bind,
    simulateQ_bind, map_bind, bind_map_left]

private theorem external_program (censored : Bool) (handler : QueryImpl spec (StateT Platform ProbComp)) (work : OracleComp spec A) :
    source(censored, external(simulateQ handler work)) =
      simulateQ (fun query => source(censored, external(handler query))) work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
    rw [simulateQ_pure, external_pure, RegistrationNativeIdentityCensorSourceFold.pure_source, simulateQ_pure]
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, external_bind, RegistrationNativeIdentityCensorSourceFold.bind_source]
    simp only [ih, simulateQ_bind, simulateQ_spec_query]

/-- Literal source binding from the actual Main dictionary to the original three-Ed/hash/Ready controller and its entire concrete stateful writer. -/
theorem source (censored : Bool) (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    source(censored, Main (simulateQ
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E control inputs coins pin))) =
      RegistrationNativePlatformBeaconPublication.begin (callback(censored)) (encoder(censored)) control inputs coins pin := by
  rw [RegistrationNativeIdentityCensorSourceFold.publication,
    RegistrationNativePlatformWriter.begin_interpret]
  have writer : (fun fields => simulateQ
      (fun query => source(censored, Main (RegistrationNativePlatformIdentityPublication.callback setup index owner (RegistrationNativePlatformConcreteSource.writer reserve) (.inr query))))
      (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit (E := E)
        (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket fields)).run) = encoder(censored) := by
    funext fields
    change simulateQ (fun query => source(censored, external(RegistrationNativePlatformConcreteSource.writer reserve query))) _ = _
    exact (external_program setup checks representation created selected placeholder censored
      (RegistrationNativePlatformConcreteSource.writer reserve) _).symm
  rw [writer]
  rfl

/-- The actual Main publication has the canonical/placeholder failed-publication coupling from the original begin gate, after the first chronological selection condition is established. -/
theorem paired (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (started : pqxdh.BeaconStart) (built : pqxdh.beacon_start control inputs coins = .ok started)
    (lineage : inputs.identity_public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    let publication := Main (simulateQ
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E control inputs coins pin))
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$> (source(false, publication)).run before =
      Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$> (source(true, publication)).run before := by
  dsimp only
  rw [source, source]
  exact RegistrationNativeIdentityCensorPrekeySource.begin setup checks representation created selected index owner placeholder reserve
    control inputs coins pin started built lineage before seed handle armed held sourceTarget fresh found

/-- Actual Main closing and concrete source serialization preserve the normal-return property on every reached result, without any selection or success condition. -/
theorem normal (censored : Bool) (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (possible : result ∈ support ((source(censored, Main (simulateQ
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E control inputs coins pin)))).run before)) :
    RegistrationNativeIdentityCensorPublicationNormal.Normal result.1 := by
  rw [source] at possible
  exact RegistrationNativeIdentityCensorPrekeySource.normal setup checks representation created selected index owner placeholder reserve
    control inputs coins pin censored before result possible

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource.paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource.normal
