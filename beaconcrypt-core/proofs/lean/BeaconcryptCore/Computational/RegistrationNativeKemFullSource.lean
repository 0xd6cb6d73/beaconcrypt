-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint
import BeaconcryptCore.Computational.RegistrationNativeKemSelectedSource

/-! The complete original raw native client has a genuine selected-first indexed KEM source. Capacity and zero-reveal conditions are derived from its actual controllers and original public budget, not supplied as source-game premises. The full native local state and original ledger survive reservation; selected private keys remain in the source comparison only. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFullSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemParsedRouting (Spec Ambient)
open RegistrationNativeKemReservation (IsCreate)
open RegistrationNativeKemPoolSource (IsReveal)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

noncomputable def program (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (parsed : Nat) :
    OracleComp (Spec n mlSource KemSK) (Value × RegistrationNativeLedger.State) :=
  simulateQ (RegistrationNativeKemParsedRouting.handler setup checks wire parsed)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)

private theorem create_predicate :
    RegistrationNativeKemCompilerFootprint.predicate (Ambient n mlSource) KemSK .create =
      IsCreate (ambient := Ambient n mlSource) (KemSK := KemSK) := by
  funext query
  apply propext
  rcases query with other | (pool | key)
  · rfl
  · cases pool <;> simp [RegistrationNativeKemCompilerFootprint.predicate, IsCreate]
  · rfl

private theorem reveal_predicate :
    RegistrationNativeKemCompilerFootprint.predicate (Ambient n mlSource) KemSK .reveal =
      IsReveal (ambient := Ambient n mlSource) (KemSK := KemSK) := by
  funext query
  apply propext
  rcases query with other | (pool | key)
  · rfl
  · cases pool <;> simp [RegistrationNativeKemCompilerFootprint.predicate, IsReveal]
  · rfl

/-- The actual original full raw program's private key births fit its original public create cap. -/
theorem creates (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (parsed : Nat) :
    (program (n := n) (mlSource := mlSource) setup checks wire serverKeyId bounds mode work parsed).IsQueryBoundP
      (IsCreate (ambient := Ambient n mlSource) (KemSK := KemSK)) budget.create := by
  simpa only [program, create_predicate] using
    RegistrationNativeKemFullFootprint.full_creates (n := n) (mlSource := mlSource) setup checks wire serverKeyId bounds mode work budget bounded parsed

/-- The actual original full raw program never requests any private KEM secret key. -/
theorem no_reveal (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (parsed : Nat) :
    (program (n := n) (mlSource := mlSource) setup checks wire serverKeyId bounds mode work parsed).IsQueryBoundP
      (IsReveal (ambient := Ambient n mlSource) (KemSK := KemSK)) 0 := by
  simpa only [program, reveal_predicate] using
    RegistrationNativeKemFullFootprint.full_no_reveal (n := n) (mlSource := mlSource) setup checks wire serverKeyId bounds mode work parsed

/-- The full original native program realizes a genuine selected-first private key family, with all ledger and source fields retained and both resource obligations discharged. -/
theorem selected_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (parsed : Nat) (selected : Fin (budget.create + 1))
    (localState : RegistrationNativeKemServerState.State n mlSource) :
    EvalDistEq
      ((fun result => (some result.1, result.2)) <$>
        (simulateQ (RegistrationNativeKemParsedRouting.source setup checks wire route representation created credential)
          (program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run
            (localState, PqxdhLiveKemBirth.empty))
      (do let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
          let others ← PqxdhLiveKemSelection.sampleFamily
            (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) budget.create
          let pairs := List.ofFn (selected.insertNth chosen others)
          Prod.map id (RegistrationNativeKemPoolSource.project pairs) <$>
            (((simulateQ (RegistrationNativeKemGame.stopped setup.baseImpl setup.kem
              (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
              selected.val pairs)
              (program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run
                (localState, PqxdhDynamicKemRouter.empty))) := by
  exact RegistrationNativeKemSelectedSource.selected_source setup.baseImpl setup.kem _ _ budget.create selected
    ((creates setup checks wire created.server.server.metadata.sender bounds mode work budget bounded parsed).mono (Nat.le_succ _))
    (no_reveal setup checks wire created.server.server.metadata.sender bounds mode work parsed) localState

end BeaconcryptCore.Computational.RegistrationNativeKemFullSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullSource.creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullSource.creates
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullSource.no_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullSource.no_reveal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullSource.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullSource.selected_source
