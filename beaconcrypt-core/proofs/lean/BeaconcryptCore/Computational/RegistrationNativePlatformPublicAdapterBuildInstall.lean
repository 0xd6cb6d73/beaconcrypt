-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries
/-! Actual source map entry and vacant insertion lift through analysis state while preserving the exact returned Server/map lens and persistent platform state. This includes the parser and every Rust failure; no installation/controller law is assumed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK P A B : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "Base"=>StateT P ProbComp
local notation "M"=>StateT (RegistrationNativePlatformCutJournal.State Native) Base
local notation "lifted"=>RegistrationNativePlatformPublicAdapterLeaves.lift (S:=RegistrationNativePlatformCutJournal.State Native)

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem base_pure (value : A) : (StateT.lift (pure value : Base A) : M A)=pure value := by
  apply StateT.ext
  intro current
  simp only [StateT.run_lift,pure_bind,StateT.run_pure]

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem base_bind (work : Base A) (next : A→Base B) :
    (StateT.lift (work >>=next) : M B)=(StateT.lift work >>=fun value=>StateT.lift (next value)) := by
  apply StateT.ext
  intro current
  simp only [StateT.run_lift,StateT.run_bind,bind_assoc,pure_bind]

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lifted_pure (value : A) :lifted (pure value :RustT Base A)=pure value := by
  apply RustT.ext
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_pure]
  exact base_pure _

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lifted_rust (value :RustM A) :
    lifted (AdapterRecordRequestMonad.liftRust value : RustT Base A)=AdapterRecordRequestMonad.liftRust value := by
  apply RustT.ext
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_liftRust]
  exact base_pure _

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lifted_bind (work :RustT Base A) (next :A→RustT Base B) :
    lifted (work >>=next)=(lifted work >>=fun value=>lifted (next value)) := by
  apply RustT.ext
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_bind,base_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [base_pure]

theorem install (original : ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (pending :peer.PeerInsert (alloc.vec.Vec U8)) :
    let : ContainerOperations (RustT Base):=original
    let : ContainerOperations (RustT M):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=source) original
    AdapterPublicServerBuildBody.install (m:=M) self pending=
      lifted (AdapterPublicServerBuildBody.install (m:=Base) self pending) := by
  let : ContainerOperations (RustT Base):=original
  let : ContainerOperations (RustT M):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=source) original
  dsimp only
  unfold AdapterPublicServerBuildBody.install AdapterPublicServerBuildBody.checked
  simp only [lifted_bind,lifted_rust]
  congr 1
  funext identifier
  congr 1
  funext parts
  congr 1
  funext binding
  congr 1
  funext identity
  congr 1
  funext parsed
  cases parsed with
  | Err error=>exact (lifted_pure _).symm
  | Ok publicKey=>
    simp only [lifted_bind]
    congr 1
    funext result
    rcases result with ⟨entry,back⟩
    cases entry with
    | Occupied entry=>
      rw [AdapterPublicServerInstall.finish,AdapterPublicServerInstall.finish]
      exact (lifted_pure _).symm
    | Vacant vacant=>
      dsimp only
      rw [AdapterPublicServerInstall.remote_source ({pending with peer:=parts.1}),
        AdapterPublicServerInstall.remote_source ({pending with peer:=parts.1})]
      simp only [pure_bind,lifted_bind,AdapterPublicServerInstall.finish,lifted_pure]
      rfl

theorem after_publication (original : ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server)
    (published :RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :
    let : ContainerOperations (RustT Base):=original
    let : ContainerOperations (RustT M):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=source) original
    AdapterPublicServerPublication.afterPublication (m:=M) self published=
      StateT.lift (AdapterPublicServerPublication.afterPublication (m:=Base) self published) := by
  let : ContainerOperations (RustT Base):=original
  let : ContainerOperations (RustT M):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=source) original
  dsimp only
  cases published with
  | fail error | div=>exact (base_pure _).symm
  | ok published=>cases published with
    | Err previous=>exact (base_pure _).symm
    | Ok published=>
      unfold AdapterPublicServerPublication.afterPublication AdapterPublicServerBuildBody.checked
      simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
      cases began:peer.begin_peer_insert self.control published with
      | fail error | div=>exact (base_pure _).symm
      | ok result=>cases result with
        | Err previous=>simp only [RustT.run_pure]; exact (base_pure _).symm
        | Ok pending=>
          have same:=congrArg RustT.run (install (n:=n) (KemSK:=KemSK) (source:=source) original self pending)
          exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall.install

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall.after_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstall.after_publication
