-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInterface
import BeaconcryptCore.Refinement.TranscriptAuthParts
/-! The source public-adapter interface carries original Rust slices. Its analysis embedding preserves every byte and command operand in the unchanged native interface. The experiment's independent hash/coin services remain separate from adapter methods. Query classes, observation modes and all deployment budget coordinates are preserved. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface

inductive Command where
  | create (edPin mlPin : Slice U8) (keyId : U64)
  | bundle (owner : Nat)
  | accept (raw : Slice U8)
  | build (session : Nat) (payload : Option (Slice U8))
  | finish (owner : Nat) (raw : Slice U8)
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | serverSend (keyId : U64) (plaintext : Slice U8)
  | serverRaw (raw : Slice U8)
  | beaconSend (owner : Nat) (plaintext : Slice U8)
  | beaconRaw (owner : Nat) (raw : Slice U8)

def nativeCommand : Command → RegistrationNativeInterface.Command
  | .create edPin mlPin keyId=>.create (TranscriptAuthParts.absSlice edPin) (TranscriptAuthParts.absSlice mlPin) keyId
  | .bundle owner=>.bundle owner
  | .accept raw=>.accept (TranscriptAuthParts.absSlice raw)
  | .build session payload=>.build session (payload.map TranscriptAuthParts.absSlice)
  | .finish owner raw=>.finish owner (TranscriptAuthParts.absSlice raw)
  | .hmac key message=>.hmac key message
  | .hash bytes=>.hash bytes
  | .serverSend keyId plaintext=>.serverSend keyId (TranscriptAuthParts.absSlice plaintext)
  | .serverRaw raw=>.serverRaw (TranscriptAuthParts.absSlice raw)
  | .beaconSend owner plaintext=>.beaconSend owner (TranscriptAuthParts.absSlice plaintext)
  | .beaconRaw owner raw=>.beaconRaw owner (TranscriptAuthParts.absSlice raw)

abbrev CommandSpec : OracleSpec Command :=fun command=>RegistrationNativeInterface.CommandSpec (nativeCommand command)
abbrev Spec :=unifSpec+CommandSpec

def nativeCore : Spec.Domain → RegistrationNativeInterface.Spec.Domain
  | .inl coin=>.inl coin
  | .inr command=>.inr (nativeCommand command)

inductive Secrecy where
  | test (handle : PqxdhDeploymentInterface.Handle) (left right : Slice U8)
  | fresh (handle : PqxdhDeploymentInterface.Handle) (length : Nat)

def nativeSecrecy : Secrecy → PqxdhDeploymentInterface.Secrecy
  | .test handle left right=>.test handle (TranscriptAuthParts.absSlice left) (TranscriptAuthParts.absSlice right)
  | .fresh handle length=>.fresh handle length

abbrev SecrecySpec : OracleSpec Secrecy :=fun query=>PqxdhDeploymentInterface.SecrecySpec (nativeSecrecy query)
abbrev FullSpec :=Spec+SecrecySpec

def nativeQuery : FullSpec.Domain → RegistrationNativeInterface.Query
  | .inl core=>.inl (nativeCore core)
  | .inr secrecy=>.inr (nativeSecrecy secrecy)

abbrev ModeSpec (mode : PqxdhDeploymentInterface.Mode) : OracleSpec FullSpec.Domain :=
  fun query=>(RegistrationNativeInterface.ModeSpec mode).Range (nativeQuery query)

variable {Value : Type}

def adapter : QueryImpl Spec (OracleComp RegistrationNativeInterface.Spec) :=
  fun query=>by
    cases query with
    | inl coin=>exact (RegistrationNativeInterface.Spec.query (.inl coin) :OracleComp RegistrationNativeInterface.Spec _)
    | inr command=>exact (RegistrationNativeInterface.Spec.query (.inr (nativeCommand command)) :OracleComp RegistrationNativeInterface.Spec _)

def modeAdapter (mode : PqxdhDeploymentInterface.Mode) :
    QueryImpl (ModeSpec mode) (OracleComp (RegistrationNativeInterface.ModeSpec mode)) :=
  fun query=>((RegistrationNativeInterface.ModeSpec mode).query (nativeQuery query) :
    OracleComp (RegistrationNativeInterface.ModeSpec mode) _)

def compile (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (ModeSpec mode) Value) :
    OracleComp (RegistrationNativeInterface.ModeSpec mode) Value :=
  simulateQ (modeAdapter mode) work

def Respects (mode : PqxdhDeploymentInterface.Mode) (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (ModeSpec mode) Value) : Prop :=
  ∀kind,work.IsQueryBoundP (fun query=>RegistrationNativeInterface.queryClass (nativeQuery query)=kind) (budget.cap kind)

theorem compile_bound (mode : PqxdhDeploymentInterface.Mode) (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (ModeSpec mode) Value) (bounded : Respects mode budget work) :
    RegistrationNativeInterface.Respects budget (compile mode work) := by
  intro kind
  unfold compile
  apply RawCtxSourceOpen.simulate_bound (modeAdapter mode)
    (fun query=>RegistrationNativeInterface.queryClass (nativeQuery query)=kind)
    (fun query=>RegistrationNativeInterface.queryClass query=kind) work (budget.cap kind) (bounded kind)
  intro query
  change IsQueryBoundP (((RegistrationNativeInterface.ModeSpec mode).query (nativeQuery query)) :
    OracleComp (RegistrationNativeInterface.ModeSpec mode) _) _ _
  rw [isQueryBoundP_query_iff]
  intro counted
  simp only [counted,ite_true]
  decide

theorem raw_bytes (raw : Slice U8) : nativeCommand (.accept raw)=.accept (TranscriptAuthParts.absSlice raw) :=rfl

theorem native_profile {m : Type → Type} [Monad m] [LawfulMonad m]
    (mode : PqxdhDeploymentInterface.Mode) (implementation : QueryImpl (RegistrationNativeInterface.ModeSpec mode) m)
    (work : OracleComp (ModeSpec mode) Value) :
    simulateQ implementation (compile mode work)=
      simulateQ (show QueryImpl (ModeSpec mode) m from fun query=>implementation (nativeQuery query)) work := by
  unfold compile
  rw [←QueryImpl.simulateQ_compose]
  apply congrArg (fun handler=>simulateQ handler work)
  funext query
  simp only [QueryImpl.apply_compose,modeAdapter,simulateQ_spec_query]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface.compile_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface.raw_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface.raw_bytes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface.native_profile' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface.native_profile
