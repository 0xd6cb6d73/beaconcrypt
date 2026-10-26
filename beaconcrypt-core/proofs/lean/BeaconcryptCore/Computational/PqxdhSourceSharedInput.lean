import BeaconcryptCore.Computational.PqxdhSourceSharedPreparation
import BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource

/-!
The concrete root-free source input is produced by the complete executed preparation. Its executable form keeps a cache placeholder; evaluation restores exactly the shared cache reached by the original source. This representation does not sample or install a cache and retains original common outcomes, private interpreter state, owner selection and complete source continuation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSourceSharedInput
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK

def restore (context : Bool ⊕ Input) (cache : CtxRO.QueryCache) : Bool ⊕ Input :=
  match context with
  | .inl decision => .inl decision
  | .inr input => .inr { input with shared := (input.shared.1, cache) }

noncomputable def input (packet : Packet) : Bool ⊕ Input :=
  PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post
    (PqxdhSourceSharedPreparation.restore setup env callbacks program post attachedVerify primitives kem packet ∅ ∅)
    selected number ancestors disclosed

/-- The interpreter restores the actual reached cache while every other source input field stays unchanged. -/
theorem input_cache (packet : Packet) (cache : CtxRO.QueryCache) :
    restore setup (input setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed packet) cache =
      PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post
        (PqxdhSourceSharedPreparation.restore setup env callbacks program post attachedVerify primitives kem packet cache ∅)
        selected number ancestors disclosed := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state <;> rfl

noncomputable def run : OracleComp HashSpec (Bool ⊕ Input) :=
  input setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed <$>
    PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem

/-- The actual root-free prior is supplied by executing the full source prefix from the ordinary empty ROM. -/
theorem source :
    (fun result => restore setup result.1 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed)).run ∅ =
    PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed := by
  have original := congrArg (fun work =>
    (fun context => PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      selected number ancestors disclosed) <$> work)
    (PqxdhSourceSharedPreparation.prepare_empty setup env callbacks program post attachedVerify primitives baseImpl kem)
  simpa only [run, simulateQ_map, StateT.run_map, Functor.map_map, input_cache,
    PqxdhInitialPreparedSourceInput.prior] using original

end BeaconcryptCore.Computational.PqxdhSourceSharedInput


/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedInput.input_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedInput.input_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedInput.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedInput.source
