import BeaconcryptCore.Computational.PqxdhSourceSharedInput
import BeaconcryptCore.Computational.PqxdhSharedParentInput

/-!
The concrete root-free source input is produced by the complete executed preparation. Its executable form keeps a cache placeholder; evaluation restores exactly the shared cache reached by the original source. This representation does not sample or install a cache and retains original common outcomes, private interpreter state, owner selection and complete source continuation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSharedParent
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

local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "input" => PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed

noncomputable def after (packet : Packet) (output : HmacBlock) (depth : Nat) : OracleComp HashSpec LocalPacket :=
  match input packet with
  | .inl decision => pure (.inl decision)
  | .inr start => PqxdhSharedParentInput.run env0 callbacks baseImpl kem attachedVerify primitives
      packet.secretKey packet.ciphertext start output depth

noncomputable def run (depth : Nat) : OracleComp HashSpec LocalPacket := do
  let packet ← PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
  let output ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ HmacBlock)
  after setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed packet output depth

/-- The actual preparation has already installed the exact local callbacks used by the shared-ROM continuation. -/
theorem input_normalized (packet : Packet) :
    Sum.map id (PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives
      packet.secretKey packet.ciphertext) (input packet) = input packet := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The literal completed, cached and first-miss alternatives continue through the actual reached shared cache. -/
theorem after_source (packet : Packet) (output : HmacBlock) (depth : Nat) (cache : CtxRO.QueryCache) :
    (fun result => PqxdhSharedParentInput.restore result.1 result.2) <$>
      (simulateQ hashImpl (after setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed packet output depth)).run cache =
    (do
      match PqxdhSourceSharedInput.restore setup (input packet) cache with
      | .inl decision => pure (.inl decision)
      | .inr start =>
        let pending ← PqxdhErasedParentSample.sampleOne env.source env.recordWriter env.senderId env.route env.decode depth (start, output)
        pure (PqxdhErasedParentSample.normalize (.inr ((start, output), pending)))) := by
  have normalized := input_normalized setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed packet
  cases inputEq : input packet with
  | inl decision => simp only [after, inputEq, simulateQ_pure, StateT.run_pure, map_pure,
      PqxdhSharedParentInput.restore, PqxdhSourceSharedInput.restore]
  | inr start =>
    simp only [inputEq, Sum.map_inr, Sum.inr.injEq] at normalized
    have changed : PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives
        packet.secretKey packet.ciphertext { start with shared := (start.shared.1, cache) } =
        { start with shared := (start.shared.1, cache) } :=
      congrArg (fun value => { value with shared := (start.shared.1, cache) }) normalized
    have actual := PqxdhSharedParentInput.source env0 callbacks baseImpl kem attachedVerify primitives
      packet.secretKey packet.ciphertext start output depth cache
    rw [changed] at actual
    simpa only [after, inputEq, PqxdhSourceSharedInput.restore, bind_pure_comp,
      PqxdhPreparedSharedPrefix.environment, PqxdhSourceSharedPreparation.environment] using actual

set_option backward.isDefEq.respectTransparency false in
/-- The complete later-parent preparation executes every earlier source hash through the ordinary empty ROM and retains all original common/cached outcomes. -/
theorem source (depth : Nat) :
    (fun result => PqxdhSharedParentInput.restore result.1 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run ∅ =
    PqxdhErasedParentSample.normalize <$>
      PqxdhErasedParentSample.sample env.source env.recordWriter env.senderId env.route env.decode depth
        (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) := by
  simp only [run, simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete,
    bind_map_left, PqxdhErasedParentSample.sample, PqxdhInitialPreparedSourceInput.prior]
  rw [← PqxdhSourceSharedPreparation.prepare_empty setup env callbacks program post attachedVerify primitives baseImpl kem]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  apply bind_congr
  intro output
  rw [after_source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed,
    PqxdhSourceSharedInput.input_cache setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed]
  cases PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post
    (PqxdhSourceSharedPreparation.restore setup env callbacks program post attachedVerify primitives kem result.1 result.2 ∅)
    selected number ancestors disclosed <;> simp only [map_bind, map_pure, PqxdhErasedParentSample.normalize]

end BeaconcryptCore.Computational.PqxdhLaterSharedParent


/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedParent.input_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedParent.input_normalized

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedParent.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedParent.after_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedParent.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedParent.source
