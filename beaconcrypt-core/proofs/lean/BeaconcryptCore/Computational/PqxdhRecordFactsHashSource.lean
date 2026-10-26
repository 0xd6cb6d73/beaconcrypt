-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashBase
import BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown
import BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal

/-! A complete source compiler into one coherent private/ordinary digest experiment. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashSource
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (AmbientExact)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every source constructor is compiled concretely, including original ambient effects and caller-known records. -/
noncomputable def compiler (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n)))
  | .allocate slot => PqxdhRecordFactsHashBase.allocate slot
  | .coin coin => PqxdhRecordFactsHashBase.coin coin
  | .hash bytes => PqxdhRecordFactsHashShared.compile (.inr ((), bytes))
  | .charge kind => PqxdhRecordFactsHashBase.charge kind
  | .lookup coordinate => PqxdhRecordFactsHashLocal.lookup coordinate
  | .opening pending => PqxdhRecordFactsHashLocal.opening codec.frameRead pending
  | .sealing pending => PqxdhRecordFactsPrivateCacheSourceDraw.compileHiddenSeal
      modes setup.source.crypto codec.frameWrite replace pending
  | .knownSend kernel context => PqxdhRecordFactsHashKnown.send setup codec kernel context
  | .knownReceive kernel target context => PqxdhRecordFactsHashKnown.receive setup codec kernel target context
  | .publish tag => PqxdhRecordFactsHashBase.publish tag

/-- The complementary ordinary/base interface is discharged by the actual source branch equations. -/
theorem ambient_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    AmbientExact (compiler modes replace setup codec) modes replace setup codec := by
  intro query nonseal state
  cases query with
  | allocate slot => exact PqxdhRecordFactsHashBase.allocate_exact modes replace setup codec slot state
  | coin coin => exact PqxdhRecordFactsHashBase.coin_exact modes replace setup codec coin state
  | hash bytes => exact PqxdhRecordFactsHashBase.hash_exact modes replace setup codec bytes state
  | charge kind => exact PqxdhRecordFactsHashBase.charge_exact modes replace setup codec kind state
  | lookup coordinate => exact PqxdhRecordFactsHashLocal.lookup_exact modes replace setup codec coordinate state
  | opening pending => exact PqxdhRecordFactsHashLocal.opening_exact modes replace setup codec pending state
  | sealing pending => exact False.elim nonseal
  | knownSend kernel context => exact PqxdhRecordFactsHashKnown.send_exact modes replace setup codec kernel context state
  | knownReceive kernel target context => exact PqxdhRecordFactsHashKnown.receive_exact modes replace setup codec kernel target context state
  | publish tag => exact PqxdhRecordFactsHashBase.publish_exact modes replace setup codec tag state

/-- The generic complementary interface installs exactly this complete concrete compiler. -/
theorem compiled_self (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    PqxdhRecordFactsPrivateCacheSourceDrawMemo.compiled (compiler modes replace setup codec)
      modes setup.source.crypto codec.frameWrite replace = compiler modes replace setup codec := by
  funext query
  cases query <;> rfl

open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (plain packed)

/-- The whole adaptive source execution compiles into one memoized private/ordinary digest experiment. All complementary source equations are discharged. -/
theorem source_exact {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (supported : ∀ label, modes label ≠ .real)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    (simulateQ plain ((simulateQ (compiler modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅ =
      packed <$> PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary := by
  simpa only [compiled_self] using
    PqxdhRecordFactsPrivateCacheSourceDrawMemo.source_compile (fun _ => $ᵗ CtxRomAuth.CtxDigest)
      (compiler modes replace setup codec) modes replace setup codec
      (ambient_exact modes replace setup codec) supported route env serverKid bounds mode adversary

/-- The actual adversarial view agrees with the complete compiled experiment after forgetting only its explicit digest-cache instrumentation. -/
theorem source_view {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (supported : ∀ label, modes label ≠ .real)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    LazyOracleDiscard.LawEq
      (PqxdhRecordLiftIdeal.ctxView <$> PqxdhRecordLiftIdeal.ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      ((PqxdhRecordLiftIdeal.ctxView ∘ Prod.fst) <$>
        (simulateQ plain ((simulateQ (compiler modes replace setup codec)
          (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
            (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅) := by
  rw [source_exact modes replace setup codec supported, Functor.map_map]
  exact PqxdhRecordFactsPrivateCacheWorld.view_observation modes replace setup codec route env serverKid bounds mode adversary supported

end BeaconcryptCore.Computational.PqxdhRecordFactsHashSource

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.ambient_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.ambient_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.compiled_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.compiled_self
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.source_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.source_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashSource.source_view
