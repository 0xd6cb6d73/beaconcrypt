-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashShared

/-! Literal caller-known record services in the combined digest experiment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhRecordFactsDigestCache (cacheOf)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The entire source send, including HKDF, AEAD, commitment hashing and the literal optional writer. -/
noncomputable def send (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (state : CtxPrivate n) :
    OracleComp (Spec n) ((ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × CtxPrivate n) :=
  PqxdhRecordFactsHashShared.nativeProgram setup codec
    (simulateQ RawCtxMixedOwner.sendAdapter
      (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))) state

/-- Actual caller-known sealing is exactly simulated with full source state, counters, writer log and coherent combined cache. -/
theorem send_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (state : CtxPrivate n) :
    (simulateQ PqxdhRecordFactsCollisionOracle.plain (send setup codec kernel context state)).run (cacheOf state) =
      (fun result => (result, cacheOf result.2)) <$>
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.knownSend kernel context)).run state := by
  simpa only [send, PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose] using
    PqxdhRecordFactsHashShared.nativeProgram_exact setup codec
      (simulateQ RawCtxMixedOwner.sendAdapter
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))) state

/-- The entire source receive retains its parser, key selection, commitment comparison and optional AEAD plaintext. -/
noncomputable def receive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : CtxPrivate n) :
    OracleComp (Spec n)
      ((ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n) :=
  PqxdhRecordFactsHashShared.nativeProgram setup codec
    (simulateQ RawCtxMixedOwner.receiveAdapter
      (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))) state

/-- Actual caller-known receiving is exactly simulated, including failure, cached/future keys and the actual optional plaintext. -/
theorem receive_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : CtxPrivate n) :
    (simulateQ PqxdhRecordFactsCollisionOracle.plain (receive setup codec kernel target context state)).run (cacheOf state) =
      (fun result => (result, cacheOf result.2)) <$>
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.knownReceive kernel target context)).run state := by
  simpa only [receive, PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose] using
    PqxdhRecordFactsHashShared.nativeProgram_exact setup codec
      (simulateQ RawCtxMixedOwner.receiveAdapter
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))) state

end BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown.send_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown.send_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown.receive_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown.receive_exact
