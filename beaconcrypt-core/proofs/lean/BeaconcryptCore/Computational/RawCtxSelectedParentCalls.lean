import BeaconcryptCore.Computational.RawCtxSelectedParentSource
import BeaconcryptCore.Computational.RawCtxChainOwner

/-!
The exact retained-parent receive and send interpreters instantiate whole-owner calls. Native admission, remaining skips/opening, exhausted sends and advanced optional sealing all keep the same complete primitive state. The mapping changes only private chain representation. Retained lookup applies only to private KDF calls; a consuming public frontend uses the same real fixed-source evaluation on both sides. These operational equations do not supply freshness or replace source outputs with uniform values.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentCalls
open RawCtxSelectedChain RawCtxChainInterpretation RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Kernel (Chain : Type) := RefinedRatchet Chain Chain RatchetMaterial

def nativeKernel (target : RootOutput) : Kernel Slot → Kernel RatchetChain :=
  mapChains (interpret (RawCtxFreshChainCut.concreteChain target)) (interpret (RawCtxFreshChainCut.concreteChain target))

noncomputable def childResponse (prior : Prior) (entry : Entry) (target : RootOutput) : RatchetKdfResponse :=
  RawCtxSelectedParentSource.response prior entry target
    (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))

noncomputable def nativeCalls {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    RawCtxChainOwner.Calls (Kernel RatchetChain) (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  { receive := fun kernel sequence context =>
      simulateQ (RawCtxSelectedParentSource.nativeReceive source writer prior entry target)
        (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalBegin kernel sequence context))
    send := fun kernel context =>
      simulateQ (RawCtxSelectedParentSource.nativeSend source writer prior entry target)
        (RawCtxInterpretedSend.program (RawCtxInterpretedSend.normalBegin kernel context)) }

noncomputable def labelCalls {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) :
    RawCtxChainOwner.Calls (Kernel Slot) (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  { receive := fun kernel sequence context =>
      simulateQ (RawCtxSelectedParentSource.labelReceive source writer prior entry response)
        (RawCtxChainReceive.execute kernel sequence context)
    send := fun kernel context =>
      simulateQ (RawCtxSelectedParentSource.labelSend source writer prior entry response)
        (RawCtxChainSend.execute kernel context) }

/-- Original native receive admission and every later optional source effect retain the exact interpreted whole kernel and primitive poststate. -/
theorem receive_map {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (kernel : Kernel Slot)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (nativeCalls (Auxiliary := Auxiliary) source writer prior entry target).receive (nativeKernel target kernel) sequence context =
      Prod.map (nativeKernel target) id <$>
        (labelCalls source writer prior entry (childResponse prior entry target)).receive kernel sequence context := by
  simp only [nativeCalls, labelCalls, nativeKernel, RawCtxChainReceive.execute,
    RawCtxChainReceive.normalBegin_native]
  exact RawCtxSelectedParentSource.receive_program source writer prior entry target _

/-- Original send exhaustion, KDF resumption and advanced optional sealing retain the same complete native kernel and primitive state. -/
theorem send_map {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (kernel : Kernel Slot)
    (context : RawCtxSourceSend.SealContext) :
    (nativeCalls (Auxiliary := Auxiliary) source writer prior entry target).send (nativeKernel target kernel) context =
      Prod.map (nativeKernel target) id <$>
        (labelCalls source writer prior entry (childResponse prior entry target)).send kernel context := by
  simp only [nativeCalls, labelCalls, nativeKernel, RawCtxChainSend.execute,
    RawCtxChainSend.normalBegin_native]
  exact RawCtxSelectedParentSource.send_program source writer prior entry target _

end BeaconcryptCore.Computational.RawCtxSelectedParentCalls

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCalls.receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCalls.receive_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCalls.send_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCalls.send_map
