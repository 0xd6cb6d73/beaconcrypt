-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRealization
import BeaconcryptCore.Computational.RegistrationNativeScalarSource

/-! The seed-free identity constructor's preparation is an actual public query program with no owner or environment mutation. Its primitive source realization is proved separately; this factor retains every optional ML/pin/identity failure and actual callback order. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare
open RegistrationNativeIdentityFrontend (Ambient Trusted Prepared)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK Auxiliary Value : Type}

def coins : QueryImpl unifSpec (OracleComp (Trusted n KemSK)) :=
  fun query => (Trusted n KemSK).query (.inl (.inl (.inl query)))

def hash (request : registration.HashRequest) : OracleComp (Trusted n KemSK) CtxRomAuth.CtxDigest :=
  (Trusted n KemSK).query (.inl (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))))

def lift {source : RegistrationNativeMldsa.Source} (work : OracleComp (Trusted n KemSK) Value) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value := StateT.lift (StateT.lift work)

noncomputable def program (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    OracleComp (Trusted n KemSK) (RustM (Option (Prepared source))) := do
  match ← simulateQ coins (RegistrationNativeMldsa.generate source) with
  | none => pure (.ok none)
  | some credentials => match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok pending => match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok request => do
          let digest ← hash request
          match pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok .None => pure (.ok none)
          | .ok (.Some pin) =>
              let identity ← RegistrationNativeIdentityInterface.create (Ambient n KemSK)
              match identity with
              | none => pure (.ok none)
              | some identity => do
                  let prekey ← simulateQ coins PqxdhJointGapDh.sampleScalar
                  pure (.ok (some ⟨credentials, pin, identity, prekey⟩))

private theorem lift_bind {source : RegistrationNativeMldsa.Source} {Result : Type}
    (work : OracleComp (Trusted n KemSK) Value) (next : Value → OracleComp (Trusted n KemSK) Result) :
    lift (Auxiliary := Auxiliary) (source := source) (work >>= next) = (lift work >>= fun value => lift (next value)) := by
  funext owners env
  simp only [lift, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure, bind_assoc, pure_bind]

private theorem lift_pure {source : RegistrationNativeMldsa.Source} (value : Value) :
    lift (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (pure value) = pure value := by
  funext owners env
  simp only [lift, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure, pure_bind]

private theorem sample_lift {source : RegistrationNativeMldsa.Source} (work : ProbComp Value) :
    RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work =
      lift (simulateQ coins work) := by
  unfold RegistrationNativeIdentityFrontend.sample
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lift_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [lift_bind]
      apply congrArg (fun continuation => (RegistrationNativeIdentityFrontend.effect (n := n) (KemSK := KemSK)
        (Auxiliary := Auxiliary) (source := source) (.inl query) >>= continuation))
      funext reply
      exact ih reply

/-- The actual public handle constructor preparation executes the literal complete query AST before any owner allocation. -/
theorem prepare_program (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeIdentityFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId =
      lift (program source edPin mlPin keyId) := by
  simp only [RegistrationNativeIdentityFrontend.prepare, program, lift_bind, sample_lift]
  apply congrArg (fun continuation => (lift (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
    (simulateQ coins (RegistrationNativeMldsa.generate source)) >>= continuation))
  funext generated
  cases generated with
  | none => exact (lift_pure _).symm
  | some credentials =>
      cases initial : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error => exact (lift_pure _).symm
      | div => exact (lift_pure _).symm
      | ok pending =>
          cases requested : pending.request with
          | fail error => simp only [requested, lift_pure]
          | div => simp only [requested, lift_pure]
          | ok request =>
              simp only [requested, lift_bind]
              apply congrArg (fun continuation => (lift (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
                (hash request) >>= continuation))
              funext digest
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error => exact (lift_pure _).symm
              | div => exact (lift_pure _).symm
              | ok reply => cases reply with
                | none => exact (lift_pure _).symm
                | some pin =>
                    simp only [lift_bind]
                    apply congrArg (fun continuation =>
                      (lift (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
                        (RegistrationNativeIdentityInterface.create (Ambient n KemSK)) >>= continuation))
                    funext identity
                    cases identity with
                    | none => exact (lift_pure _).symm
                    | some identity => simp only [lift_bind, lift_pure]

/-- Preparation keeps the current public owner list and mutable environment while executing every actual query. -/
theorem prepare_run (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeIdentityFrontend.State source) (env : EnvState Auxiliary) :
    ((RegistrationNativeIdentityFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env =
      (fun reply => ((reply, owners), env)) <$> program source edPin mlPin keyId := by
  rw [prepare_program]
  simp only [lift, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare.prepare_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare.prepare_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare.prepare_run
