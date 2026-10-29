-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyPort

/-! Each native create transports its ML pin immediately before the unchanged old create. All native HMAC messages use a disjoint tag. Coins, records and the original test/fresh commands retain their exact query/reply types and observations. Observation-mode naturality is proved for the entire adaptive client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyCompile
open RegistrationNativeEntropyInterface (metadata userHmac)
open PqxdhSecretInputKdf (zeroSalt)
variable {Value : Type}

def modeO : QueryImpl RegistrationNativeInterface.FullSpec (OracleComp PqxdhDeploymentInterface.FullSpec)
  | .inl (.inl coin) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inl coin))
  | .inl (.inr (.create edPin mlPin keyId)) => do
      let _ ← PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.hmac zeroSalt (metadata mlPin))))
      PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.create edPin keyId)))
  | .inl (.inr (.bundle owner)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.bundle owner)))
  | .inl (.inr (.accept raw)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.accept raw)))
  | .inl (.inr (.build session payload)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.build session payload)))
  | .inl (.inr (.finish owner raw)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.finish owner raw)))
  | .inl (.inr (.hmac key message)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.hmac key (userHmac message))))
  | .inl (.inr (.hash bytes)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.hash bytes)))
  | .inl (.inr (.serverSend keyId plaintext)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.serverSend keyId plaintext)))
  | .inl (.inr (.serverRaw raw)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.serverRaw raw)))
  | .inl (.inr (.beaconSend owner plaintext)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.beaconSend owner plaintext)))
  | .inl (.inr (.beaconRaw owner raw)) => PqxdhDeploymentInterface.FullSpec.query (.inl (.inr (.beaconRaw owner raw)))
  | .inr secrecy => PqxdhDeploymentInterface.FullSpec.query (.inr secrecy)

def modeP : QueryImpl RegistrationNativeInterface.FullSuccessSpec (OracleComp PqxdhDeploymentInterface.FullSuccessSpec)
  | .inl (.inl coin) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inl coin))
  | .inl (.inr (.create edPin mlPin keyId)) => do
      let _ ← PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.hmac zeroSalt (metadata mlPin))))
      PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.create edPin keyId)))
  | .inl (.inr (.bundle owner)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.bundle owner)))
  | .inl (.inr (.accept raw)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.accept raw)))
  | .inl (.inr (.build session payload)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.build session payload)))
  | .inl (.inr (.finish owner raw)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.finish owner raw)))
  | .inl (.inr (.hmac key message)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.hmac key (userHmac message))))
  | .inl (.inr (.hash bytes)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.hash bytes)))
  | .inl (.inr (.serverSend keyId plaintext)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.serverSend keyId plaintext)))
  | .inl (.inr (.serverRaw raw)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.serverRaw raw)))
  | .inl (.inr (.beaconSend owner plaintext)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.beaconSend owner plaintext)))
  | .inl (.inr (.beaconRaw owner raw)) => PqxdhDeploymentInterface.FullSuccessSpec.query (.inl (.inr (.beaconRaw owner raw)))
  | .inr secrecy => PqxdhDeploymentInterface.FullSuccessSpec.query (.inr secrecy)

def compiler : (mode : PqxdhDeploymentInterface.Mode) →
    QueryImpl (RegistrationNativeInterface.ModeSpec mode) (OracleComp (PqxdhDeploymentInterface.ModeSpec mode))
  | .O => modeO
  | .P => modeP

def compile (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :=
  simulateQ (compiler mode) work

/-- The transport preserves raw receive observation mode query by query, including both creation transport operations. -/
theorem observation_query (query : RegistrationNativeInterface.FullSuccessSpec.Domain) :
    (modeO ∘ₛ RegistrationNativeInterface.observeFull) query =
      (PqxdhDeploymentInterface.observeFull ∘ₛ modeP) query := by
  rcases query with (coin | command) | secrecy
  · rfl
  · cases command <;> simp only [QueryImpl.compose, RegistrationNativeInterface.observeFull,
      PqxdhDeploymentInterface.observeFull, modeO, modeP, simulateQ_bind, simulateQ_spec_query,
      simulateQ_map, RegistrationNativeInterface.eraseCommand,
      PqxdhDeploymentInterface.project, bind_pure, bind_pure_comp]
    all_goals rfl
  · rfl

/-- Full adaptive compilation commutes with the actual Mode P wrapper; hidden raw plaintexts are never exposed to the native adversary. -/
theorem observation_program (work : OracleComp RegistrationNativeInterface.FullSuccessSpec Value) :
    simulateQ modeO (RegistrationNativeInterface.asModeO .P work) =
      PqxdhDeploymentInterface.asModeO .P (compile .P work) := by
  simp only [RegistrationNativeInterface.asModeO, PqxdhDeploymentInterface.asModeO,
    compile, compiler, ← QueryImpl.simulateQ_compose]
  exact congrArg (fun implementation => simulateQ implementation work) (funext observation_query)

/-- The original secrecy command is forwarded literally, without moving or replacing its private sampler. -/
theorem secrecy_forwardO (secrecy : PqxdhDeploymentInterface.Secrecy) :
    modeO (.inr secrecy) = (PqxdhDeploymentInterface.FullSpec.query (.inr secrecy) :
      OracleComp PqxdhDeploymentInterface.FullSpec _) := rfl

/-- Mode P likewise forwards the literal original secrecy command and ciphertext reply. -/
theorem secrecy_forwardP (secrecy : PqxdhDeploymentInterface.Secrecy) :
    modeP (.inr secrecy) = (PqxdhDeploymentInterface.FullSuccessSpec.query (.inr secrecy) :
      OracleComp PqxdhDeploymentInterface.FullSuccessSpec _) := rfl

end BeaconcryptCore.Computational.RegistrationNativeEntropyCompile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.observation_query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.observation_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.observation_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.observation_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.secrecy_forwardO' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.secrecy_forwardO
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.secrecy_forwardP' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyCompile.secrecy_forwardP
