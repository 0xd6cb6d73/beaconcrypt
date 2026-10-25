// SPDX-License-Identifier: 0BSD

//! Role-selected key agreement after the exact registration authentication gates.
//!
//! Primitive execution and the association of secret roles with native handles remain
//! interpreter obligations. Each owned phase fixes the operands of its next operation.

#![allow(clippy::large_enum_variant, clippy::question_mark)]

use crate::pqxdh::{
	self, BeaconAborted, BeaconInitSent, BeaconRegistrationCandidate, PendingServerRegistration,
	PqxdhSharedSecrets, RegistrationId, RegistrationStatus, ServerCoins, ServerState,
	VerifiedInitKex,
};
use crate::ratchet::RatchetChain;
use crate::registration::{AuthenticatedInit, AuthenticatedResponse};
use crate::session::RegistrationBinding;

/// The fixed fields of the same response whose complete transcript was verified.
pub struct ResponsePublic {
	pub identity_key: [u8; 32],
	pub ephemeral_key: [u8; 32],
	pub kem_cipher_text: [u8; 1088],
	pub key_id: u64,
}

/// A private key selected from the current registration interpreter's handles.
pub enum DhSecretRole {
	LocalIdentity,
	ServerEphemeral,
	BeaconPrekey,
	BeaconOneTime,
}

/// Native key generation returns a public key and retains its secret under this role.
pub enum EphemeralRole {
	ServerEphemeral,
}

/// Every operation can reject without creating a registration candidate.
#[must_use]
pub enum AgreementEffect<'a> {
	Rejected(Option<BeaconAborted>),
	ConvertPublic(PublicConversionPending<'a>),
	ConvertSecret(SecretConversionPending<'a>),
	GenerateEphemeral(EphemeralPending<'a>),
	Encapsulate(EncapsulationPending<'a>),
	Decapsulate(DecapsulationPending<'a>),
	Dh(DhPending<'a>),
	RootKdf(RootKdfPending<'a>),
	ServerComplete(ServerAgreement),
	BeaconComplete(BeaconAgreement<'a>),
}

enum AgreementInput<'a> {
	Server {
		control: ServerState,
		status: RegistrationStatus,
		registration: VerifiedInitKex,
		binding: RegistrationBinding,
	},
	Beacon {
		control: BeaconInitSent,
		binding: RegistrationBinding,
		response: ResponsePublic,
		application_ciphertext: &'a [u8],
	},
}

struct AgreementState<'a> {
	input: AgreementInput<'a>,
	remote_identity: [u8; 32],
	ephemeral_public_key: [u8; 32],
	kem_ciphertext: [u8; 1088],
	dh1: RatchetChain,
	dh2: RatchetChain,
	dh3: RatchetChain,
	dh4: RatchetChain,
	kem: RatchetChain,
}

impl<'a> AgreementState<'a> {
	fn reject(self) -> AgreementEffect<'a> {
		match self.input {
			AgreementInput::Server { .. } => AgreementEffect::Rejected(None),
			AgreementInput::Beacon { control, .. } => {
				AgreementEffect::Rejected(Some(pqxdh::beacon_abort_init(control)))
			}
		}
	}

	fn new(input: AgreementInput<'a>) -> Self {
		Self {
			input,
			remote_identity: [0; 32],
			ephemeral_public_key: [0; 32],
			kem_ciphertext: [0; 1088],
			dh1: RatchetChain::from_bytes([0; 32]),
			dh2: RatchetChain::from_bytes([0; 32]),
			dh3: RatchetChain::from_bytes([0; 32]),
			dh4: RatchetChain::from_bytes([0; 32]),
			kem: RatchetChain::from_bytes([0; 32]),
		}
	}
}

/// Begin only from the core-owned authenticated request; field pairing is internal.
pub fn begin_server_agreement(
	control: ServerState,
	status: RegistrationStatus,
	authenticated: AuthenticatedInit,
) -> AgreementEffect<'static> {
	if pqxdh::validate_registration_status(status).is_err() {
		return AgreementEffect::Rejected(None);
	}
	let (registration, binding) = authenticated.into_parts();
	AgreementEffect::GenerateEphemeral(EphemeralPending {
		state: AgreementState::new(AgreementInput::Server {
			control,
			status,
			registration,
			binding,
		}),
	})
}

/// The application ciphertext stays borrowed from the authenticated response.
pub fn begin_beacon_agreement<'a>(authenticated: AuthenticatedResponse<'a>) -> AgreementEffect<'a> {
	let (control, binding, response, application_ciphertext) = authenticated.into_parts();
	let expected = control.expected_server_binding();
	let pinned = binding.server_pin().binding();
	if expected.identity_key_id != pinned.identity_key_id
		|| expected.identity_public_key != pinned.identity_public_key
	{
		return AgreementEffect::Rejected(Some(pqxdh::beacon_abort_init(control)));
	}
	AgreementEffect::ConvertPublic(PublicConversionPending {
		state: AgreementState::new(AgreementInput::Beacon {
			control,
			binding,
			response,
			application_ciphertext,
		}),
	})
}

pub struct PublicConversionPending<'a> {
	state: AgreementState<'a>,
}

impl<'a> PublicConversionPending<'a> {
	pub fn public_key(&self) -> &[u8; 32] {
		match &self.state.input {
			AgreementInput::Server { registration, .. } => {
				registration.beacon_identity_public_key()
			}
			AgreementInput::Beacon { response, .. } => &response.identity_key,
		}
	}

	pub fn resume(mut self, converted: Option<[u8; 32]>) -> AgreementEffect<'a> {
		let Some(converted) = converted else {
			return self.state.reject();
		};
		self.state.remote_identity = converted;
		AgreementEffect::ConvertSecret(SecretConversionPending { state: self.state })
	}
}

/// Convert the current owner's Ed25519 secret to its local X25519 identity handle.
pub struct SecretConversionPending<'a> {
	state: AgreementState<'a>,
}

impl<'a> SecretConversionPending<'a> {
	pub const fn secret_role(&self) -> DhSecretRole {
		DhSecretRole::LocalIdentity
	}

	pub fn resume(self, converted: bool) -> AgreementEffect<'a> {
		if !converted {
			return self.state.reject();
		}
		match &self.state.input {
			AgreementInput::Server { .. } => AgreementEffect::Dh(DhPending {
				state: self.state,
				position: DhPosition::First,
			}),
			AgreementInput::Beacon { .. } => {
				AgreementEffect::Decapsulate(DecapsulationPending { state: self.state })
			}
		}
	}
}

pub struct EphemeralPending<'a> {
	state: AgreementState<'a>,
}

impl<'a> EphemeralPending<'a> {
	pub const fn role(&self) -> EphemeralRole {
		EphemeralRole::ServerEphemeral
	}

	pub fn resume(mut self, public_key: Option<[u8; 32]>) -> AgreementEffect<'a> {
		let Some(public_key) = public_key else {
			return self.state.reject();
		};
		self.state.ephemeral_public_key = public_key;
		AgreementEffect::Encapsulate(EncapsulationPending { state: self.state })
	}
}

pub struct EncapsulationPending<'a> {
	state: AgreementState<'a>,
}

impl<'a> EncapsulationPending<'a> {
	pub fn public_key(&self) -> Option<&[u8; 1184]> {
		match &self.state.input {
			AgreementInput::Server { registration, .. } => {
				Some(registration.beacon_pq_public_key())
			}
			AgreementInput::Beacon { .. } => None,
		}
	}

	pub fn resume(mut self, result: Option<([u8; 1088], [u8; 32])>) -> AgreementEffect<'a> {
		let Some((ciphertext, shared)) = result else {
			return self.state.reject();
		};
		self.state.kem_ciphertext = ciphertext;
		self.state.kem = RatchetChain::from_bytes(shared);
		AgreementEffect::ConvertPublic(PublicConversionPending { state: self.state })
	}
}

pub struct DecapsulationPending<'a> {
	state: AgreementState<'a>,
}

impl<'a> DecapsulationPending<'a> {
	pub fn ciphertext(&self) -> Option<&[u8; 1088]> {
		match &self.state.input {
			AgreementInput::Beacon { response, .. } => Some(&response.kem_cipher_text),
			AgreementInput::Server { .. } => None,
		}
	}

	pub fn resume(mut self, shared: Option<[u8; 32]>) -> AgreementEffect<'a> {
		let Some(shared) = shared else {
			return self.state.reject();
		};
		self.state.kem = RatchetChain::from_bytes(shared);
		AgreementEffect::Dh(DhPending {
			state: self.state,
			position: DhPosition::First,
		})
	}
}

enum DhPosition {
	First,
	Second,
	Third,
	Fourth,
}

pub struct DhRequest<'a> {
	pub secret_role: DhSecretRole,
	pub public_key: &'a [u8; 32],
}

pub struct DhPending<'a> {
	state: AgreementState<'a>,
	position: DhPosition,
}

impl<'a> DhPending<'a> {
	pub fn request(&self) -> DhRequest<'_> {
		match (&self.state.input, &self.position) {
			(AgreementInput::Server { registration, .. }, DhPosition::First) => DhRequest {
				secret_role: DhSecretRole::LocalIdentity,
				public_key: registration.beacon_prekey_public_key(),
			},
			(AgreementInput::Server { .. }, DhPosition::Second) => DhRequest {
				secret_role: DhSecretRole::ServerEphemeral,
				public_key: &self.state.remote_identity,
			},
			(AgreementInput::Server { registration, .. }, DhPosition::Third) => DhRequest {
				secret_role: DhSecretRole::ServerEphemeral,
				public_key: registration.beacon_prekey_public_key(),
			},
			(AgreementInput::Server { registration, .. }, DhPosition::Fourth) => DhRequest {
				secret_role: DhSecretRole::ServerEphemeral,
				public_key: registration.beacon_one_time_public_key(),
			},
			(AgreementInput::Beacon { .. }, DhPosition::First) => DhRequest {
				secret_role: DhSecretRole::BeaconPrekey,
				public_key: &self.state.remote_identity,
			},
			(AgreementInput::Beacon { response, .. }, DhPosition::Second) => DhRequest {
				secret_role: DhSecretRole::LocalIdentity,
				public_key: &response.ephemeral_key,
			},
			(AgreementInput::Beacon { response, .. }, DhPosition::Third) => DhRequest {
				secret_role: DhSecretRole::BeaconPrekey,
				public_key: &response.ephemeral_key,
			},
			(AgreementInput::Beacon { response, .. }, DhPosition::Fourth) => DhRequest {
				secret_role: DhSecretRole::BeaconOneTime,
				public_key: &response.ephemeral_key,
			},
		}
	}

	pub fn resume(mut self, shared: Option<[u8; 32]>) -> AgreementEffect<'a> {
		let Some(shared) = shared else {
			return self.state.reject();
		};
		match self.position {
			DhPosition::First => {
				self.state.dh1 = RatchetChain::from_bytes(shared);
				AgreementEffect::Dh(DhPending {
					state: self.state,
					position: DhPosition::Second,
				})
			}
			DhPosition::Second => {
				self.state.dh2 = RatchetChain::from_bytes(shared);
				AgreementEffect::Dh(DhPending {
					state: self.state,
					position: DhPosition::Third,
				})
			}
			DhPosition::Third => {
				self.state.dh3 = RatchetChain::from_bytes(shared);
				AgreementEffect::Dh(DhPending {
					state: self.state,
					position: DhPosition::Fourth,
				})
			}
			DhPosition::Fourth => {
				self.state.dh4 = RatchetChain::from_bytes(shared);
				finish_dh(self.state)
			}
		}
	}
}

enum AgreementCandidate<'a> {
	Server {
		pending: PendingServerRegistration,
		binding: RegistrationBinding,
	},
	Beacon {
		candidate: BeaconRegistrationCandidate,
		binding: RegistrationBinding,
		application_ciphertext: &'a [u8],
	},
}

fn finish_dh(state: AgreementState<'_>) -> AgreementEffect<'_> {
	let secrets = PqxdhSharedSecrets {
		dh1: *state.dh1.as_bytes(),
		dh2: *state.dh2.as_bytes(),
		dh3: *state.dh3.as_bytes(),
		dh4: *state.dh4.as_bytes(),
		kem_shared_secret: *state.kem.as_bytes(),
	};
	let candidate = match state.input {
		AgreementInput::Server {
			control,
			status,
			registration,
			binding,
		} => {
			let accepted = pqxdh::server_accept(
				control,
				registration,
				status,
				binding.server_pin().binding(),
				ServerCoins {
					ephemeral_public_key: state.ephemeral_public_key,
					kem_ciphertext: state.kem_ciphertext,
				},
				&secrets,
			);
			let Ok((_unchanged, pending)) = accepted else {
				return AgreementEffect::Rejected(None);
			};
			AgreementCandidate::Server { pending, binding }
		}
		AgreementInput::Beacon {
			control,
			binding,
			response,
			application_ciphertext,
		} => {
			let inputs = pqxdh::BeaconFinishInputs {
				response_server_identity: response.identity_key,
				assigned_key_id: response.key_id,
				shared_secrets: secrets,
			};
			let Ok(candidate) = pqxdh::beacon_prepare_finish(control, &inputs) else {
				return AgreementEffect::Rejected(Some(pqxdh::beacon_abort_init(control)));
			};
			AgreementCandidate::Beacon {
				candidate,
				binding,
				application_ciphertext,
			}
		}
	};
	AgreementEffect::RootKdf(RootKdfPending { candidate })
}

/// HKDF-SHA512, no salt, fixed PQXDH domain and 32-byte output.
pub struct RootKdfRequest<'a> {
	pub input: &'a [u8; 192],
	pub info: &'a [u8; 46],
}

pub struct RootKdfPending<'a> {
	candidate: AgreementCandidate<'a>,
}

impl<'a> RootKdfPending<'a> {
	pub fn request(&self) -> RootKdfRequest<'_> {
		let input = match &self.candidate {
			AgreementCandidate::Server { pending, .. } => pending.root_key_input().as_bytes(),
			AgreementCandidate::Beacon { candidate, .. } => candidate.root_key_input().as_bytes(),
		};
		RootKdfRequest {
			input,
			info: pqxdh::PQXDH_INFO,
		}
	}

	pub fn resume(mut self, root: Option<[u8; 32]>) -> AgreementEffect<'a> {
		let Some(root) = root else {
			return match self.candidate {
				AgreementCandidate::Server { .. } => AgreementEffect::Rejected(None),
				AgreementCandidate::Beacon { candidate, .. } => {
					AgreementEffect::Rejected(Some(pqxdh::beacon_abort_candidate(candidate)))
				}
			};
		};
		match &mut self.candidate {
			AgreementCandidate::Server { pending, .. } => pending.root_key_input_mut().clear(),
			AgreementCandidate::Beacon { candidate, .. } => candidate.root_key_input_mut().clear(),
		}
		let root = RatchetChain::from_bytes(root);
		match self.candidate {
			AgreementCandidate::Server { pending, binding } => {
				AgreementEffect::ServerComplete(ServerAgreement {
					pending,
					binding,
					root,
				})
			}
			AgreementCandidate::Beacon {
				candidate,
				binding,
				application_ciphertext,
			} => AgreementEffect::BeaconComplete(BeaconAgreement {
				candidate,
				binding,
				root,
				application_ciphertext,
			}),
		}
	}
}

/// Only a completed primitive trace creates this registration capability.
pub struct ServerAgreement {
	pub(crate) pending: PendingServerRegistration,
	pub(crate) binding: RegistrationBinding,
	pub(crate) root: RatchetChain,
}

impl ServerAgreement {
	pub fn registration_id(&self) -> RegistrationId {
		self.pending.registration_id()
	}
}

pub struct BeaconAgreement<'a> {
	pub(crate) candidate: BeaconRegistrationCandidate,
	pub(crate) binding: RegistrationBinding,
	pub(crate) root: RatchetChain,
	pub(crate) application_ciphertext: &'a [u8],
}
