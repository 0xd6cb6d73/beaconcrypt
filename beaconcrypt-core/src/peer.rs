// SPDX-License-Identifier: 0BSD

//! Peer ownership and the collection effects of server registration.
//!
//! Lookup and insertion replies must faithfully describe the adapter's collections.
//! The core binds each reply to an owned, one-use continuation; it does not verify
//! the allocation, hashing, or storage implementation of those collections.

use crate::agreement::{self, AgreementEffect, ServerAgreement};
use crate::pqxdh::{self, RegistrationId, ServerState};
use crate::ratchet::ConcreteRatchetKernel;
use crate::registration::{self, AuthenticatedInit, PublishedServerResponse, ServerInitialKdf};
use crate::session::{ServerAuthenticationPin, SessionBinding};

/// Core-owned immutable peer binding and the ratchet stored for that peer.
///
/// Publication constructs `Peer<ConcreteRatchetKernel>`. An adapter may wrap that
/// exact kernel for its synchronous interpreter while retaining this peer owner.
pub struct Peer<Ratchet> {
	binding: SessionBinding,
	ratchet: Ratchet,
}

impl<Ratchet> Peer<Ratchet> {
	/// Restoration boundary: the caller establishes metadata and ratchet provenance.
	pub const fn from_trusted_parts(binding: SessionBinding, ratchet: Ratchet) -> Self {
		Self { binding, ratchet }
	}

	pub const fn key_id(&self) -> u64 {
		self.binding.assigned_key_id()
	}

	pub const fn binding(&self) -> &SessionBinding {
		&self.binding
	}

	pub const fn ratchet(&self) -> &Ratchet {
		&self.ratchet
	}

	pub fn ratchet_mut(&mut self) -> &mut Ratchet {
		&mut self.ratchet
	}

	pub fn into_parts(self) -> (SessionBinding, Ratchet) {
		(self.binding, self.ratchet)
	}
}

/// Exact replay lookup before any shared-secret preparation.
pub struct RegistrationLookup {
	control: ServerState,
	authenticated: AuthenticatedInit,
}

pub fn begin_registration_lookup(
	control: ServerState,
	authenticated: AuthenticatedInit,
) -> RegistrationLookup {
	RegistrationLookup {
		control,
		authenticated,
	}
}

impl RegistrationLookup {
	pub fn request(&self) -> RegistrationId {
		self.authenticated.registration_id()
	}

	pub fn resume<'a>(self, consumed: bool) -> AgreementEffect<'a> {
		if consumed {
			return AgreementEffect::Rejected(None);
		}
		agreement::begin_server_agreement(
			self.control,
			pqxdh::RegistrationStatus::Fresh,
			self.authenticated,
		)
	}
}

/// Replay insertion is available only after successful shared-secret preparation.
pub struct RegistrationInsert {
	agreement: ServerAgreement,
}

pub fn begin_registration_insert(agreement: ServerAgreement) -> RegistrationInsert {
	RegistrationInsert { agreement }
}

impl RegistrationInsert {
	pub fn request(&self) -> RegistrationId {
		self.agreement.registration_id()
	}

	/// `inserted` is the actual insert-if-absent result for `request()`.
	pub fn resume(self, inserted: bool) -> Option<ConsumedRegistration> {
		if !inserted {
			return None;
		}
		Some(ConsumedRegistration {
			agreement: self.agreement,
		})
	}
}

/// A successful replay insertion; dropping this token never unconsumes its ID.
pub struct ConsumedRegistration {
	agreement: ServerAgreement,
}

/// Core-selected vacant-peer lookup for a consumed registration.
pub struct CompletionLookup<'a> {
	control: ServerState,
	pin: ServerAuthenticationPin,
	registration: ConsumedRegistration,
	application: &'a [u8],
	key_id: u64,
}

pub fn begin_completion_lookup<'a>(
	control: ServerState,
	pin: ServerAuthenticationPin,
	registration: ConsumedRegistration,
	application: &'a [u8],
) -> Result<CompletionLookup<'a>, ServerState> {
	let key_id = match pqxdh::server_next_key_id(control) {
		Ok(key_id) => key_id,
		Err(_) => return Err(control),
	};
	Ok(CompletionLookup {
		control,
		pin,
		registration,
		application,
		key_id,
	})
}

impl<'a> CompletionLookup<'a> {
	pub const fn request(&self) -> u64 {
		self.key_id
	}

	/// `occupied` is the actual membership reply for this continuation's key ID.
	pub fn resume(self, occupied: bool) -> Result<ServerInitialKdf<'a>, ServerState> {
		let availability = if occupied {
			pqxdh::KeyIdAvailability::Occupied
		} else {
			pqxdh::KeyIdAvailability::Available
		};
		registration::begin_server_completion(
			self.control,
			&self.pin,
			availability,
			self.registration.agreement,
			self.application,
		)
	}
}

/// Exact peer insertion obtained from completed sealing, signing, and encoding.
pub struct PeerInsert<Encoded> {
	previous: ServerState,
	next: ServerState,
	peer: Peer<ConcreteRatchetKernel>,
	encoded: Encoded,
}

pub fn begin_peer_insert<Encoded>(
	control: ServerState,
	published: PublishedServerResponse<Encoded>,
) -> Result<PeerInsert<Encoded>, ServerState> {
	let key_id = match pqxdh::server_next_key_id(control) {
		Ok(key_id) => key_id,
		Err(_) => return Err(control),
	};
	let (next, binding, kernel, encoded) = published.into_parts();
	if next.last_key_id() != key_id {
		return Err(control);
	}
	Ok(PeerInsert {
		previous: control,
		next,
		peer: Peer::from_trusted_parts(binding, kernel),
		encoded,
	})
}

impl<Encoded> PeerInsert<Encoded> {
	pub const fn request(&self) -> u64 {
		self.peer.key_id()
	}

	/// Transfer the exact peer to the map interpreter, retaining publication rights.
	pub fn into_parts(self) -> (Peer<ConcreteRatchetKernel>, PublicationFinish<Encoded>) {
		let key_id = self.peer.key_id();
		(
			self.peer,
			PublicationFinish {
				previous: self.previous,
				next: self.next,
				key_id,
				encoded: self.encoded,
			},
		)
	}
}

pub struct PublicationFinish<Encoded> {
	previous: ServerState,
	next: ServerState,
	key_id: u64,
	encoded: Encoded,
}

impl<Encoded> PublicationFinish<Encoded> {
	/// Publish the allocation counter and response only after actual vacant insertion.
	pub fn finish(self, inserted: bool) -> Result<PublishedPeer<Encoded>, ServerState> {
		if !inserted {
			return Err(self.previous);
		}
		Ok(PublishedPeer {
			control: self.next,
			key_id: self.key_id,
			encoded: self.encoded,
		})
	}
}

pub struct PublishedPeer<Encoded> {
	control: ServerState,
	key_id: u64,
	encoded: Encoded,
}

impl<Encoded> PublishedPeer<Encoded> {
	pub fn into_parts(self) -> (ServerState, u64, Encoded) {
		(self.control, self.key_id, self.encoded)
	}
}
