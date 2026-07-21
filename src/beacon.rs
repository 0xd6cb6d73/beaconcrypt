// SPDX-License-Identifier: 0BSD

pub trait ProviderBeacon {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>>;
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>>;
}
