// SPDX-License-Identifier: 0BSD

//! Bounded coordination of independent optimistic commits. Native callbacks stay with callers.

use std::{
	sync::{Arc, Mutex, mpsc},
	thread::{self, JoinHandle},
	time::{Duration, Instant},
};

#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

use beaconcrypt::RowError;
use zeroize::{Zeroize, Zeroizing};

use super::buffered::{ReadSet, WriteSet};

#[derive(Clone, Copy, Debug)]
pub struct BatchConfig {
	pub max_requests: usize,
	pub max_bytes: usize,
	pub queue_capacity: usize,
	pub max_delay: Duration,
}

impl Default for BatchConfig {
	fn default() -> Self {
		Self {
			max_requests: 8,
			max_bytes: 1024 * 1024,
			queue_capacity: 8,
			max_delay: Duration::from_micros(100),
		}
	}
}

impl BatchConfig {
	pub fn validate(&self) -> Result<(), RowError> {
		// Bound queued and active logical key/value bytes, including one carry. Blocked callers
		// retain their own candidate outside this bound; allocator/entry overhead is not counted.
		let buffered_bytes = self
			.queue_capacity
			.checked_add(2)
			.and_then(|count| count.checked_mul(self.max_bytes));
		if self.max_requests == 0
			|| self.max_requests > 1024
			|| self.queue_capacity == 0
			|| self.queue_capacity > 1024
			|| self.max_bytes == 0
			|| !matches!(buffered_bytes, Some(bytes) if bytes <= 1024 * 1024 * 1024)
			|| self.max_delay > Duration::from_secs(1)
			|| Instant::now().checked_add(self.max_delay).is_none()
		{
			return Err(storage("invalid PostgreSQL batch bounds"));
		}
		Ok(())
	}
}

pub type ChangeSet = Zeroizing<RowChanges>;

pub struct RowChanges {
	pub reads: ReadSet,
	pub writes: WriteSet,
}

impl RowChanges {
	fn bytes(&self) -> Option<usize> {
		// The entry byte also bounds the number of empty values and absent expectations.
		self.reads
			.iter()
			.map(|(key, value)| (key.len(), value.as_ref().map_or(0, Vec::len)))
			.chain(
				self.writes
					.iter()
					.map(|(key, value)| (key.len(), value.len())),
			)
			.try_fold(0usize, |total, (key, value)| {
				total.checked_add(1)?.checked_add(key)?.checked_add(value)
			})
	}

	fn independent(&self, other: &Self) -> bool {
		!self
			.writes
			.keys()
			.any(|key| other.reads.contains_key(key) || other.writes.contains_key(key))
			&& !other.writes.keys().any(|key| self.reads.contains_key(key))
	}
}

impl Zeroize for RowChanges {
	fn zeroize(&mut self) {
		for value in self.reads.values_mut().flatten() {
			value.zeroize();
		}
		for value in self.writes.values_mut() {
			value.zeroize();
		}
	}
}

#[derive(Debug)]
pub struct BatchReceipt {
	pub status: Result<(), RowError>,
	pub leader: bool,
	#[cfg(test)]
	pub batch_len: usize,
}

struct Request {
	changes: ChangeSet,
	bytes: usize,
	reply: mpsc::Sender<BatchReceipt>,
}

#[cfg(test)]
#[derive(Default)]
struct QueueCounts {
	submitted: AtomicUsize,
	received: AtomicUsize,
}

struct Inbox {
	receiver: mpsc::Receiver<Request>,
	#[cfg(test)]
	counts: Arc<QueueCounts>,
}

impl Inbox {
	fn received(&self) {
		#[cfg(test)]
		self.counts.received.fetch_add(1, Ordering::SeqCst);
	}

	fn first(&self) -> Result<Request, mpsc::RecvError> {
		let request = self.receiver.recv()?;
		self.received();
		Ok(request)
	}

	fn next(&self, deadline: Instant) -> Result<Request, mpsc::RecvTimeoutError> {
		let remaining = deadline.saturating_duration_since(Instant::now());
		let request = if remaining.is_zero() {
			self.receiver.try_recv().map_err(|error| match error {
				mpsc::TryRecvError::Empty => mpsc::RecvTimeoutError::Timeout,
				mpsc::TryRecvError::Disconnected => mpsc::RecvTimeoutError::Disconnected,
			})?
		} else {
			self.receiver.recv_timeout(remaining)?
		};
		self.received();
		Ok(request)
	}
}

struct Worker {
	handle: Option<JoinHandle<()>>,
	outcome: Option<Result<(), RowError>>,
}

impl Worker {
	fn join(&mut self) -> Result<(), RowError> {
		if let Some(handle) = self.handle.take() {
			self.outcome = Some(
				handle
					.join()
					.map_err(|_| storage("PostgreSQL batch coordinator panicked")),
			);
		}
		self.outcome.clone().unwrap_or(Ok(()))
	}
}

struct Inner {
	config: BatchConfig,
	// A blocking send holds this lock, so closing admission cannot overtake an accepted send.
	admission: Mutex<Option<mpsc::SyncSender<Request>>>,
	worker: Mutex<Worker>,
	#[cfg(test)]
	counts: Arc<QueueCounts>,
}

impl Drop for Inner {
	fn drop(&mut self) {
		self.admission
			.get_mut()
			.unwrap_or_else(std::sync::PoisonError::into_inner)
			.take();
		let _ = self
			.worker
			.get_mut()
			.unwrap_or_else(std::sync::PoisonError::into_inner)
			.join();
	}
}

#[derive(Clone)]
pub struct Batcher {
	inner: Arc<Inner>,
}

impl Batcher {
	/// `commit` returns only after the outer transaction's durable acknowledgement.
	/// It must acquire all batch locks in the same global order as ordinary writers.
	pub fn start(
		config: BatchConfig,
		commit: impl FnMut(&[ChangeSet]) -> Result<Vec<bool>, RowError> + Send + 'static,
	) -> Result<Self, RowError> {
		config.validate()?;
		let (sender, receiver) = mpsc::sync_channel(config.queue_capacity);
		#[cfg(test)]
		let counts = Arc::new(QueueCounts::default());
		let inbox = Inbox {
			receiver,
			#[cfg(test)]
			counts: Arc::clone(&counts),
		};
		let handle = thread::Builder::new()
			.name("pg-batch-commit".into())
			.spawn(move || run(config, inbox, commit))
			.map_err(|error| {
				storage(&format!(
					"cannot start PostgreSQL batch coordinator: {error}"
				))
			})?;
		Ok(Self {
			inner: Arc::new(Inner {
				config,
				admission: Mutex::new(Some(sender)),
				worker: Mutex::new(Worker {
					handle: Some(handle),
					outcome: None,
				}),
				#[cfg(test)]
				counts,
			}),
		})
	}

	pub fn commit(&self, changes: ChangeSet) -> Result<BatchReceipt, RowError> {
		self.submit(changes)?.recv().map_err(|_| {
			storage("PostgreSQL batch result unavailable; commit outcome may be unknown")
		})
	}

	fn submit(&self, changes: ChangeSet) -> Result<mpsc::Receiver<BatchReceipt>, RowError> {
		let bytes = changes
			.bytes()
			.filter(|size| *size <= self.inner.config.max_bytes)
			.ok_or_else(|| storage("PostgreSQL change set exceeds batch byte bound"))?;
		let (reply, received) = mpsc::channel();
		let admission = self
			.inner
			.admission
			.lock()
			.unwrap_or_else(std::sync::PoisonError::into_inner);
		let sender = admission
			.as_ref()
			.ok_or_else(|| storage("PostgreSQL batch coordinator is shut down"))?;
		sender
			.send(Request {
				changes,
				bytes,
				reply,
			})
			.map_err(|_| storage("PostgreSQL batch coordinator disconnected before submission"))?;
		#[cfg(test)]
		self.inner.counts.submitted.fetch_add(1, Ordering::SeqCst);
		Ok(received)
	}

	/// Stop admission, drain every accepted request, and join before database fixture cleanup.
	pub fn shutdown(&self) -> Result<(), RowError> {
		self.inner
			.admission
			.lock()
			.unwrap_or_else(std::sync::PoisonError::into_inner)
			.take();
		// Keep the join lock until completion: concurrent shutdown calls must also wait for it.
		self.inner
			.worker
			.lock()
			.unwrap_or_else(std::sync::PoisonError::into_inner)
			.join()
	}

	#[cfg(test)]
	pub(super) fn pending_for_test(&self) -> usize {
		self.inner
			.counts
			.submitted
			.load(Ordering::SeqCst)
			.saturating_sub(self.inner.counts.received.load(Ordering::SeqCst))
	}
}

fn run(
	config: BatchConfig,
	inbox: Inbox,
	mut commit: impl FnMut(&[ChangeSet]) -> Result<Vec<bool>, RowError>,
) {
	let mut carry = None;
	loop {
		let first = match carry.take().map(Ok).unwrap_or_else(|| inbox.first()) {
			Ok(request) => request,
			Err(_) => break,
		};
		let deadline = Instant::now() + config.max_delay;
		let mut bytes = first.bytes;
		let mut changes = Vec::with_capacity(config.max_requests);
		let mut replies = Vec::with_capacity(config.max_requests);
		changes.push(first.changes);
		replies.push(first.reply);
		while changes.len() < config.max_requests {
			let next = match inbox.next(deadline) {
				Ok(request) => request,
				Err(_) => break,
			};
			let size = bytes.checked_add(next.bytes);
			if !matches!(size, Some(size) if size <= config.max_bytes)
				|| !changes
					.iter()
					.all(|change| change.independent(&next.changes))
			{
				carry = Some(next);
				break;
			}
			bytes = size.expect("checked batch byte count");
			changes.push(next.changes);
			replies.push(next.reply);
		}
		let batch_len = changes.len();
		let outcome = match commit(&changes) {
			Ok(statuses) if statuses.len() == batch_len => Ok(statuses),
			Ok(_) => Err(storage(
				"PostgreSQL batch returned the wrong number of statuses",
			)),
			Err(error @ RowError::Storage(_)) => Err(error),
			Err(error) => Err(storage(&error.to_string())),
		};
		for (index, reply) in replies.into_iter().enumerate() {
			let status = match &outcome {
				Ok(statuses) if statuses[index] => Ok(()),
				Ok(_) => Err(RowError::Conflict),
				Err(error) => Err(error.clone()),
			};
			let _ = reply.send(BatchReceipt {
				status,
				leader: index == 0,
				#[cfg(test)]
				batch_len,
			});
		}
	}
}

fn storage(message: &str) -> RowError {
	RowError::Storage(message.into())
}

#[cfg(test)]
#[path = "postgres_batch_tests.rs"]
mod tests;
