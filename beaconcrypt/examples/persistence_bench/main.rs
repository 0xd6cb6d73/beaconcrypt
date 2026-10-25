// SPDX-License-Identifier: 0BSD

//! Controlled persistence-component benchmark. See doc/impl/row-persistence-benchmark.md.

#[cfg(test)]
mod adapter_tests;
mod buffered;
mod concurrency;
mod concurrency_schedule;
mod database;
#[cfg(test)]
mod native_postgres_tests;
mod postgres;

use std::{
	error::Error,
	fs::{File, OpenOptions},
	io::{Seek, Write},
	path::PathBuf,
	process::Command,
	rc::Rc,
	time::{Instant, SystemTime, UNIX_EPOCH},
};

use self::postgres::{PgFixture, PgRowStore, PgSnapshotStore};
use beaconcrypt::{
	Beacon, CachedRowServer, Decrypted, Encrypted, PersistentServer, ProviderBeacon, RegResponse,
	RowServer, RowStore, SnapshotLineage, SnapshotStore,
};
use database::{Counters, Counts, SqlRowStore, SqlSnapshotStore};
use serde::Serialize;
use serde_json::{Value, json};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
const MYTHIC_REFERENCE: &str = "200af54bd8500d6d619b98d952fd4851e540ce10";
const SERVER_ID: u64 = 19;

#[derive(Clone, Serialize)]
struct Config {
	backend: String,
	peer_counts: Vec<usize>,
	trials: usize,
	extra_registrations: usize,
	active_peers: Option<usize>,
	small_bytes: usize,
	small_messages: usize,
	large_bytes: usize,
	large_messages: usize,
	mixed_messages: usize,
	large_every: usize,
	burst_chunk_bytes: usize,
	burst_chunks: Vec<usize>,
	warmup_messages: usize,
}

impl Default for Config {
	fn default() -> Self {
		Self {
			backend: "sqlite".into(),
			peer_counts: vec![1, 100, 1000],
			trials: 3,
			extra_registrations: 0,
			active_peers: None,
			small_bytes: 1024,
			small_messages: 1024,
			large_bytes: 64 * 1024,
			large_messages: 128,
			mixed_messages: 1024,
			large_every: 16,
			burst_chunk_bytes: 512_000,
			burst_chunks: vec![64, 256, 512],
			warmup_messages: 16,
		}
	}
}

struct Options {
	config: Config,
	concurrent: bool,
	concurrency: concurrency::Config,
	output: PathBuf,
	database_directory: Option<PathBuf>,
}

fn parse_list(value: &str) -> Result<Vec<usize>> {
	let mut seen = std::collections::HashSet::new();
	value
		.split(',')
		.map(|part| {
			let value = part.parse()?;
			if !seen.insert(value) {
				return Err(format!("duplicate list axis value: {value}").into());
			}
			Ok(value)
		})
		.collect()
}

fn options() -> Result<Option<Options>> {
	let mut config = Config::default();
	let mut output = PathBuf::from("row-persistence-benchmark.json");
	let mut database_directory = None;
	let mut concurrent = false;
	let mut concurrency = concurrency::Config::default();
	let mut run = false;
	let mut args = std::env::args().skip(1);
	while let Some(arg) = args.next() {
		if matches!(arg.as_str(), "--help" | "-h") {
			println!(
				"persistence_bench --run --output REPORT.json [options]\n\
This is a durable SQLite/PostgreSQL component benchmark, not a Mythic end-to-end benchmark.\n\
Run only in an explicitly approved quiet window with no other active coordination leases.\n\
Options: --backend sqlite|postgres (PostgreSQL DSN: BEACONCRYPT_BENCH_POSTGRES)\n\
         --peers 1,100,1000 --trials 3 --extra-registrations 0 --active-peers N\n\
         --small-bytes 1024 --small-messages 1024 --large-bytes 65536 --large-messages 128\n\
         --mixed-messages 1024 --large-every 16 --burst-chunk-bytes 512000\n\
         --burst-chunks 64,256,512 --warmup-messages 16 --database-directory DIR\n\
         --mode serial|concurrent --workers 8 --period-ms 1000,100,10,5\n\
         --arrival-ms 2000 --queue-capacity 256 --queue-bytes 16777216\n\
         --deadline-ms 1000 --drain-ms 600000 --max-offered 20000\n\
         --max-precomputed-bytes 536870912\n\
All measured payloads are deterministic and generated before timing. Outputs are checked afterward.\n\
Reports refuse to overwrite an existing file. Database fixtures are temporary, even when DIR is given."
			);
			return Ok(None);
		}
		if arg == "--run" {
			run = true;
			continue;
		}
		let value = args
			.next()
			.ok_or_else(|| format!("missing value after {arg}"))?;
		match arg.as_str() {
			"--mode" => {
				concurrent = match value.as_str() {
					"serial" => false,
					"concurrent" => true,
					_ => return Err("--mode must be serial or concurrent".into()),
				}
			}
			"--workers" => concurrency.workers = value.parse()?,
			"--period-ms" => concurrency.period_ms = parse_list(&value)?,
			"--arrival-ms" => concurrency.arrival_ms = value.parse()?,
			"--queue-capacity" => concurrency.queue_capacity = value.parse()?,
			"--queue-bytes" => concurrency.queue_bytes = value.parse()?,
			"--deadline-ms" => concurrency.deadline_ms = value.parse()?,
			"--drain-ms" => concurrency.drain_ms = value.parse()?,
			"--max-offered" => concurrency.max_offered = value.parse()?,
			"--max-precomputed-bytes" => concurrency.max_precomputed_bytes = value.parse()?,
			"--output" => output = value.into(),
			"--backend" => config.backend = value,
			"--database-directory" => database_directory = Some(value.into()),
			"--peers" => config.peer_counts = parse_list(&value)?,
			"--trials" => config.trials = value.parse()?,
			"--extra-registrations" => config.extra_registrations = value.parse()?,
			"--active-peers" => config.active_peers = Some(value.parse()?),
			"--small-bytes" => config.small_bytes = value.parse()?,
			"--small-messages" => config.small_messages = value.parse()?,
			"--large-bytes" => config.large_bytes = value.parse()?,
			"--large-messages" => config.large_messages = value.parse()?,
			"--mixed-messages" => config.mixed_messages = value.parse()?,
			"--large-every" => config.large_every = value.parse()?,
			"--burst-chunk-bytes" => config.burst_chunk_bytes = value.parse()?,
			"--burst-chunks" => config.burst_chunks = parse_list(&value)?,
			"--warmup-messages" => config.warmup_messages = value.parse()?,
			_ => return Err(format!("unknown argument {arg}").into()),
		}
	}
	if !run {
		return Err(
			"execution requires --run after arranging an approved quiet benchmark window".into(),
		);
	}
	if !matches!(config.backend.as_str(), "sqlite" | "postgres") {
		return Err("--backend must be sqlite or postgres".into());
	}
	if config.trials == 0
		|| config.peer_counts.is_empty()
		|| config.peer_counts.contains(&0)
		|| config.active_peers == Some(0)
		|| config.large_every == 0
		|| config.burst_chunks.is_empty()
		|| config.burst_chunks.contains(&0)
		|| [
			config.small_messages,
			config.large_messages,
			config.mixed_messages,
		]
		.contains(&0)
	{
		return Err("trial, peer, message and period counts must be positive".into());
	}
	for bytes in [
		config.small_bytes,
		config.large_bytes,
		config.burst_chunk_bytes,
	] {
		if bytes == 0 || bytes > beaconcrypt::MAX_MESSAGE_SIZE - 128 {
			return Err(
				"payload sizes must be positive and leave framing room below MAX_MESSAGE_SIZE"
					.into(),
			);
		}
	}
	Ok(Some(Options {
		config,
		concurrent,
		concurrency,
		output,
		database_directory,
	}))
}

#[derive(Clone, Copy, Debug)]
enum Arm {
	Snapshot,
	Row,
	Cached,
}

impl Arm {
	fn label(self) -> &'static str {
		match self {
			Self::Snapshot => "snapshot",
			Self::Row => "row",
			Self::Cached => "cached_row",
		}
	}
	fn index(self) -> usize {
		match self {
			Self::Snapshot => 0,
			Self::Row => 1,
			Self::Cached => 2,
		}
	}
}

enum Location {
	Sqlite(PathBuf),
	Postgres(Rc<PgFixture>),
}
impl Location {
	fn new(backend: &str, path: PathBuf, lineage: SnapshotLineage) -> Result<Self> {
		Ok(match backend {
			"sqlite" => Self::Sqlite(path),
			"postgres" => Self::Postgres(PgFixture::create(
				&std::env::var("BEACONCRYPT_BENCH_POSTGRES").map_err(
					|_| "set BEACONCRYPT_BENCH_POSTGRES to a dedicated loopback TCP database",
				)?,
				lineage,
			)?),
			_ => unreachable!(),
		})
	}
	fn snapshot(&self, counts: Rc<Counters>) -> Result<Box<dyn SnapshotStore>> {
		Ok(match self {
			Self::Sqlite(path) => Box::new(SqlSnapshotStore::open(path, counts)?),
			Self::Postgres(fixture) => Box::new(PgSnapshotStore::open(Rc::clone(fixture), counts)?),
		})
	}
	fn rows(&self, counts: Rc<Counters>) -> Result<Box<dyn RowStore>> {
		Ok(match self {
			Self::Sqlite(path) => Box::new(SqlRowStore::open(path, counts)?),
			Self::Postgres(fixture) => Box::new(PgRowStore::open(Rc::clone(fixture), counts)?),
		})
	}
	fn checkpoint(&self) -> Result<()> {
		match self {
			Self::Sqlite(path) => Ok(database::checkpoint(path)?),
			Self::Postgres(fixture) => fixture.checkpoint(),
		}
	}
	fn footprint(&self, arm: Arm) -> Result<Value> {
		match self {
			Self::Sqlite(path) => Ok(database::footprint(path, !matches!(arm, Arm::Snapshot))?),
			Self::Postgres(fixture) => fixture.footprint(!matches!(arm, Arm::Snapshot)),
		}
	}
	fn settings(&self) -> Value {
		match self {
			Self::Sqlite(_) => {
				json!({"settings":database::SQL_SETTINGS,"transport":"in-process SQLite","row_adapter":"optimistic buffered validation at commit"})
			}
			Self::Postgres(fixture) => fixture.settings.clone(),
		}
	}
}

enum Backend {
	Snapshot(PersistentServer<Box<dyn SnapshotStore>>),
	Row(RowServer<Box<dyn RowStore>>),
	Cached(CachedRowServer<Box<dyn RowStore>>),
}
impl Backend {
	fn create(
		arm: Arm,
		location: &Location,
		counts: Rc<Counters>,
		lineage: SnapshotLineage,
		capacity: usize,
	) -> Result<Self> {
		Ok(match arm {
			Arm::Snapshot => Self::Snapshot(PersistentServer::create_with_lineage(
				SERVER_ID,
				Some(&[0x52; 32]),
				Some(&[0x53; 32]),
				location.snapshot(counts)?,
				lineage,
			)?),
			Arm::Row => Self::Row(RowServer::create(
				SERVER_ID,
				Some(&[0x52; 32]),
				Some(&[0x53; 32]),
				location.rows(counts)?,
				lineage,
			)?),
			Arm::Cached => Self::Cached(CachedRowServer::create(
				SERVER_ID,
				Some(&[0x52; 32]),
				Some(&[0x53; 32]),
				location.rows(counts)?,
				lineage,
				capacity,
			)?),
		})
	}
	fn open(
		arm: Arm,
		location: &Location,
		counts: Rc<Counters>,
		lineage: SnapshotLineage,
		capacity: usize,
	) -> Result<(Self, u64)> {
		// Prepare connections and SQL statements before measuring native restoration.
		match arm {
			Arm::Snapshot => {
				let store = location.snapshot(counts)?;
				let start = Instant::now();
				let server = PersistentServer::restore(store)?;
				Ok((Self::Snapshot(server), nanos(start.elapsed())))
			}
			Arm::Row => {
				let store = location.rows(counts)?;
				let start = Instant::now();
				let server = RowServer::open(store, lineage)?;
				Ok((Self::Row(server), nanos(start.elapsed())))
			}
			Arm::Cached => {
				let store = location.rows(counts)?;
				let start = Instant::now();
				let server = CachedRowServer::open(store, lineage, capacity)?;
				Ok((Self::Cached(server), nanos(start.elapsed())))
			}
		}
	}
	fn beacon(&self) -> Result<Beacon> {
		let (public, mldsa) = match self {
			Self::Snapshot(s) => (s.identity_pk(), s.mldsa_public_key()),
			Self::Row(s) => (s.identity_pk(), s.mldsa_public_key()),
			Self::Cached(s) => (s.identity_pk(), s.mldsa_public_key()),
		};
		Ok(Beacon::try_new(SERVER_ID, public.as_bytes(), &mldsa)?)
	}
	fn register(&mut self, request: &[u8], data: Option<&[u8]>) -> Result<Option<RegResponse>> {
		Ok(match self {
			Self::Snapshot(s) => match s.get_shared_secret(request)? {
				Some(pending) => s.build_registration_response(pending, data)?,
				None => None,
			},
			Self::Row(s) => s.register_beacon(request, data)?,
			Self::Cached(s) => s.register_beacon(request, data)?,
		})
	}
	fn encrypt(&mut self, bytes: &[u8], kid: u64) -> Result<Encrypted> {
		let output = match self {
			Self::Snapshot(s) => s.encrypt_message(bytes, kid)?,
			Self::Row(s) => s.encrypt_message(bytes, kid)?,
			Self::Cached(s) => s.encrypt_message(bytes, kid)?,
		};
		output.ok_or_else(|| "send rejected".into())
	}
	fn decrypt(&mut self, bytes: &[u8]) -> Result<Decrypted> {
		let output = match self {
			Self::Snapshot(s) => s.decrypt_message(bytes)?,
			Self::Row(s) => s.decrypt_message(bytes)?,
			Self::Cached(s) => s.decrypt_message(bytes)?,
		};
		output.ok_or_else(|| "receive rejected".into())
	}
	fn cached_peers(&self) -> Option<usize> {
		match self {
			Self::Cached(s) => Some(s.cached_peer_count()),
			_ => None,
		}
	}
}

struct Fixture {
	arm: Arm,
	location: Location,
	lineage: SnapshotLineage,
	server: Backend,
	beacons: Vec<Beacon>,
	kids: Vec<u64>,
	send_sequences: Vec<u64>,
	receive_sequences: Vec<u64>,
	counts: Rc<Counters>,
	setup_ns: u64,
	warm_database_open_ns: u64,
	cold_open_counts: Counts,
	cache_fill_counts: Counts,
	warm_counts: Counts,
}

impl Fixture {
	fn new(arm: Arm, path: PathBuf, peers: usize, config: &Config) -> Result<Self> {
		let start = Instant::now();
		libsodium_rs::ensure_init()?;
		let mut lineage_bytes = [0; 32];
		libsodium_rs::random::fill_bytes(&mut lineage_bytes);
		let lineage = SnapshotLineage::from_bytes(lineage_bytes);
		let counts = Rc::new(Counters::default());
		let active = config.active_peers.unwrap_or(peers).min(peers);
		let location = Location::new(&config.backend, path, lineage)?;
		let mut server = Backend::create(arm, &location, Rc::clone(&counts), lineage, active)?;
		let mut beacons = Vec::with_capacity(peers);
		let mut kids = Vec::with_capacity(peers);
		for _ in 0..peers {
			let mut beacon = server.beacon()?;
			let request = beacon
				.get_registration_bundle()
				.ok_or("registration bundle failed")?;
			let response = server
				.register(&request, Some(b"benchmark registration"))?
				.ok_or("registration rejected")?;
			let plaintext = beacon
				.finish_registration(&response.serialized)
				.ok_or("registration response rejected")?;
			assert_eq!(plaintext, b"benchmark registration");
			kids.push(response.kid);
			beacons.push(beacon);
		}
		// Additional accepted registrations whose empty responses fail grow only replay history.
		for _ in 0..config.extra_registrations {
			let mut beacon = server.beacon()?;
			let request = beacon
				.get_registration_bundle()
				.ok_or("history fixture failed")?;
			assert!(server.register(&request, Some(b""))?.is_none());
		}
		drop(server);
		counts.take();
		let (server, warm_database_open_ns) =
			Backend::open(arm, &location, Rc::clone(&counts), lineage, active)?;
		let cold_open_counts = counts.take();
		let mut result = Self {
			arm,
			location,
			lineage,
			server,
			beacons,
			kids,
			send_sequences: vec![1; peers],
			receive_sequences: vec![0; peers],
			cache_fill_counts: counts.take(),
			warm_counts: counts.take(),
			cold_open_counts,
			counts,
			setup_ns: nanos(start.elapsed()),
			warm_database_open_ns,
		};
		for peer in 0..active {
			result.warm_exchange(peer)?;
		}
		result.cache_fill_counts = result.counts.take();
		for i in 0..config.warmup_messages {
			result.warm_exchange(i % active)?;
		}
		result.warm_counts = result.counts.take();
		if let Some(cached) = result.server.cached_peers() {
			assert_eq!(
				cached, active,
				"all eligible peers must be cached before measurements"
			);
		}
		result.counts.take();
		Ok(result)
	}
	fn warm_exchange(&mut self, peer: usize) -> Result<()> {
		let encrypted = self.server.encrypt(b"warmup", self.kids[peer])?;
		let received = self.beacons[peer]
			.decrypt_message(&encrypted.ciphertext)
			.ok_or("warmup send invalid")?;
		assert_eq!(received.plaintext, b"warmup");
		self.send_sequences[peer] += 1;
		let encrypted = self.beacons[peer]
			.encrypt_message(b"warmup")
			.ok_or("warmup client failed")?;
		assert_eq!(
			self.server.decrypt(&encrypted.ciphertext)?.plaintext,
			b"warmup"
		);
		self.receive_sequences[peer] += 1;
		Ok(())
	}
}

fn nanos(duration: std::time::Duration) -> u64 {
	u64::try_from(duration.as_nanos()).expect("benchmark duration fits nanoseconds")
}

/// Deterministic non-secret SplitMix64 bytes; this is only benchmark payload generation.
fn payload(length: usize, seed: u64) -> Vec<u8> {
	let mut state = seed;
	let mut result = Vec::with_capacity(length);
	while result.len() < length {
		state = state.wrapping_add(0x9e3779b97f4a7c15);
		let mut value = state;
		value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
		value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
		value ^= value >> 31;
		let remaining = (length - result.len()).min(8);
		result.extend_from_slice(&value.to_le_bytes()[..remaining]);
	}
	result
}

struct Payloads {
	small: Vec<u8>,
	large: Vec<u8>,
	chunk: Vec<u8>,
}

#[derive(Clone, Copy)]
enum Pattern {
	Small,
	Large,
	Mixed,
	Burst,
}

struct Scenario {
	name: String,
	messages: usize,
	pattern: Pattern,
}

impl Scenario {
	fn bytes<'a>(&self, index: usize, config: &Config, payloads: &'a Payloads) -> &'a [u8] {
		match self.pattern {
			Pattern::Small => &payloads.small,
			Pattern::Large => &payloads.large,
			Pattern::Mixed if (index + 1).is_multiple_of(config.large_every) => &payloads.large,
			Pattern::Mixed => &payloads.small,
			Pattern::Burst => &payloads.chunk,
		}
	}
}

fn scenarios(config: &Config) -> Vec<Scenario> {
	let mut result = vec![
		Scenario {
			name: "small_stream".into(),
			messages: config.small_messages,
			pattern: Pattern::Small,
		},
		Scenario {
			name: "large_stream".into(),
			messages: config.large_messages,
			pattern: Pattern::Large,
		},
		Scenario {
			name: "mixed_stream".into(),
			messages: config.mixed_messages,
			pattern: Pattern::Mixed,
		},
	];
	result.extend(config.burst_chunks.iter().map(|chunks| Scenario {
		name: format!("burst_{chunks}"),
		messages: *chunks,
		pattern: Pattern::Burst,
	}));
	result
}

#[derive(Clone, Copy)]
enum Direction {
	Send,
	Receive,
}

impl Direction {
	fn label(self) -> &'static str {
		match self {
			Self::Send => "send",
			Self::Receive => "receive",
		}
	}
}

fn percentile(sorted: &[u64], percentage: usize) -> u64 {
	sorted[(sorted.len() * percentage).div_ceil(100).saturating_sub(1)]
}

fn measure(
	fixture: &mut Fixture,
	scenario: &Scenario,
	direction: Direction,
	config: &Config,
	payloads: &Payloads,
	trial: usize,
	pair_order: usize,
) -> Result<Value> {
	let peers = fixture.beacons.len();
	let active = config.active_peers.unwrap_or(peers).min(peers);
	let mut frames = Vec::new();
	if matches!(direction, Direction::Receive) {
		frames.reserve(scenario.messages);
		for i in 0..scenario.messages {
			frames.push(
				fixture.beacons[i % active]
					.encrypt_message(scenario.bytes(i, config, payloads))
					.ok_or("client frame generation failed")?
					.ciphertext,
			);
		}
	}
	// Allocate result/measurement containers before timing. No client crypto, payload generation,
	// output verification, reporting, database scanning, or intentional sleep occurs in the batch.
	let mut outputs: Vec<(Vec<u8>, u64, u64)> = Vec::with_capacity(scenario.messages);
	let mut latencies = Vec::with_capacity(scenario.messages);
	let plaintext_bytes: usize = (0..scenario.messages)
		.map(|i| scenario.bytes(i, config, payloads).len())
		.sum();
	fixture.location.checkpoint()?;
	let footprint_before = fixture.location.footprint(fixture.arm)?;
	fixture.counts.take();
	let mut incoming = frames.iter();
	let started = Instant::now();
	for i in 0..scenario.messages {
		let peer = i % active;
		let bytes = scenario.bytes(i, config, payloads);
		let operation = Instant::now();
		let output = match direction {
			Direction::Send => {
				let output = fixture.server.encrypt(bytes, fixture.kids[peer])?;
				(output.ciphertext, output.key_id, output.seq)
			}
			Direction::Receive => {
				let output = fixture
					.server
					.decrypt(incoming.next().expect("one prepared frame per receive"))?;
				(output.plaintext, output.key_id, output.seq)
			}
		};
		latencies.push(nanos(operation.elapsed()));
		outputs.push(output);
	}
	let batch_ns = nanos(started.elapsed());
	let counts = fixture.counts.take();
	let footprint_after = fixture.location.footprint(fixture.arm)?;
	let wire_bytes: usize = match direction {
		Direction::Send => outputs.iter().map(|value| value.0.len()).sum(),
		Direction::Receive => frames.iter().map(Vec::len).sum(),
	};
	for (i, (bytes, kid, seq)) in outputs.into_iter().enumerate() {
		let peer = i % active;
		assert_eq!(kid, fixture.kids[peer], "output routed to wrong peer");
		let plaintext = match direction {
			Direction::Send => {
				fixture.send_sequences[peer] += 1;
				assert_eq!(seq, fixture.send_sequences[peer]);
				let output = fixture.beacons[peer]
					.decrypt_message(&bytes)
					.ok_or("server ciphertext verification failed")?;
				assert_eq!(output.key_id, SERVER_ID);
				assert_eq!(output.seq, seq);
				output.plaintext
			}
			Direction::Receive => {
				fixture.receive_sequences[peer] += 1;
				assert_eq!(seq, fixture.receive_sequences[peer]);
				bytes
			}
		};
		assert_eq!(
			plaintext,
			scenario.bytes(i, config, payloads),
			"payload mismatch"
		);
	}
	let operation_ns: u64 = latencies.iter().sum();
	let mut sorted = latencies.clone();
	sorted.sort_unstable();
	let seconds = batch_ns as f64 / 1e9;
	Ok(json!({
		"arm": fixture.arm.label(), "trial": trial, "pair_order": pair_order,
		"peers": peers, "active_peers": active, "touched_peers": active.min(scenario.messages),
		"consumed_registrations": peers + config.extra_registrations,
		"scenario": scenario.name, "direction": direction.label(),
		"messages": scenario.messages, "plaintext_bytes": plaintext_bytes, "wire_bytes": wire_bytes,
		"server_batch_ns": batch_ns, "sum_operation_ns": operation_ns,
		"operations_per_second": scenario.messages as f64 / seconds,
		"plaintext_mib_per_second": plaintext_bytes as f64 / 1_048_576.0 / seconds,
		"latency_ns": { "min": sorted[0], "p50": percentile(&sorted, 50), "p95": percentile(&sorted, 95),
			"p99": percentile(&sorted, 99), "max": sorted[sorted.len()-1], "mean": operation_ns as f64 / sorted.len() as f64 },
		"operation_latencies_ns": latencies, "database": counts,
		"footprint_before": footprint_before, "footprint_after": footprint_after,
		"outputs_verified": true,
	}))
}

fn command(program: &str, args: &[&str]) -> Option<String> {
	Command::new(program)
		.args(args)
		.current_dir(env!("CARGO_MANIFEST_DIR"))
		.output()
		.ok()
		.filter(|output| output.status.success())
		.map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn environment() -> Value {
	json!({
		"unix_time_seconds": SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
		"os": std::env::consts::OS, "arch": std::env::consts::ARCH,
		"available_parallelism": std::thread::available_parallelism().map(|n| n.get()).ok(),
		"sqlite_version": rusqlite::version(),
		"rustc_version_from_path": command("rustc", &["--version"]),
		"git_revision": command("git", &["rev-parse", "HEAD"]),
		"git_status": command("git", &["status", "--short"]),
		"uname": command("uname", &["-a"]),
		"cpuinfo": std::fs::read_to_string("/proc/cpuinfo").ok(),
		"meminfo": std::fs::read_to_string("/proc/meminfo").ok(),
		"process_status": std::fs::read_to_string("/proc/self/status").ok(),
		"debug_assertions": cfg!(debug_assertions),
		"rustflags": std::env::var("RUSTFLAGS").ok(),
		"cpu0_scaling_governor": std::fs::read_to_string("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor").ok(),
		"command_line": std::env::args().collect::<Vec<_>>(),
		"executable": std::env::current_exe().ok(),
	})
}

fn write_report(file: &mut File, report: &Value) -> Result<()> {
	file.rewind()?;
	file.set_len(0)?;
	serde_json::to_writer_pretty(&mut *file, report)?;
	file.write_all(b"\n")?;
	file.flush()?;
	// Finish report writeback before preparing the next measured trial.
	file.sync_all()?;
	Ok(())
}

fn main() -> Result<()> {
	let Some(options) = options()? else {
		return Ok(());
	};
	if cfg!(debug_assertions) {
		return Err("build this benchmark with --release; debug timings are not accepted".into());
	}
	if options.concurrent {
		return concurrency::run(options);
	}
	// Capture source status before generated report/database files can dirty this checkout.
	let source_environment = environment();
	let mut output = OpenOptions::new()
		.create_new(true)
		.write(true)
		.open(&options.output)?;
	let directory = match &options.database_directory {
		Some(path) => tempfile::Builder::new()
			.prefix("beaconcrypt-persistence-bench-")
			.tempdir_in(path)?,
		None => tempfile::Builder::new()
			.prefix("beaconcrypt-persistence-bench-")
			.tempdir_in(std::env::current_dir()?)?,
	};
	let filesystem_type = command(
		"stat",
		&["-f", "-c", "%T", &directory.path().to_string_lossy()],
	);
	if options.config.backend == "sqlite"
		&& matches!(filesystem_type.as_deref(), Some("tmpfs" | "ramfs"))
	{
		return Err("use --database-directory on persistent storage, not tmpfs or ramfs".into());
	}
	let config = options.config;
	let payloads = Payloads {
		small: payload(config.small_bytes, 1),
		large: payload(config.large_bytes, 2),
		chunk: payload(config.burst_chunk_bytes, 3),
	};
	let scenarios = scenarios(&config);
	let mut report = json!({
		"schema_version": 2, "arms": ["snapshot","row","cached_row"], "backend": config.backend, "status": "running", "component": "native durable persistence",
		"mythic_reference_commit": MYTHIC_REFERENCE, "config": config,
		"environment": source_environment, "database_settings": "Actual settings recorded per fixture; SQL and connection preparation outside timing",
		"fixture_workspace": directory.path(),
		"database_directory": (config.backend == "sqlite").then_some(directory.path()),
		"filesystem_type": if config.backend == "sqlite" { filesystem_type } else { None },
		"scope": "Resident native APIs, one worker, no HTTP/AMQP/CGO/JSON-RPC/provider metadata or result journal. No artificial full restore on each snapshot operation.",
		"timing": "Unpaced server batches. Client encryption, registration, verification and checkpoint preparation are outside timing; automatic WAL checkpoints inside batches remain included.",
		"byte_metrics": "Opaque fetched/written value bytes; validation_bytes_sent counts expected values/heads supplied for commit checks. All are logical bytes, not physical disk/network I/O. SQLite snapshot reads a 72-byte head; PostgreSQL uses a conditional update. network_exchanges counts prepared query/ack calls, not packets. SQL calls count explicit client calls, not statements inside the commit function.",
		"memory": "Payloads/frames/results are retained outside and across batches for exact verification; process memory includes this harness and is not a server-memory comparison.",
		"fixtures": [], "results": [],
	});
	write_report(&mut output, &report)?;
	let outcome = (|| -> Result<()> {
		for (peer_index, &peers) in config.peer_counts.iter().enumerate() {
			for trial in 1..=config.trials {
				let mut fixtures = Vec::with_capacity(3);
				let mut arms = [Arm::Snapshot, Arm::Row, Arm::Cached];
				arms.rotate_left((trial - 1 + peer_index) % 3);
				for arm in arms {
					let path = directory.path().join(format!(
						"{}-axis{peer_index}-peers{peers}-trial{trial}.sqlite",
						arm.label()
					));
					let fixture = Fixture::new(arm, path, peers, &config)?;
					report["fixtures"].as_array_mut().unwrap().push(json!({
						"arm": arm.label(), "peers": peers, "trial": trial,
						"lineage": fixture.lineage.as_bytes(),
						"setup_ns": fixture.setup_ns, "warm_database_open_ns": fixture.warm_database_open_ns,
						"cold_open_database":fixture.cold_open_counts,"cache_fill_database":fixture.cache_fill_counts,"warm_database":fixture.warm_counts,
						"cached_peers_at_measurement_start":fixture.server.cached_peers(),"cache_capacity":fixture.server.cached_peers().map(|_|config.active_peers.unwrap_or(peers).min(peers)),
						"database_settings":fixture.location.settings(),
						"warm_open_definition": "Native restore/open after connection setup; OS database cache is warm. Snapshot includes activation commit; row open is read-only.",
						"footprint": fixture.location.footprint(arm)?,
					}));
					fixtures.push(fixture);
				}
				fixtures.sort_by_key(|fixture| fixture.arm.index());
				for (scenario_index, scenario) in scenarios.iter().enumerate() {
					for (direction_index, direction) in [Direction::Send, Direction::Receive]
						.into_iter()
						.enumerate()
					{
						// Rotate three arms: over three trials each arm occupies every position.
						let first = (trial - 1 + peer_index + scenario_index + direction_index) % 3;
						for pair_order in 0..3 {
							let index = (first + pair_order) % 3;
							let result = measure(
								&mut fixtures[index],
								scenario,
								direction,
								&config,
								&payloads,
								trial,
								pair_order,
							)?;
							report["results"].as_array_mut().unwrap().push(result);
						}
						println!(
							"trial={trial} peers={peers} scenario={} direction={} operations_per_arm={}",
							scenario.name,
							direction.label(),
							scenario.messages
						);
					}
				}
				// Reporting between paired arms would bias the following arm with filesystem activity.
				// Save raw results after all arms finish every workload for this fresh trial.
				write_report(&mut output, &report)?;
			}
		}
		Ok(())
	})();
	match outcome {
		Ok(()) => report["status"] = json!("complete"),
		Err(ref error) => {
			report["status"] = json!("failed");
			report["error"] = json!(error.to_string());
		}
	}
	write_report(&mut output, &report)?;
	outcome
}
