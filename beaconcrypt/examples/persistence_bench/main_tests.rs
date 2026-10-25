// SPDX-License-Identifier: 0BSD

use super::*;
use std::{collections::BTreeSet, time::Duration};

fn parse(args: &[&str]) -> Result<Option<Options>> {
	options(args.iter().map(|arg| (*arg).to_owned()))
}

#[test]
fn axis_lists_preserve_distinct_values_and_reject_ambiguous_input() {
	assert_eq!(parse_list("7,2,19").unwrap(), vec![7, 2, 19]);
	assert_eq!(parse_list("0").unwrap(), vec![0]);
	for invalid in ["", "1,", "1,,2", "-1", "x", "1,1", "01,1"] {
		assert!(
			parse_list(invalid).is_err(),
			"accepted invalid list {invalid}"
		);
	}
	assert!(parse_list(&format!("{}0", usize::MAX)).is_err());
}

#[test]
fn cli_requires_explicit_run_and_handles_help_without_running() {
	assert!(parse(&[]).is_err());
	assert!(parse(&["--peers", "1"]).is_err());
	assert!(parse(&["--help"]).unwrap().is_none());
	assert!(parse(&["-h"]).unwrap().is_none());
	assert!(parse(&["--run"]).unwrap().is_some());
	assert!(parse(&["--run", "--unknown", "1"]).is_err());
	assert!(parse(&["--run", "--peers"]).is_err());
	assert!(parse(&["--run", "--mode", "other"]).is_err());
	assert!(parse(&["--run", "--backend", "other"]).is_err());
	// A test-harness invocation never authorizes the benchmark entrypoint.
	assert!(main().is_err());
}

#[test]
fn cli_defaults_and_every_override_reach_the_declared_configuration() {
	let defaults = parse(&["--run"]).unwrap().unwrap();
	assert!(!defaults.concurrent);
	assert_eq!(
		defaults.output,
		PathBuf::from("row-persistence-benchmark.json")
	);
	assert!(defaults.database_directory.is_none());
	assert_eq!(
		serde_json::to_value(defaults.config).unwrap(),
		json!({"backend":"sqlite","peer_counts":[1,100,1000],"trials":3,"extra_registrations":0,"active_peers":null,"small_bytes":1024,"small_messages":1024,"large_bytes":65536,"large_messages":128,"mixed_messages":1024,"large_every":16,"burst_chunk_bytes":512000,"burst_chunks":[64,256,512],"warmup_messages":16})
	);
	assert_eq!(
		serde_json::to_value(defaults.concurrency).unwrap(),
		json!({"workers":8,"period_ms":[1000,100,10,5],"arrival_ms":2000,"queue_capacity":256,"queue_bytes":16777216,"deadline_ms":1000,"drain_ms":600000,"max_offered":20000,"max_precomputed_bytes":536870912})
	);
	let overridden = parse(&[
		"--run",
		"--mode",
		"concurrent",
		"--backend",
		"postgres",
		"--peers",
		"2,7",
		"--trials",
		"2",
		"--extra-registrations",
		"3",
		"--active-peers",
		"2",
		"--small-bytes",
		"13",
		"--small-messages",
		"5",
		"--large-bytes",
		"37",
		"--large-messages",
		"7",
		"--mixed-messages",
		"9",
		"--large-every",
		"3",
		"--burst-chunk-bytes",
		"65",
		"--burst-chunks",
		"2,5",
		"--warmup-messages",
		"0",
		"--output",
		"answer.json",
		"--database-directory",
		"database-place",
		"--workers",
		"3",
		"--period-ms",
		"9,2",
		"--arrival-ms",
		"7",
		"--queue-capacity",
		"5",
		"--queue-bytes",
		"2048",
		"--deadline-ms",
		"6",
		"--drain-ms",
		"5000",
		"--max-offered",
		"12",
		"--max-precomputed-bytes",
		"65536",
	])
	.unwrap()
	.unwrap();
	assert!(overridden.concurrent);
	assert_eq!(overridden.output, PathBuf::from("answer.json"));
	assert_eq!(
		overridden.database_directory,
		Some(PathBuf::from("database-place"))
	);
	assert_eq!(
		serde_json::to_value(overridden.config).unwrap(),
		json!({"backend":"postgres","peer_counts":[2,7],"trials":2,"extra_registrations":3,"active_peers":2,"small_bytes":13,"small_messages":5,"large_bytes":37,"large_messages":7,"mixed_messages":9,"large_every":3,"burst_chunk_bytes":65,"burst_chunks":[2,5],"warmup_messages":0})
	);
	assert_eq!(
		serde_json::to_value(overridden.concurrency).unwrap(),
		json!({"workers":3,"period_ms":[9,2],"arrival_ms":7,"queue_capacity":5,"queue_bytes":2048,"deadline_ms":6,"drain_ms":5000,"max_offered":12,"max_precomputed_bytes":65536})
	);
	assert!(
		!parse(&["--run", "--mode", "serial"])
			.unwrap()
			.unwrap()
			.concurrent
	);
}

#[test]
fn cli_enforces_message_and_axis_boundaries_before_fixture_allocation() {
	for flag in [
		"--trials",
		"--peers",
		"--active-peers",
		"--large-every",
		"--burst-chunks",
		"--small-messages",
		"--large-messages",
		"--mixed-messages",
	] {
		assert!(parse(&["--run", flag, "0"]).is_err(), "accepted {flag}=0");
		assert!(
			parse(&["--run", flag, "1"]).unwrap().is_some(),
			"rejected {flag}=1"
		);
	}
	for flag in ["--peers", "--period-ms", "--burst-chunks"] {
		assert!(parse(&["--run", flag, "1,1"]).is_err());
		assert!(parse(&["--run", flag, ""]).is_err());
	}
	let largest = (beaconcrypt::MAX_MESSAGE_SIZE - 128).to_string();
	let too_large = (beaconcrypt::MAX_MESSAGE_SIZE - 127).to_string();
	for flag in ["--small-bytes", "--large-bytes", "--burst-chunk-bytes"] {
		assert!(parse(&["--run", flag, "0"]).is_err());
		assert!(parse(&["--run", flag, "1"]).unwrap().is_some());
		assert!(parse(&["--run", flag, &largest]).unwrap().is_some());
		assert!(parse(&["--run", flag, &too_large]).is_err());
	}
	for flag in [
		"--workers",
		"--arrival-ms",
		"--queue-capacity",
		"--queue-bytes",
		"--deadline-ms",
		"--drain-ms",
		"--max-offered",
		"--max-precomputed-bytes",
		"--extra-registrations",
		"--warmup-messages",
	] {
		assert!(parse(&["--run", flag, "not-a-number"]).is_err());
	}
}

#[test]
fn payload_generator_has_stable_bytes_and_exact_partial_block_lengths() {
	// Fixed SplitMix64 seed-zero vector, serialized little-endian as this fixture specifies.
	let expected = [
		0xaf, 0xcd, 0x1d, 0x7b, 0x39, 0xa8, 0x20, 0xe2, 0xf4, 0x65, 0xb9, 0xa1, 0x6a, 0x9e, 0x78,
		0x6e, 0x4f,
	];
	for length in [0, 1, 7, 8, 9, 16, 17] {
		assert_eq!(payload(length, 0), expected[..length]);
	}
	assert_eq!(
		payload(8, 1),
		vec![0xc1, 0x5c, 0x02, 0x89, 0xec, 0x2d, 0x0a, 0x91]
	);
	assert_ne!(payload(31, 1), payload(31, 2));
}

#[test]
fn percentile_uses_nearest_rank_and_duration_conversion_retains_units() {
	let ordered = (1..=20).map(|n| n * 10).collect::<Vec<u64>>();
	for (percentage, expected) in [
		(1, 10),
		(5, 10),
		(6, 20),
		(50, 100),
		(95, 190),
		(99, 200),
		(100, 200),
	] {
		assert_eq!(percentile(&ordered, percentage), expected);
	}
	assert_eq!(percentile(&[42], 95), 42);
	assert_eq!(nanos(Duration::ZERO), 0);
	assert_eq!(nanos(Duration::new(2, 17)), 2_000_000_017);
}

#[test]
fn scenarios_select_the_actual_payload_and_count_at_mixed_boundaries() {
	let config = Config {
		small_messages: 3,
		large_messages: 2,
		mixed_messages: 7,
		large_every: 3,
		burst_chunks: vec![1, 4],
		..Default::default()
	};
	let payloads = Payloads {
		small: vec![1; 13],
		large: vec![2; 37],
		chunk: vec![3; 65],
	};
	let cases = scenarios(&config);
	assert_eq!(
		cases
			.iter()
			.map(|case| (case.name.as_str(), case.messages))
			.collect::<Vec<_>>(),
		vec![
			("small_stream", 3),
			("large_stream", 2),
			("mixed_stream", 7),
			("burst_1", 1),
			("burst_4", 4)
		]
	);
	assert_eq!(cases[0].bytes(0, &config, &payloads), payloads.small);
	assert_eq!(cases[1].bytes(0, &config, &payloads), payloads.large);
	for (index, length) in [
		(0, 13),
		(1, 13),
		(2, 37),
		(3, 13),
		(4, 13),
		(5, 37),
		(6, 13),
	] {
		assert_eq!(cases[2].bytes(index, &config, &payloads).len(), length);
	}
	assert_eq!(cases[3].bytes(0, &config, &payloads), payloads.chunk);
	assert_eq!(cases[4].bytes(3, &config, &payloads), payloads.chunk);
}

#[test]
fn provenance_commands_trim_success_and_do_not_invent_failed_output() {
	assert_eq!(
		command("sh", &["-c", "printf '  recorded value  \\n'"]),
		Some("recorded value".into())
	);
	assert!(command("sh", &["-c", "printf ignored; exit 1"]).is_none());
	assert!(command("beaconcrypt-benchmark-command-does-not-exist", &[]).is_none());
	let value = environment();
	assert_eq!(value["os"], std::env::consts::OS);
	assert_eq!(value["arch"], std::env::consts::ARCH);
	assert_eq!(value["debug_assertions"], cfg!(debug_assertions));
	assert!(value["unix_time_seconds"].as_u64().unwrap() > 0);
	assert_eq!(value["sqlite_version"], rusqlite::version());
	assert!(value["executable"].as_str().is_some());
}

#[test]
fn report_checkpoints_replace_longer_prior_contents_and_leave_valid_json() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("report.json");
	let mut file = OpenOptions::new()
		.create_new(true)
		.write(true)
		.open(&path)
		.unwrap();
	write_report(
		&mut file,
		&json!({"status":"running","extra":"x".repeat(2048)}),
	)
	.unwrap();
	let final_value = json!({"status":"complete","verified":true});
	write_report(&mut file, &final_value).unwrap();
	let bytes = std::fs::read(&path).unwrap();
	assert_eq!(
		serde_json::from_slice::<Value>(&bytes).unwrap(),
		final_value
	);
	assert_eq!(bytes.last(), Some(&b'\n'));
	assert!(bytes.len() < 100);
}

fn small_options(directory: &std::path::Path, backend: &str) -> Options {
	Options {
		config: Config {
			backend: backend.into(),
			peer_counts: vec![1, 2],
			trials: 3,
			extra_registrations: 1,
			active_peers: Some(1),
			small_bytes: 13,
			small_messages: 3,
			large_bytes: 37,
			large_messages: 2,
			mixed_messages: 5,
			large_every: 2,
			burst_chunk_bytes: 65,
			burst_chunks: vec![1, 4],
			warmup_messages: 2,
		},
		concurrent: false,
		concurrency: concurrency::Config::default(),
		output: directory.join("full-report.json"),
		database_directory: Some(directory.to_owned()),
	}
}

fn validate_serial_report(path: &std::path::Path, backend: &str) {
	let report: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
	assert_eq!(report["status"], "complete");
	assert_eq!(report["schema_version"], 2);
	assert_eq!(report["backend"], backend);
	assert_eq!(report["mythic_reference_commit"], MYTHIC_REFERENCE);
	assert_eq!(report["fixtures"].as_array().unwrap().len(), 18);
	let mut lineages = BTreeSet::new();
	for fixture in report["fixtures"].as_array().unwrap() {
		assert!(lineages.insert(fixture["lineage"].to_string()));
		assert_eq!(fixture["lineage"].as_array().unwrap().len(), 32);
		let peers = fixture["peers"].as_u64().unwrap();
		let arm = fixture["arm"].as_str().unwrap();
		assert_eq!(fixture["cache_fill_database"]["transactions"], 2);
		assert_eq!(fixture["warm_database"]["transactions"], 4);
		assert_eq!(
			fixture["footprint"]["rows"],
			if arm == "snapshot" {
				1
			} else {
				2 + 2 * peers + 1
			}
		);
		if arm == "cached_row" {
			assert_eq!(fixture["cached_peers_at_measurement_start"], 1);
			assert_eq!(fixture["cache_capacity"], 1);
		}
		assert!(fixture["warm_database_open_ns"].as_u64().unwrap() > 0);
		if backend == "sqlite" {
			assert!(fixture["footprint"]["main_file_bytes"].as_u64().unwrap() > 0);
		}
	}
	let results = report["results"].as_array().unwrap();
	assert_eq!(results.len(), 180);
	let mut keys = BTreeSet::new();
	for result in results {
		assert_eq!(result["outputs_verified"], true);
		let messages = result["messages"].as_u64().unwrap();
		let arm = result["arm"].as_str().unwrap();
		assert!(keys.insert((
			result["peers"].as_u64().unwrap(),
			result["trial"].as_u64().unwrap(),
			result["scenario"].as_str().unwrap(),
			result["direction"].as_str().unwrap(),
			arm
		)));
		assert_eq!(result["active_peers"], 1);
		assert_eq!(result["touched_peers"], 1);
		assert_eq!(
			result["consumed_registrations"].as_u64().unwrap(),
			result["peers"].as_u64().unwrap() + 1
		);
		assert_eq!(
			result["operation_latencies_ns"].as_array().unwrap().len() as u64,
			messages
		);
		assert!(result["server_batch_ns"].as_u64().unwrap() > 0);
		assert!(
			result["wire_bytes"].as_u64().unwrap() > result["plaintext_bytes"].as_u64().unwrap()
		);
		assert_eq!(result["database"]["writes"], messages);
		assert_eq!(result["database"]["transactions"], messages);
		assert_eq!(
			result["database"]["network_exchanges"],
			if backend == "postgres" {
				messages * if arm == "row" { 2 } else { 1 }
			} else {
				0
			}
		);
		if arm == "cached_row" {
			assert_eq!(result["database"]["loads"], 0);
			assert_eq!(result["database"]["expects"], messages);
		} else if arm == "row" {
			assert_eq!(result["database"]["loads"], messages);
			assert_eq!(result["database"]["expects"], 0);
		}
	}
	assert!(
		!std::path::Path::new(report["fixture_workspace"].as_str().unwrap()).exists(),
		"temporary database fixtures must be cleaned after completion"
	);
	// Independently recompute matrix, ratios, percentiles and byte totals through the Python validator.
	let checked = Command::new("python3")
		.arg(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/examples/persistence_bench/summarize.py"
		))
		.arg(path)
		.args(["--format", "json"])
		.output()
		.unwrap();
	assert!(
		checked.status.success(),
		"{}",
		String::from_utf8_lossy(&checked.stderr)
	);
	let summary: Value = serde_json::from_slice(&checked.stdout).unwrap();
	assert_eq!(summary["groups"].as_array().unwrap().len(), 20);
}

#[test]
fn serial_full_report_smoke_checks_all_arms_directions_axes_and_orders() {
	let directory = tempfile::tempdir().unwrap();
	let opts = small_options(directory.path(), "sqlite");
	let path = opts.output.clone();
	dispatch(opts, false).unwrap();
	validate_serial_report(&path, "sqlite");
	let before = std::fs::read(&path).unwrap();
	assert!(dispatch(small_options(directory.path(), "sqlite"), false).is_err());
	assert_eq!(std::fs::read(path).unwrap(), before);
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn postgres_serial_full_report_smoke_checks_all_arms_directions_axes_and_orders() {
	let directory = tempfile::tempdir().unwrap();
	let opts = small_options(directory.path(), "postgres");
	let path = opts.output.clone();
	dispatch(opts, false).unwrap();
	validate_serial_report(&path, "postgres");
}

#[test]
fn dispatcher_rejects_debug_measurements_without_creating_a_report() {
	let directory = tempfile::tempdir().unwrap();
	let opts = small_options(directory.path(), "sqlite");
	let path = opts.output.clone();
	assert!(dispatch(opts, true).is_err());
	assert!(!path.exists());
}

#[test]
fn dispatcher_runs_the_concurrent_mode_and_exports_a_valid_complete_matrix() {
	let directory = tempfile::tempdir().unwrap();
	let mut opts = small_options(directory.path(), "sqlite");
	let path = opts.output.clone();
	opts.concurrent = true;
	opts.config.peer_counts = vec![2];
	opts.config.trials = 1;
	opts.config.extra_registrations = 0;
	opts.config.active_peers = Some(2);
	opts.config.warmup_messages = 0;
	opts.config.burst_chunks = vec![4];
	opts.concurrency = concurrency::Config {
		workers: 2,
		period_ms: vec![1],
		arrival_ms: 2,
		queue_capacity: 2,
		queue_bytes: 256,
		deadline_ms: 1000,
		drain_ms: 10_000,
		max_offered: 16,
		max_precomputed_bytes: 1024 * 1024,
	};
	dispatch(opts, false).unwrap();
	let report: Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
	assert_eq!(report["schema_version"], 3);
	assert_eq!(report["status"], "complete");
	assert_eq!(report["results"].as_array().unwrap().len(), 15);
	assert!(
		report["results"]
			.as_array()
			.unwrap()
			.iter()
			.all(|result| result["outputs_verified"] == true && result["failures"] == json!([]))
	);
	let checked = Command::new("python3")
		.arg(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/examples/persistence_bench/summarize.py"
		))
		.arg(&path)
		.args(["--format", "json"])
		.output()
		.unwrap();
	assert!(
		checked.status.success(),
		"{}",
		String::from_utf8_lossy(&checked.stderr)
	);
	let summary: Value = serde_json::from_slice(&checked.stdout).unwrap();
	assert_eq!(summary["groups"].as_array().unwrap().len(), 5);
}

#[test]
fn serial_native_rejection_records_failed_status_instead_of_a_complete_report() {
	let directory = tempfile::tempdir().unwrap();
	let mut opts = small_options(directory.path(), "sqlite");
	let path = opts.output.clone();
	opts.config.peer_counts = vec![1];
	opts.config.trials = 1;
	opts.config.small_bytes = 0;
	assert!(run_serial(opts).is_err());
	let report: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
	assert_eq!(report["status"], "failed");
	assert!(report["error"].as_str().unwrap().contains("rejected"));
}
