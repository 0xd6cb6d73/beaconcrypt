# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/persistence-reduced.json`

Input SHA-256: `aed3531acd1498221afc50b8b90df354d287b19d3812f18a4d33d588e40011d7`

Ratios divide snapshot batch duration by row batch duration. A ratio above 1 means the row batch finished sooner in that paired trial. Latency percentiles remain separate for every trial; no latency samples are pooled.

Storage counters describe logical SQL values and snapshot head reads. They are not physical disk I/O measurements. The benchmark omits the application request/result journal and transport.

## small_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 32; plaintext bytes: 32768; wire bytes: 35598.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 185.489 / 186.950 | 172.5 / 171.2 | 0.17 / 0.17 | 7026.587 / 12532.884 | 7843.036 / 10926.454 | 0.992 |
| 2 | snapshot | 189.031 / 192.517 | 169.3 / 166.2 | 0.17 / 0.16 | 6812.628 / 14781.899 | 10100.777 / 10906.948 | 0.982 |

Paired batch ratio: median **0.987**, range 0.982–0.992, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 43523 | 25862 / 25855 | 2304 |
| 2 | 0 / 43434 | 26362 / 26361 | 2304 |

## small_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 32; plaintext bytes: 32768; wire bytes: 35597.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 181.554 / 192.584 | 176.3 / 166.2 | 0.17 / 0.16 | 6472.084 / 10767.628 | 10001.473 / 10770.604 | 0.943 |
| 2 | row | 210.742 / 202.483 | 151.8 / 158.0 | 0.15 / 0.15 | 11421.675 / 11907.910 | 8958.362 / 11176.379 | 1.041 |

Paired batch ratio: median **0.992**, range 0.943–1.041, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 43587 | 25866 / 25863 | 2304 |
| 2 | 0 / 43611 | 26361 / 26368 | 2304 |

## large_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 8; plaintext bytes: 524288; wire bytes: 525016.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 48.972 / 51.837 | 163.4 / 154.3 | 10.21 / 9.65 | 10843.850 / 10843.850 | 12235.521 / 12235.521 | 0.945 |
| 2 | row | 70.033 / 77.516 | 114.2 / 103.2 | 7.14 / 6.45 | 15647.050 / 15647.050 | 16669.352 / 16669.352 | 0.903 |

Paired batch ratio: median **0.924**, range 0.903–0.945, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 10923 | 6441 / 6442 | 576 |
| 2 | 0 / 10853 | 6665 / 6671 | 576 |

## large_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 8; plaintext bytes: 524288; wire bytes: 525016.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 48.942 / 50.157 | 163.5 / 159.5 | 10.22 / 9.97 | 10928.528 / 10928.528 | 10763.080 / 10763.080 | 0.976 |
| 2 | snapshot | 60.252 / 68.614 | 132.8 / 116.6 | 8.30 / 7.29 | 14105.340 / 14105.340 | 14118.234 / 14118.234 | 0.878 |

Paired batch ratio: median **0.927**, range 0.878–0.976, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 10945 | 6479 / 6480 | 576 |
| 2 | 0 / 10861 | 6647 / 6641 | 576 |

## mixed_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 32; plaintext bytes: 161792; wire bytes: 164644.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 181.450 / 198.169 | 176.4 / 161.5 | 0.85 / 0.78 | 6342.834 / 10952.362 | 11134.251 / 13888.957 | 0.916 |
| 2 | snapshot | 241.543 / 231.716 | 132.5 / 138.1 | 0.64 / 0.67 | 11489.162 / 16624.168 | 11612.221 / 13711.076 | 1.042 |

Paired batch ratio: median **0.979**, range 0.916–1.042, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 43576 | 25837 / 25840 | 2304 |
| 2 | 0 / 43357 | 26408 / 26408 | 2304 |

## mixed_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 32; plaintext bytes: 161792; wire bytes: 164644.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 185.374 / 181.729 | 172.6 / 176.1 | 0.83 / 0.85 | 6352.793 / 11368.356 | 6576.819 / 10949.557 | 1.020 |
| 2 | row | 193.703 / 228.384 | 165.2 / 140.1 | 0.80 / 0.68 | 7604.732 / 14069.654 | 8836.635 / 13535.981 | 0.848 |

Paired batch ratio: median **0.934**, range 0.848–1.020, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 43611 | 26013 / 26011 | 2304 |
| 2 | 0 / 43288 | 26587 / 26585 | 2304 |

## burst_4 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 4; plaintext bytes: 2048000; wire bytes: 2048364.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 34.481 / 31.114 | 116.0 / 128.6 | 56.64 / 62.77 | 11792.005 / 11792.005 | 11642.246 / 11642.246 | 1.108 |
| 2 | row | 31.759 / 32.289 | 126.0 / 123.9 | 61.50 / 60.49 | 12975.928 / 12975.928 | 12489.493 / 12489.493 | 0.984 |

Paired batch ratio: median **1.046**, range 0.984–1.108, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 5459 | 3225 / 3227 | 288 |
| 2 | 0 / 5426 | 3292 / 3288 | 288 |

## burst_4 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 4; plaintext bytes: 2048000; wire bytes: 2048364.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 30.756 / 29.055 | 130.1 / 137.7 | 63.50 / 67.22 | 12162.183 / 12162.183 | 11271.767 / 11271.767 | 1.059 |
| 2 | snapshot | 31.637 / 29.815 | 126.4 / 134.2 | 61.74 / 65.51 | 11333.392 / 11333.392 | 11557.810 / 11557.810 | 1.061 |

Paired batch ratio: median **1.060**, range 1.059–1.061, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 5428 | 3247 / 3257 | 288 |
| 2 | 0 / 5409 | 3304 / 3305 | 288 |

## small_stream / send / 10 peers

Eligible/touched peers: 10/10; consumed registrations: 10; messages: 32; plaintext bytes: 32768; wire bytes: 35584.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 197.840 / 187.799 | 161.7 / 170.4 | 0.16 / 0.17 | 10770.704 / 11308.526 | 6763.407 / 11379.477 | 1.053 |
| 2 | row | 191.944 / 188.860 | 166.7 / 169.4 | 0.16 / 0.17 | 7091.888 / 11603.143 | 6419.456 / 11154.990 | 1.016 |

Paired batch ratio: median **1.035**, range 1.016–1.053, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 311417 | 26117 / 26116 | 2304 |
| 2 | 0 / 312183 | 26143 / 26141 | 2304 |

## small_stream / receive / 10 peers

Eligible/touched peers: 10/10; consumed registrations: 10; messages: 32; plaintext bytes: 32768; wire bytes: 35602.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 193.535 / 187.832 | 165.3 / 170.4 | 0.16 / 0.17 | 9808.905 / 11171.360 | 6671.917 / 11399.654 | 1.030 |
| 2 | snapshot | 191.204 / 199.776 | 167.4 / 160.2 | 0.16 / 0.16 | 7341.272 / 10873.346 | 10473.221 / 11376.702 | 0.957 |

Paired batch ratio: median **0.994**, range 0.957–1.030, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 312001 | 26128 / 26124 | 2304 |
| 2 | 0 / 312019 | 26136 / 26137 | 2304 |

## large_stream / send / 10 peers

Eligible/touched peers: 10/8; consumed registrations: 10; messages: 8; plaintext bytes: 524288; wire bytes: 525008.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 52.496 / 50.327 | 152.4 / 159.0 | 9.52 / 9.94 | 11384.727 / 11384.727 | 11128.069 / 11128.069 | 1.043 |
| 2 | snapshot | 52.463 / 55.075 | 152.5 / 145.3 | 9.53 / 9.08 | 11703.750 / 11703.750 | 11167.493 / 11167.493 | 0.953 |

Paired batch ratio: median **0.998**, range 0.953–1.043, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 78065 | 6532 / 6547 | 576 |
| 2 | 0 / 78082 | 6544 / 6547 | 576 |

## large_stream / receive / 10 peers

Eligible/touched peers: 10/8; consumed registrations: 10; messages: 8; plaintext bytes: 524288; wire bytes: 525012.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 51.762 / 52.001 | 154.6 / 153.8 | 9.66 / 9.62 | 11681.809 / 11681.809 | 11045.586 / 11045.586 | 0.995 |
| 2 | row | 52.314 / 51.555 | 152.9 / 155.2 | 9.56 / 9.70 | 11446.602 / 11446.602 | 11544.945 / 11544.945 | 1.015 |

Paired batch ratio: median **1.005**, range 0.995–1.015, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 77950 | 6547 / 6544 | 576 |
| 2 | 0 / 78007 | 6547 / 6546 | 576 |

## mixed_stream / send / 10 peers

Eligible/touched peers: 10/10; consumed registrations: 10; messages: 32; plaintext bytes: 161792; wire bytes: 164612.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 209.414 / 209.451 | 152.8 / 152.8 | 0.74 / 0.74 | 9613.721 / 11273.470 | 10737.122 / 10983.019 | 1.000 |
| 2 | row | 202.130 / 194.596 | 158.3 / 164.4 | 0.76 / 0.79 | 11175.287 / 14761.792 | 8404.741 / 14071.357 | 1.039 |

Paired batch ratio: median **1.019**, range 1.000–1.039, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 311458 | 26151 / 26146 | 2304 |
| 2 | 0 / 311712 | 26131 / 26124 | 2304 |

## mixed_stream / receive / 10 peers

Eligible/touched peers: 10/10; consumed registrations: 10; messages: 32; plaintext bytes: 161792; wire bytes: 164630.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 190.914 / 203.735 | 167.6 / 157.1 | 0.81 / 0.76 | 6919.137 / 11373.126 | 8709.077 / 11463.033 | 0.937 |
| 2 | snapshot | 191.125 / 205.293 | 167.4 / 155.9 | 0.81 / 0.75 | 7444.164 / 11332.049 | 9467.439 / 12068.129 | 0.931 |

Paired batch ratio: median **0.934**, range 0.931–0.937, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 311801 | 26157 / 26171 | 2304 |
| 2 | 0 / 312256 | 26150 / 26163 | 2304 |

## burst_4 / send / 10 peers

Eligible/touched peers: 10/4; consumed registrations: 10; messages: 4; plaintext bytes: 2048000; wire bytes: 2048360.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 35.175 / 31.167 | 113.7 / 128.3 | 55.53 / 62.67 | 14210.366 / 14210.366 | 12205.033 / 12205.033 | 1.129 |
| 2 | snapshot | 32.236 / 32.337 | 124.1 / 123.7 | 60.59 / 60.40 | 11759.214 / 11759.214 | 11868.979 / 11868.979 | 0.997 |

Paired batch ratio: median **1.063**, range 0.997–1.129, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 39048 | 3267 / 3268 | 288 |
| 2 | 0 / 39078 | 3274 / 3268 | 288 |

## burst_4 / receive / 10 peers

Eligible/touched peers: 10/4; consumed registrations: 10; messages: 4; plaintext bytes: 2048000; wire bytes: 2048360.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 33.403 / 31.684 | 119.7 / 126.2 | 58.47 / 61.64 | 13159.200 / 13159.200 | 12308.276 / 12308.276 | 1.054 |
| 2 | row | 30.614 / 30.886 | 130.7 / 129.5 | 63.80 / 63.24 | 11661.131 / 11661.131 | 11327.881 / 11327.881 | 0.991 |

Paired batch ratio: median **1.023**, range 0.991–1.054, 2 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 39040 | 3268 / 3274 | 288 |
| 2 | 0 / 39071 | 3268 / 3274 | 288 |
