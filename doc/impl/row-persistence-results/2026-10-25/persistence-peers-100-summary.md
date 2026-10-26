# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/persistence-peers-100.json`

Input SHA-256: `e6c3c38c58d1facd698553c783956f1bb0b01e56a637f09bd50633986ad5ff4f`

Ratios divide snapshot batch duration by row batch duration. A ratio above 1 means the row batch finished sooner in that paired trial. Latency percentiles remain separate for every trial; no latency samples are pooled.

Storage counters describe logical SQL values and snapshot head reads. They are not physical disk I/O measurements. The benchmark omits the application request/result journal and transport.

## small_stream / send / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 1024; plaintext bytes: 1048576; wire bytes: 1138688.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 8019.980 / 7180.056 | 127.7 / 142.6 | 0.12 / 0.14 | 13301.555 / 17170.644 | 10331.106 / 14245.090 | 1.117 |
| 2 | snapshot | 8005.915 / 6815.346 | 127.9 / 150.2 | 0.12 / 0.15 | 12946.183 / 17065.269 | 9596.709 / 14560.056 | 1.175 |
| 3 | row | 8505.130 / 7935.422 | 120.4 / 129.0 | 0.12 / 0.13 | 13643.861 / 16965.483 | 12092.714 / 16917.724 | 1.072 |

Paired batch ratio: median **1.117**, range 1.072–1.175, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 96193012 | 837630 / 837731 | 73728 |
| 2 | 0 / 96154244 | 837814 / 837884 | 73728 |
| 3 | 0 / 96131761 | 838321 / 838398 | 73728 |

## small_stream / receive / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 1024; plaintext bytes: 1048576; wire bytes: 1139668.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 7403.155 / 6401.101 | 138.3 / 160.0 | 0.14 / 0.16 | 12098.766 / 16153.752 | 8773.527 / 12608.043 | 1.157 |
| 2 | row | 7451.456 / 8199.470 | 137.4 / 124.9 | 0.13 / 0.12 | 11624.484 / 16077.240 | 12031.320 / 15442.729 | 0.909 |
| 3 | snapshot | 7139.211 / 6792.159 | 143.4 / 150.8 | 0.14 / 0.15 | 11622.179 / 14656.957 | 9460.186 / 13684.747 | 1.051 |

Paired batch ratio: median **1.051**, range 0.909–1.157, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 96300442 | 838791 / 838934 | 73728 |
| 2 | 0 / 96300025 | 837663 / 837718 | 73728 |
| 3 | 0 / 96210737 | 838610 / 838711 | 73728 |

## large_stream / send / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 128; plaintext bytes: 8388608; wire bytes: 8400128.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 894.322 / 847.923 | 143.1 / 151.0 | 8.95 / 9.43 | 12221.294 / 13161.093 | 8973.419 / 12372.655 | 1.055 |
| 2 | row | 845.097 / 887.266 | 151.5 / 144.3 | 9.47 / 9.02 | 11290.491 / 12621.008 | 9451.068 / 11457.773 | 0.952 |
| 3 | snapshot | 975.121 / 748.475 | 131.3 / 171.0 | 8.20 / 10.69 | 11397.220 / 16826.664 | 6986.292 / 8172.118 | 1.303 |

Paired batch ratio: median **1.055**, range 0.952–1.303, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 12046986 | 105042 / 105076 | 9216 |
| 2 | 0 / 12042147 | 104834 / 104888 | 9216 |
| 3 | 0 / 12032945 | 104926 / 105007 | 9216 |

## large_stream / receive / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 128; plaintext bytes: 8388608; wire bytes: 8400248.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 865.460 / 865.694 | 147.9 / 147.9 | 9.24 / 9.24 | 11796.192 / 13248.726 | 9108.911 / 16599.222 | 1.000 |
| 2 | snapshot | 845.000 / 782.803 | 151.5 / 163.5 | 9.47 / 10.22 | 11576.704 / 13218.209 | 7903.178 / 10754.584 | 1.079 |
| 3 | row | 864.861 / 751.793 | 148.0 / 170.3 | 9.25 / 10.64 | 10090.318 / 12856.405 | 6877.359 / 10132.817 | 1.150 |

Paired batch ratio: median **1.079**, range 1.000–1.150, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 12043476 | 105092 / 105061 | 9216 |
| 2 | 0 / 12051901 | 104905 / 104866 | 9216 |
| 3 | 0 / 12032098 | 105035 / 105064 | 9216 |

## mixed_stream / send / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 1024; plaintext bytes: 5177344; wire bytes: 5267648.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 7042.836 / 6080.899 | 145.4 / 168.4 | 0.70 / 0.81 | 11509.219 / 15305.964 | 7999.657 / 11141.495 | 1.158 |
| 2 | snapshot | 6695.380 / 6512.341 | 152.9 / 157.2 | 0.74 / 0.76 | 11046.868 / 13331.660 | 8830.373 / 16315.563 | 1.028 |
| 3 | row | 6697.105 / 6208.315 | 152.9 / 164.9 | 0.74 / 0.80 | 10941.873 / 13113.985 | 7983.958 / 10246.208 | 1.079 |

Paired batch ratio: median **1.079**, range 1.028–1.158, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 96363117 | 839438 / 839431 | 73728 |
| 2 | 0 / 96409809 | 838696 / 838734 | 73728 |
| 3 | 0 / 96245475 | 840407 / 840359 | 73728 |

## mixed_stream / receive / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 1024; plaintext bytes: 5177344; wire bytes: 5268604.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 7645.279 / 6681.881 | 133.9 / 153.3 | 0.65 / 0.74 | 12025.139 / 16541.234 | 9005.620 / 13051.198 | 1.144 |
| 2 | row | 7347.890 / 6990.458 | 139.4 / 146.5 | 0.67 / 0.71 | 11802.906 / 14980.960 | 10972.139 / 15635.979 | 1.051 |
| 3 | snapshot | 6897.614 / 6582.943 | 148.5 / 155.6 | 0.72 / 0.75 | 11332.470 / 13262.091 | 8578.194 / 12040.277 | 1.048 |

Paired batch ratio: median **1.051**, range 1.048–1.144, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 96322657 | 840178 / 840259 | 73728 |
| 2 | 0 / 96348379 | 839609 / 839689 | 73728 |
| 3 | 0 / 96283785 | 839988 / 839953 | 73728 |

## burst_64 / send / 100 peers

Eligible/touched peers: 100/64; consumed registrations: 100; messages: 64; plaintext bytes: 32768000; wire bytes: 32773788.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 473.476 / 421.026 | 135.2 / 152.0 | 66.00 / 74.22 | 11714.711 / 13990.907 | 7410.792 / 12336.288 | 1.125 |
| 2 | row | 465.853 / 518.792 | 137.4 / 123.4 | 67.08 / 60.24 | 10700.393 / 12756.159 | 11628.281 / 15967.075 | 0.898 |
| 3 | snapshot | 461.323 / 428.317 | 138.7 / 149.4 | 67.74 / 72.96 | 9933.506 / 12770.736 | 8942.102 / 11988.390 | 1.077 |

Paired batch ratio: median **1.077**, range 0.898–1.125, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 6024645 | 52524 / 52520 | 4608 |
| 2 | 0 / 6019585 | 52540 / 52583 | 4608 |
| 3 | 0 / 6012976 | 52505 / 52494 | 4608 |

## burst_64 / receive / 100 peers

Eligible/touched peers: 100/64; consumed registrations: 100; messages: 64; plaintext bytes: 32768000; wire bytes: 32773844.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 437.115 / 421.247 | 146.4 / 151.9 | 71.49 / 74.18 | 7871.659 / 12802.005 | 8416.874 / 11658.517 | 1.038 |
| 2 | snapshot | 443.907 / 419.891 | 144.2 / 152.4 | 70.40 / 74.42 | 9973.320 / 12937.206 | 7993.236 / 12689.065 | 1.057 |
| 3 | row | 521.460 / 438.689 | 122.7 / 145.9 | 59.93 / 71.23 | 11402.591 / 15891.274 | 9674.545 / 11342.559 | 1.189 |

Paired batch ratio: median **1.057**, range 1.038–1.189, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 6022504 | 52520 / 52463 | 4608 |
| 2 | 0 / 6022366 | 52583 / 52549 | 4608 |
| 3 | 0 / 6015649 | 52494 / 52458 | 4608 |

## burst_256 / send / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 256; plaintext bytes: 131072000; wire bytes: 131095260.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 2015.935 / 1805.234 | 127.0 / 141.8 | 62.01 / 69.24 | 12243.896 / 15180.160 | 9180.985 / 11714.000 | 1.117 |
| 2 | snapshot | 1858.641 / 1991.178 | 137.7 / 128.6 | 67.25 / 62.78 | 10828.251 / 13809.740 | 9692.548 / 14090.873 | 0.933 |
| 3 | row | 1935.031 / 1968.846 | 132.3 / 130.0 | 64.60 / 63.49 | 12801.203 / 20808.865 | 10125.855 / 12801.914 | 0.983 |

Paired batch ratio: median **0.983**, range 0.933–1.117, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 24081274 | 209912 / 209854 | 18432 |
| 2 | 0 / 24099001 | 209956 / 209905 | 18432 |
| 3 | 0 / 24074606 | 209918 / 209919 | 18432 |

## burst_256 / receive / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 256; plaintext bytes: 131072000; wire bytes: 131095432.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 1931.975 / 1838.080 | 132.5 / 139.3 | 64.70 / 68.01 | 12807.354 / 13718.150 | 10289.318 / 15022.497 | 1.051 |
| 2 | row | 2330.701 / 2297.534 | 109.8 / 111.4 | 53.63 / 54.41 | 15846.831 / 19434.217 | 12892.503 / 17532.468 | 1.014 |
| 3 | snapshot | 2025.981 / 2229.511 | 126.4 / 114.8 | 61.70 / 56.07 | 12292.035 / 17242.388 | 12909.514 / 15425.036 | 0.909 |

Paired batch ratio: median **1.014**, range 0.909–1.051, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 24093290 | 209820 / 209849 | 18432 |
| 2 | 0 / 24082691 | 209927 / 209951 | 18432 |
| 3 | 0 / 24080062 | 209876 / 209924 | 18432 |

## burst_512 / send / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 512; plaintext bytes: 262144000; wire bytes: 262190592.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 3722.261 / 3797.611 | 137.6 / 134.8 | 67.16 / 65.83 | 11877.534 / 13745.380 | 9884.655 / 11965.057 | 0.980 |
| 2 | row | 4312.541 / 4596.584 | 118.7 / 111.4 | 57.97 / 54.39 | 13704.804 / 17629.388 | 12895.338 / 16041.253 | 0.938 |
| 3 | snapshot | 4121.789 / 3506.324 | 124.2 / 146.0 | 60.65 / 71.30 | 12803.327 / 16966.565 | 9451.399 / 11824.786 | 1.176 |

Paired batch ratio: median **0.980**, range 0.938–1.176, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 48183037 | 419993 / 419995 | 36864 |
| 2 | 0 / 48193647 | 419787 / 419747 | 36864 |
| 3 | 0 / 48126496 | 420148 / 420118 | 36864 |

## burst_512 / receive / 100 peers

Eligible/touched peers: 100/100; consumed registrations: 100; messages: 512; plaintext bytes: 262144000; wire bytes: 262191080.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 4173.632 / 3497.663 | 122.7 / 146.4 | 59.90 / 71.48 | 13052.030 / 18970.273 | 9125.132 / 12785.534 | 1.193 |
| 2 | snapshot | 3753.417 / 3376.602 | 136.4 / 151.6 | 66.61 / 74.04 | 11682.371 / 14737.517 | 8929.748 / 11363.798 | 1.112 |
| 3 | row | 4691.190 / 4194.329 | 109.1 / 122.1 | 53.29 / 59.60 | 15735.323 / 19013.564 | 11476.718 / 15537.035 | 1.118 |

Paired batch ratio: median **1.118**, range 1.112–1.193, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 48181038 | 419746 / 419656 | 36864 |
| 2 | 0 / 48190933 | 419542 / 419513 | 36864 |
| 3 | 0 / 48115525 | 419724 / 419754 | 36864 |
