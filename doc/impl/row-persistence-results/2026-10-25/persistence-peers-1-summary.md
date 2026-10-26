# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/persistence-peers-1.json`

Input SHA-256: `b3ead15ab9d157594ff66f15d9dd7a794461862afad181dd28f2aef49e679cf2`

Ratios divide snapshot batch duration by row batch duration. A ratio above 1 means the row batch finished sooner in that paired trial. Latency percentiles remain separate for every trial; no latency samples are pooled.

Storage counters describe logical SQL values and snapshot head reads. They are not physical disk I/O measurements. The benchmark omits the application request/result journal and transport.

## small_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140492.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 6029.522 / 6265.088 | 169.8 / 163.4 | 0.17 / 0.16 | 7301.829 / 10017.062 | 8202.876 / 11665.980 | 0.962 |
| 2 | snapshot | 6112.551 / 6252.011 | 167.5 / 163.8 | 0.16 / 0.16 | 8073.785 / 10471.778 | 8405.532 / 11403.411 | 0.978 |
| 3 | row | 6514.448 / 6385.793 | 157.2 / 160.4 | 0.15 / 0.16 | 9051.605 / 15175.020 | 8608.451 / 12242.884 | 1.020 |

Paired batch ratio: median **0.978**, range 0.962–1.020, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 1372323 | 853173 / 853176 | 73728 |
| 2 | 0 / 1383757 | 846110 / 846116 | 73728 |
| 3 | 0 / 1386709 | 836071 / 836076 | 73728 |

## small_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140490.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 7136.970 / 6440.787 | 143.5 / 159.0 | 0.14 / 0.16 | 10176.578 / 13486.118 | 8404.320 / 11739.047 | 1.108 |
| 2 | row | 6061.633 / 6333.197 | 168.9 / 161.7 | 0.16 / 0.16 | 7268.177 / 10288.286 | 8518.753 / 10821.909 | 0.957 |
| 3 | snapshot | 6175.485 / 6921.999 | 165.8 / 147.9 | 0.16 / 0.14 | 8026.568 / 10654.668 | 9551.947 / 12725.292 | 0.892 |

Paired batch ratio: median **0.957**, range 0.892–1.108, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 1374554 | 852271 / 852268 | 73728 |
| 2 | 0 / 1384639 | 849166 / 849166 | 73728 |
| 3 | 0 / 1386723 | 836822 / 836819 | 73728 |

## large_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 809.038 / 762.817 | 158.2 / 167.8 | 9.89 / 10.49 | 8798.524 / 11500.092 | 7195.902 / 9318.852 | 1.061 |
| 2 | row | 817.902 / 757.421 | 156.5 / 169.0 | 9.78 / 10.56 | 7939.575 / 8763.749 | 6899.369 / 9793.836 | 1.080 |
| 3 | snapshot | 1108.049 / 1223.891 | 115.5 / 104.6 | 7.22 / 6.54 | 13696.620 / 14693.114 | 15901.994 / 17860.739 | 0.905 |

Paired batch ratio: median **1.061**, range 0.905–1.080, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 171773 | 106406 / 106397 | 9216 |
| 2 | 0 / 173473 | 105906 / 105908 | 9216 |
| 3 | 0 / 174618 | 104243 / 104238 | 9216 |

## large_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 844.995 / 822.134 | 151.5 / 155.7 | 9.47 / 9.73 | 10673.774 / 13069.993 | 8168.542 / 11198.150 | 1.028 |
| 2 | snapshot | 816.258 / 883.887 | 156.8 / 144.8 | 9.80 / 9.05 | 10720.551 / 13635.826 | 10638.999 / 11548.251 | 0.923 |
| 3 | row | 766.398 / 797.940 | 167.0 / 160.4 | 10.44 / 10.03 | 7041.244 / 12286.596 | 8716.592 / 11002.907 | 0.960 |

Paired batch ratio: median **0.960**, range 0.923–1.028, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 172569 | 105559 / 105554 | 9216 |
| 2 | 0 / 172600 | 106495 / 106500 | 9216 |
| 3 | 0 / 173876 | 104091 / 104095 | 9216 |

## mixed_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 6091.396 / 6417.631 | 168.1 / 159.6 | 0.81 / 0.77 | 7663.511 / 10637.216 | 9133.387 / 14108.576 | 0.949 |
| 2 | snapshot | 6627.146 / 6982.831 | 154.5 / 146.6 | 0.75 / 0.71 | 8746.647 / 11637.297 | 9550.193 / 13626.720 | 0.949 |
| 3 | row | 7151.891 / 6777.966 | 143.2 / 151.1 | 0.69 / 0.73 | 10116.056 / 14826.542 | 9510.138 / 13298.649 | 1.055 |

Paired batch ratio: median **0.949**, range 0.949–1.055, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 1373380 | 846071 / 846080 | 73728 |
| 2 | 0 / 1380563 | 852241 / 852238 | 73728 |
| 3 | 0 / 1390881 | 837852 / 837849 | 73728 |

## mixed_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 6046.618 / 6537.614 | 169.4 / 156.6 | 0.82 / 0.76 | 7235.706 / 10178.142 | 9135.681 / 12287.808 | 0.925 |
| 2 | row | 6380.831 / 6601.512 | 160.5 / 155.1 | 0.77 / 0.75 | 8953.863 / 11713.549 | 9099.003 / 12786.967 | 0.967 |
| 3 | snapshot | 7333.375 / 6016.351 | 139.6 / 170.2 | 0.67 / 0.82 | 10485.283 / 15207.311 | 7280.179 / 10554.572 | 1.219 |

Paired batch ratio: median **0.967**, range 0.925–1.219, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 1377541 | 853239 / 853246 | 73728 |
| 2 | 0 / 1384696 | 849151 / 849149 | 73728 |
| 3 | 0 / 1393065 | 829830 / 829825 | 73728 |

## burst_64 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 518.046 / 498.501 | 123.5 / 128.4 | 60.32 / 62.69 | 12534.146 / 13655.993 | 9670.988 / 14388.337 | 1.039 |
| 2 | row | 457.875 / 453.326 | 139.8 / 141.2 | 68.25 / 68.93 | 9030.886 / 11970.658 | 9572.254 / 15015.023 | 1.010 |
| 3 | snapshot | 422.078 / 438.871 | 151.6 / 145.8 | 74.04 / 71.21 | 7730.927 / 11563.219 | 8522.641 / 12756.280 | 0.962 |

Paired batch ratio: median **1.010**, range 0.962–1.039, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 86157 | 53301 / 53303 | 4608 |
| 2 | 0 / 86749 | 53178 / 53177 | 4608 |
| 3 | 0 / 87633 | 52045 / 52053 | 4608 |

## burst_64 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 470.878 / 486.656 | 135.9 / 131.5 | 66.37 / 64.21 | 10712.406 / 13170.401 | 9410.834 / 14050.678 | 0.968 |
| 2 | snapshot | 451.225 / 456.979 | 141.8 / 140.1 | 69.26 / 68.38 | 9319.954 / 16496.419 | 10202.747 / 14080.905 | 0.987 |
| 3 | row | 429.474 / 451.232 | 149.0 / 141.8 | 72.76 / 69.25 | 8912.296 / 13478.935 | 9945.749 / 14138.972 | 0.952 |

Paired batch ratio: median **0.968**, range 0.952–0.987, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 86026 | 53469 / 53470 | 4608 |
| 2 | 0 / 86171 | 53009 / 53001 | 4608 |
| 3 | 0 / 86884 | 52359 / 52367 | 4608 |

## burst_256 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 1691.948 / 1801.699 | 151.3 / 142.1 | 73.88 / 69.38 | 8599.985 / 10627.829 | 9938.185 / 12046.839 | 0.939 |
| 2 | snapshot | 1786.982 / 1694.433 | 143.3 / 151.1 | 69.95 / 73.77 | 9274.029 / 10526.600 | 7530.174 / 11970.377 | 1.055 |
| 3 | row | 1698.505 / 1698.483 | 150.7 / 150.7 | 73.59 / 73.60 | 8057.024 / 10373.916 | 8125.482 / 11152.926 | 1.000 |

Paired batch ratio: median **1.000**, range 0.939–1.055, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 343364 | 213586 / 213587 | 18432 |
| 2 | 0 / 346429 | 210533 / 210528 | 18432 |
| 3 | 0 / 347137 | 210212 / 210215 | 18432 |

## burst_256 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 1805.255 / 1846.742 | 141.8 / 138.6 | 69.24 / 67.69 | 10895.366 / 11593.205 | 11338.150 / 12552.090 | 0.978 |
| 2 | row | 1656.129 / 1718.890 | 154.6 / 148.9 | 75.48 / 72.72 | 7922.324 / 11130.274 | 9247.390 / 11380.699 | 0.963 |
| 3 | snapshot | 1714.386 / 1684.126 | 149.3 / 152.0 | 72.91 / 74.22 | 8503.134 / 10261.226 | 9280.421 / 14020.622 | 1.018 |

Paired batch ratio: median **0.978**, range 0.963–1.018, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 344160 | 214121 / 214118 | 18432 |
| 2 | 0 / 346431 | 210699 / 210711 | 18432 |
| 3 | 0 / 347127 | 210209 / 210204 | 18432 |

## burst_512 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 3741.984 / 3430.093 | 136.8 / 149.3 | 66.81 / 72.88 | 10723.116 / 12651.675 | 8388.582 / 11385.218 | 1.091 |
| 2 | row | 3372.764 / 3447.121 | 151.8 / 148.5 | 74.12 / 72.52 | 8119.230 / 10148.767 | 8548.379 / 10918.168 | 0.978 |
| 3 | snapshot | 3682.240 / 3662.808 | 139.0 / 139.8 | 67.89 / 68.25 | 9494.539 / 11349.452 | 9494.168 / 13197.691 | 1.005 |

Paired batch ratio: median **1.005**, range 0.978–1.091, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 688761 | 425650 / 425644 | 36864 |
| 2 | 0 / 691865 | 427093 / 427097 | 36864 |
| 3 | 0 / 697992 | 417848 / 417842 | 36864 |

## burst_512 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 3408.359 / 3503.050 | 150.2 / 146.2 | 73.35 / 71.37 | 8491.222 / 11170.658 | 9238.213 / 10716.974 | 0.973 |
| 2 | snapshot | 4146.139 / 3895.066 | 123.5 / 131.4 | 60.30 / 64.18 | 10637.827 / 15792.590 | 10872.133 / 15754.539 | 1.064 |
| 3 | row | 3802.280 / 3706.885 | 134.7 / 138.1 | 65.75 / 67.44 | 10455.999 / 13772.350 | 9536.327 / 11819.256 | 1.026 |

Paired batch ratio: median **1.026**, range 0.973–1.064, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 686118 | 425020 / 425024 | 36864 |
| 2 | 0 / 690364 | 423564 / 423557 | 36864 |
| 3 | 0 / 695098 | 417417 / 417411 | 36864 |
