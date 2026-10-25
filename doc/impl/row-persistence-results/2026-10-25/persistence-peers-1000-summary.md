# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/persistence-peers-1000.json`

Input SHA-256: `28736f08cf30e39d3d84d5e20a2196d398f6332f60f68594bc92b0e31ba5ba90`

Ratios divide snapshot batch duration by row batch duration. A ratio above 1 means the row batch finished sooner in that paired trial. Latency percentiles remain separate for every trial; no latency samples are pooled.

Storage counters describe logical SQL values and snapshot head reads. They are not physical disk I/O measurements. The benchmark omits the application request/result journal and transport.

## small_stream / send / 1000 peers

Eligible/touched peers: 1000/1000; consumed registrations: 1000; messages: 1024; plaintext bytes: 1048576; wire bytes: 1138688.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 13941.078 / 6230.246 | 73.5 / 164.4 | 0.07 / 0.16 | 19586.490 / 23217.307 | 8306.288 / 10703.680 | 2.238 |
| 2 | snapshot | 14105.358 / 7243.112 | 72.6 / 141.4 | 0.07 / 0.14 | 19666.059 / 22833.202 | 12040.888 / 15010.244 | 1.947 |
| 3 | row | 14274.954 / 6690.197 | 71.7 / 153.1 | 0.07 / 0.15 | 20576.142 / 24200.787 | 9037.178 / 14026.593 | 2.134 |

Paired batch ratio: median **2.134**, range 1.947–2.238, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 958289412 | 837779 / 837983 | 73728 |
| 2 | 0 / 958143144 | 837980 / 837982 | 73728 |
| 3 | 0 / 958389978 | 837749 / 837738 | 73728 |

## small_stream / receive / 1000 peers

Eligible/touched peers: 1000/1000; consumed registrations: 1000; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140468.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 14736.814 / 6218.640 | 69.5 / 164.7 | 0.07 / 0.16 | 21658.466 / 26234.172 | 8147.353 / 10400.375 | 2.370 |
| 2 | row | 14844.542 / 6931.200 | 69.0 / 147.7 | 0.07 / 0.14 | 21743.254 / 25554.828 | 8998.205 / 13598.476 | 2.142 |
| 3 | snapshot | 14701.760 / 7126.554 | 69.7 / 143.7 | 0.07 / 0.14 | 21081.312 / 23799.621 | 9709.750 / 12631.087 | 2.063 |

Paired batch ratio: median **2.142**, range 2.063–2.370, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 958185270 | 837937 / 837819 | 73728 |
| 2 | 0 / 958153746 | 837970 / 837766 | 73728 |
| 3 | 0 / 958527945 | 837731 / 837574 | 73728 |

## large_stream / send / 1000 peers

Eligible/touched peers: 1000/128; consumed registrations: 1000; messages: 128; plaintext bytes: 8388608; wire bytes: 8400128.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 1769.379 / 754.499 | 72.3 / 169.6 | 4.52 / 10.60 | 19403.179 / 20229.958 | 6881.406 / 10161.231 | 2.345 |
| 2 | row | 1994.219 / 780.300 | 64.2 / 164.0 | 4.01 / 10.25 | 22539.336 / 24565.757 | 8265.562 / 12769.574 | 2.556 |
| 3 | snapshot | 1784.518 / 790.205 | 71.7 / 162.0 | 4.48 / 10.12 | 19384.545 / 20322.981 | 7594.013 / 12140.132 | 2.258 |

Paired batch ratio: median **2.345**, range 2.258–2.556, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 119761471 | 104761 / 104751 | 9216 |
| 2 | 0 / 119772907 | 104780 / 104826 | 9216 |
| 3 | 0 / 119800767 | 104744 / 104711 | 9216 |

## large_stream / receive / 1000 peers

Eligible/touched peers: 1000/128; consumed registrations: 1000; messages: 128; plaintext bytes: 8388608; wire bytes: 8400252.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 1751.203 / 902.296 | 73.1 / 141.9 | 4.57 / 8.87 | 20098.834 / 21258.662 | 11315.829 / 15478.856 | 1.941 |
| 2 | snapshot | 1756.112 / 771.468 | 72.9 / 165.9 | 4.56 / 10.37 | 19379.375 / 23168.587 | 7201.923 / 9488.528 | 2.276 |
| 3 | row | 1767.842 / 769.403 | 72.4 / 166.4 | 4.53 / 10.40 | 20159.958 / 24065.877 | 7779.909 / 11271.305 | 2.298 |

Paired batch ratio: median **2.276**, range 1.941–2.298, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 119766091 | 104751 / 104751 | 9216 |
| 2 | 0 / 119776612 | 104826 / 104830 | 9216 |
| 3 | 0 / 119804815 | 104711 / 104749 | 9216 |

## mixed_stream / send / 1000 peers

Eligible/touched peers: 1000/1000; consumed registrations: 1000; messages: 1024; plaintext bytes: 5177344; wire bytes: 5267584.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 14567.641 / 6312.226 | 70.3 / 162.2 | 0.34 / 0.78 | 20821.188 / 24259.256 | 8062.615 / 10961.188 | 2.308 |
| 2 | snapshot | 14245.499 / 6243.257 | 71.9 / 164.0 | 0.35 / 0.79 | 20257.409 / 23639.272 | 8306.769 / 10796.803 | 2.282 |
| 3 | row | 14115.310 / 6214.381 | 72.5 / 164.8 | 0.35 / 0.79 | 20015.800 / 23997.890 | 7970.533 / 12837.761 | 2.271 |

Paired batch ratio: median **2.282**, range 2.271–2.308, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 958198546 | 837846 / 837978 | 73728 |
| 2 | 0 / 958267713 | 837861 / 837913 | 73728 |
| 3 | 0 / 958444226 | 837550 / 837447 | 73728 |

## mixed_stream / receive / 1000 peers

Eligible/touched peers: 1000/1000; consumed registrations: 1000; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269364.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 14599.180 / 6847.308 | 70.1 / 149.5 | 0.34 / 0.72 | 21437.735 / 25022.257 | 9562.546 / 12980.446 | 2.132 |
| 2 | row | 14886.419 / 6085.995 | 68.8 / 168.3 | 0.33 / 0.81 | 20916.526 / 24994.615 | 7234.874 / 10097.061 | 2.446 |
| 3 | snapshot | 14219.269 / 6225.222 | 72.0 / 164.5 | 0.35 / 0.79 | 20030.617 / 24101.763 | 8170.806 / 10795.391 | 2.284 |

Paired batch ratio: median **2.284**, range 2.132–2.446, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 958206088 | 838006 / 838038 | 73728 |
| 2 | 0 / 958222537 | 837895 / 838028 | 73728 |
| 3 | 0 / 958335930 | 837460 / 837448 | 73728 |

## burst_64 / send / 1000 peers

Eligible/touched peers: 1000/64; consumed registrations: 1000; messages: 64; plaintext bytes: 32768000; wire bytes: 32773760.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 944.372 / 441.702 | 67.8 / 144.9 | 33.09 / 70.75 | 21223.156 / 24513.610 | 11112.080 / 12177.182 | 2.138 |
| 2 | row | 973.284 / 468.792 | 65.8 / 136.5 | 32.11 / 66.66 | 21338.992 / 23602.805 | 10006.132 / 11688.412 | 2.076 |
| 3 | snapshot | 960.143 / 420.229 | 66.7 / 152.3 | 32.55 / 74.36 | 20056.485 / 27142.342 | 7634.338 / 13101.322 | 2.285 |

Paired batch ratio: median **2.138**, range 2.076–2.285, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 59889317 | 52385 / 52328 | 4608 |
| 2 | 0 / 59889209 | 52386 / 52391 | 4608 |
| 3 | 0 / 59906271 | 52416 / 52487 | 4608 |

## burst_64 / receive / 1000 peers

Eligible/touched peers: 1000/64; consumed registrations: 1000; messages: 64; plaintext bytes: 32768000; wire bytes: 32773820.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 901.881 / 433.762 | 71.0 / 147.5 | 34.65 / 72.04 | 18920.812 / 23304.299 | 10093.624 / 12114.906 | 2.079 |
| 2 | snapshot | 916.976 / 430.368 | 69.8 / 148.7 | 34.08 / 72.61 | 19431.362 / 20813.444 | 7682.066 / 16332.435 | 2.131 |
| 3 | row | 936.901 / 417.213 | 68.3 / 153.4 | 33.35 / 74.90 | 20142.014 / 22422.749 | 7550.772 / 11830.497 | 2.246 |

Paired batch ratio: median **2.131**, range 2.079–2.246, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 59888720 | 52328 / 52415 | 4608 |
| 2 | 0 / 59889274 | 52391 / 52421 | 4608 |
| 3 | 0 / 59907036 | 52487 / 52501 | 4608 |

## burst_256 / send / 1000 peers

Eligible/touched peers: 1000/256; consumed registrations: 1000; messages: 256; plaintext bytes: 131072000; wire bytes: 131095040.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 3608.981 / 1707.730 | 70.9 / 149.9 | 34.64 / 73.20 | 19650.750 / 21759.144 | 7865.788 / 12724.931 | 2.113 |
| 2 | snapshot | 3742.943 / 1995.688 | 68.4 / 128.3 | 33.40 / 62.64 | 20963.143 / 24274.845 | 11057.689 / 13764.325 | 1.876 |
| 3 | row | 4097.714 / 1783.749 | 62.5 / 143.5 | 30.50 / 70.08 | 23889.338 / 28950.557 | 9246.258 / 12420.826 | 2.297 |

Paired batch ratio: median **2.113**, range 1.876–2.297, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 239570418 | 209468 / 209494 | 18432 |
| 2 | 0 / 239555050 | 209609 / 209728 | 18432 |
| 3 | 0 / 239607914 | 209437 / 209461 | 18432 |

## burst_256 / receive / 1000 peers

Eligible/touched peers: 1000/256; consumed registrations: 1000; messages: 256; plaintext bytes: 131072000; wire bytes: 131095312.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 3911.846 / 1665.758 | 65.4 / 153.7 | 31.95 / 75.04 | 22675.870 / 29608.371 | 7971.124 / 9822.590 | 2.348 |
| 2 | row | 3740.941 / 1715.809 | 68.4 / 149.2 | 33.41 / 72.85 | 20832.670 / 27032.567 | 9010.088 / 10587.353 | 2.180 |
| 3 | snapshot | 4063.301 / 3098.393 | 63.0 / 82.6 | 30.76 / 40.34 | 25820.422 / 36991.661 | 20140.802 / 25532.466 | 1.311 |

Paired batch ratio: median **2.180**, range 1.311–2.348, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 239560612 | 209494 / 209477 | 18432 |
| 2 | 0 / 239549352 | 209728 / 209756 | 18432 |
| 3 | 0 / 239593810 | 209461 / 209459 | 18432 |

## burst_512 / send / 1000 peers

Eligible/touched peers: 1000/512; consumed registrations: 1000; messages: 512; plaintext bytes: 262144000; wire bytes: 262190080.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 7416.113 / 3698.011 | 69.0 / 138.5 | 33.71 / 67.60 | 19824.252 / 22735.281 | 9570.561 / 13076.315 | 2.005 |
| 2 | row | 7570.809 / 3417.679 | 67.6 / 149.8 | 33.02 / 73.15 | 21391.980 / 25206.991 | 8475.643 / 11795.812 | 2.215 |
| 3 | snapshot | 11196.570 / 5993.881 | 45.7 / 85.4 | 22.33 / 41.71 | 34967.244 / 49357.604 | 17965.213 / 23699.766 | 1.868 |

Paired batch ratio: median **2.005**, range 1.868–2.215, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 479147858 | 419032 / 419051 | 36864 |
| 2 | 0 / 479082995 | 419286 / 419207 | 36864 |
| 3 | 0 / 479214682 | 418757 / 418657 | 36864 |

## burst_512 / receive / 1000 peers

Eligible/touched peers: 1000/512; consumed registrations: 1000; messages: 512; plaintext bytes: 262144000; wire bytes: 262190864.

| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | row | 7368.891 / 4117.281 | 69.5 / 124.4 | 33.93 / 60.72 | 20855.392 / 24172.294 | 10850.183 / 14675.381 | 1.790 |
| 2 | snapshot | 9013.406 / 3915.278 | 56.8 / 130.8 | 27.74 / 63.85 | 27190.431 / 36372.529 | 12061.356 / 17017.519 | 2.302 |
| 3 | row | 10714.976 / 5933.453 | 47.8 / 86.3 | 23.33 / 42.13 | 32924.252 / 41298.416 | 17434.666 / 24057.340 | 1.806 |

Paired batch ratio: median **1.806**, range 1.790–2.302, 3 trials.

| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |
| ---: | ---: | ---: | ---: |
| 1 | 0 / 479129899 | 419051 / 418930 | 36864 |
| 2 | 0 / 479145197 | 419207 / 419147 | 36864 |
| 3 | 0 / 479244137 | 418657 / 418726 | 36864 |
