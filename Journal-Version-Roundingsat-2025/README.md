
This directory contains three systems, the usage for each of them are the following: 


# Compilation
The compilation is the same for all systems:
```bash
$ cd build
$ cmake -DCMAKE_BUILD_TYPE=Release ..
$ make -j
```
For a debug build:
```bash
$ cd build_debug
$ cmake -DCMAKE_BUILD_TYPE=Debug ..
$ make -j
```

- `**orignal-system-write-read-logs**`: \
   The original RoundingSat 2025 version, it is used to generate the logs as an oracle to be read to guide the search. The system has been modified to be also able to read the logs by itself.

   For a writing the logs (with the default flag `--prop-counting=0.7`):
   ```bash
   $ ./roundingsat --w=1 --exec=<logs-filename> <benchmark*.opb>
   ```

   For a reading the logs:
   ```bash
   $ ./roundingsat --r=1 --exec=<logs-filename> <benchmark*.opb>
   ```

- `**improved-system-read-logs**`: \
   The improved version that will be `only` able to read a log file.

   For a reading the logs (with the default flag `--prop-counting=0.6`):
   ```bash
   $ ./roundingsat --r=1 --exec=<logs-filename> <benchmark*.opb>
   ```

- `**final-improved-system-no-logs**`: \
   The final improved RoundingSat 2025 that will run as a standard PB solver with the default flag `--prop-counting=0.6`.
   ```bash
   $ ./roundingsat <benchmark*.opb>
   ```
