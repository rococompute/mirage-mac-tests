# MirageOS on Apple Silicon: test matrix

`run-matrix.sh` builds a set of [mirage-skeleton](https://github.com/mirage/mirage-skeleton)
unikernels (plus the ones in `unikernels/`) for `hvt` on this Mac and runs them on `solo5-hvt`
(Hypervisor.framework), checking that each one does what it should:

| Case | What it shows |
| --- | --- |
| `hello` | boot, console, timers (`Mirage_sleep`), clean exit |
| `noop` | minimal unikernel exits 0 |
| `block` | block device reads and writes (`--block`) |
| `crypto` | mirage-crypto C and assembly code, RSA 4096 keygen, sign, verify |
| `entropy` | the RNG is seeded from the host (`solo5_random`, source `solo5-host`) |
| `entropy-fallback` | under `solo5-hvt --no-random` the same unikernel boots on its own sources |
| `gradual` | code extracted from [gradual Rocq](unikernels/gradual/gradual_prog.v) checks its casts at run time, with the kernel's results |
| `gradual-poly` | the same for casts at type parameters, whose runtime descriptions the extracted functions take as arguments |
| `gradual-omega` | Omega, well typed in gradual Rocq, never terminates and is stopped by `--cpu-limit` |
| `sandbox-cpu-limit` | an idle guest is not stopped by `--cpu-limit` |
| `dns` | DHCP and DNS over vmnet (`solo5-vmnet`) |
| `https-fetch` | DNS, TCP and TLS to the internet through vmnet NAT |
| `egress-deny` | `solo5-vmnet --allow` drops traffic outside the allow-list |
| `guest-to-guest` | one unikernel serves HTTP, another fetches from it |

```sh
eval $(opam env --switch <switch with the hvf-mac repository>)
./run-matrix.sh                 # build everything, then run
./run-matrix.sh --no-build      # rerun with what is built
./run-matrix.sh dns block       # only some cases
./run-matrix.sh --no-network    # hvt-only installation, no vmnet required
```

The harness uses the system Perl for timeouts and process-group cleanup; GNU
coreutils are not required. It checks out mirage-skeleton commit
`d51f6582fbc39882f61de45ed22759ab19def1fc`. An existing `skeleton/` must be at
that commit. To test a different snapshot, set `SKELETON_REV` to its full 40-digit
commit SHA and check out that commit in `skeleton/` first. Rebuild after changing
the snapshot; `--no-build` reuses existing artifacts.

To check the committed gradual extraction without modifying it, run
`ROCQ=/path/to/gradual-rocq/bin/rocq unikernels/gradual/extract.sh --check`.
This requires the gradual fork of Rocq and fails if either generated file differs.

The network cases need macOS 26 (vmnet without root) and outbound internet
access.
