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
```

The network cases need macOS 26 (vmnet without root) and outbound internet
access.
