#!/bin/sh
#
# Build and run a matrix of MirageOS unikernels on this Mac with solo5-hvt
# (Hypervisor.framework) and check that each one does what it should.
#
# Usage: ./run-matrix.sh [--no-build] [--no-network] [NAME...]
#
#   --no-build    reuse the unikernels already built
#   --no-network  skip the cases that need vmnet (solo5-vmnet)
#   NAME...       only run these cases (see CASES below)
#
# Needs an opam switch with the hvf-mac repository (see
# ../opam-repository/README.md) and `opam env` applied. Exits non-zero if
# any case fails.
#
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
SKELETON="${HERE}/skeleton"
SKELETON_URL="https://github.com/mirage/mirage-skeleton"
SKELETON_REV="${SKELETON_REV:-main}"
WORK="${TMPDIR:-/tmp}/mirage-matrix.$$"
BUILD=1
NETWORK=1

while [ $# -gt 0 ]; do
    case "$1" in
        --no-build) BUILD=0 ;;
        --no-network) NETWORK=0 ;;
        --) shift; break ;;
        -*) echo "unknown option: $1" >&2; exit 2 ;;
        *) break ;;
    esac
    shift
done
ONLY="$*"

for tool in mirage solo5-hvt solo5-vmnet opam; do
    command -v "${tool}" >/dev/null 2>&1 || {
        echo "error: ${tool} not found; run: eval \$(opam env)" >&2
        exit 2
    }
done

if [ ! -d "${SKELETON}" ]; then
    git clone -q "${SKELETON_URL}" "${SKELETON}" || exit 2
    git -C "${SKELETON}" checkout -q "${SKELETON_REV}" || exit 2
fi
mkdir -p "${WORK}"
trap 'rm -rf "${WORK}"' EXIT

PASS=0
FAIL=0
SKIP=0
FAILED=""

# build DIR: configure and build the unikernel in skeleton/DIR (or in DIR, if
# it is an absolute path) for hvt.
build()
{
    [ "${BUILD}" = 1 ] || return 0
    case "$1" in
        /*) dir="$1" ;;
        *) dir="${SKELETON}/$1" ;;
    esac
    # opam-monorepo deletes an existing duniverse/ before pulling, and fails
    # with "Directory not empty" when macOS (Finder) writes a .DS_Store into
    # it meanwhile. Renaming it out of the way is atomic.
    (
        if [ -d "${dir}/duniverse" ]; then
            mv "${dir}/duniverse" "$(mktemp -d "${WORK}/old-duniverse.XXXXXX")" ||
                exit 1
        fi
        cd "${dir}" &&
        mirage configure -t hvt >"${WORK}/build.log" 2>&1 &&
        make depends >>"${WORK}/build.log" 2>&1 &&
        make build >>"${WORK}/build.log" 2>&1
    ) || {
        echo "FAIL build $1"
        sed 's/^/    /' "${WORK}/build.log" | tail -20
        FAIL=$((FAIL + 1))
        FAILED="${FAILED} build:$1"
        return 1
    }
}

# check NAME PATTERN COMMAND...: run COMMAND (with a 60s timeout) and pass if
# it exits 0 and its output matches the extended regex PATTERN.
check()
{
    name="$1"
    pattern="$2"
    shift 2
    timeout 60 "$@" >"${WORK}/${name}.log" 2>&1
    rc=$?
    if [ ${rc} -eq 0 ] && grep -Eq "${pattern}" "${WORK}/${name}.log"; then
        echo "PASS ${name}"
        PASS=$((PASS + 1))
    else
        echo "FAIL ${name} (exit ${rc})"
        sed 's/^/    /' "${WORK}/${name}.log" | tail -15
        FAIL=$((FAIL + 1))
        FAILED="${FAILED} ${name}"
    fi
}

skip()
{
    echo "SKIP $1 ($2)"
    SKIP=$((SKIP + 1))
}

want()
{
    [ -z "${ONLY}" ] && return 0
    for n in ${ONLY}; do [ "$n" = "$1" ] && return 0; done
    return 1
}

S="${SKELETON}"

if want hello; then
    build tutorial/hello &&
    check hello "\[application\] hello" \
        solo5-hvt --mem=32 -- "${S}/tutorial/hello/dist/hello.hvt"
fi

if want noop; then
    build tutorial/noop &&
    check noop "solo5_exit\(0\)" \
        solo5-hvt --mem=32 -- "${S}/tutorial/noop/dist/noop.hvt"
fi

if want block; then
    dd if=/dev/zero of="${WORK}/disk.img" bs=1048576 count=8 2>/dev/null
    build device-usage/block &&
    check block "Total tests failed: +0" \
        solo5-hvt --mem=32 --block:storage="${WORK}/disk.img" -- \
        "${S}/device-usage/block/dist/block_test.hvt"
fi

if want crypto; then
    build applications/crypto &&
    check crypto "Generated a RSA key of 4096 bits \(sign \+ verify true\)" \
        solo5-hvt --mem=64 -- "${S}/applications/crypto/dist/crypto-test.hvt"
fi

if want entropy; then
    # The RNG is seeded and fed from the host (solo5_random)...
    U="${HERE}/unikernels/entropy"
    build "${U}" &&
    check entropy "entropy sources: \[0\] solo5-host" \
        solo5-hvt --mem=64 -- "${U}/dist/entropy.hvt" &&
    # ...and still boots, on its own sources, on a tender without it.
    check entropy-fallback "solo5_random unavailable" \
        solo5-hvt --mem=64 --no-random -- "${U}/dist/entropy.hvt"
fi

if want gradual; then
    # Code extracted from gradual Rocq checks its casts at run time and
    # agrees with the kernel, also for casts at type parameters (passed
    # at run time)...
    U="${HERE}/unikernels/gradual"
    build "${U}" && {
        check gradual "gradual: all [0-9]+ cases agree with the kernel" \
            solo5-hvt --mem=32 -- "${U}/dist/gradual.hvt"
        check gradual-poly \
            "gradual: all [0-9]+ polymorphic cases agree with the kernel" \
            solo5-hvt --mem=32 -- "${U}/dist/gradual.hvt"
        # ...and Omega, well typed there, never terminates: --cpu-limit
        # stops it.
        timeout 30 solo5-hvt --mem=32 --cpu-limit=2 --exit-report=3 -- \
            "${U}/dist/gradual.hvt" --omega \
            3>"${WORK}/omega.json" >"${WORK}/omega.log" 2>&1
        if grep -q '"reason":"cpu_limit"' "${WORK}/omega.json" &&
            grep -q "gradual: running Omega" "${WORK}/omega.log"; then
            echo "PASS gradual-omega (stopped by --cpu-limit)"
            PASS=$((PASS + 1))
        else
            echo "FAIL gradual-omega: $(cat "${WORK}/omega.json")"
            sed 's/^/    /' "${WORK}/omega.log" | tail -5
            FAIL=$((FAIL + 1))
            FAILED="${FAILED} gradual-omega"
        fi
    }
fi

if want sandbox-cpu-limit; then
    # A guest that never returns is stopped by --cpu-limit and reported.
    build device-usage/clock
    timeout 30 solo5-hvt --mem=32 --cpu-limit=1 --exit-report=3 -- \
        "${S}/device-usage/clock/dist/speaking_clock.hvt" \
        3>"${WORK}/report.json" >/dev/null 2>&1
    # The speaking clock sleeps between ticks and uses almost no CPU, so it
    # must still be running when the timeout fires, i.e. not be stopped.
    if grep -q '"kind":"signal"' "${WORK}/report.json"; then
        echo "PASS sandbox-cpu-limit (idle guest not stopped)"
        PASS=$((PASS + 1))
    else
        echo "FAIL sandbox-cpu-limit: $(cat "${WORK}/report.json")"
        FAIL=$((FAIL + 1))
        FAILED="${FAILED} sandbox-cpu-limit"
    fi
fi

if [ "${NETWORK}" = 1 ]; then
    if want dns; then
        build applications/dns &&
        check dns "mirageos.org: [0-9.]+" \
            solo5-vmnet -- solo5-hvt --mem=64 -- \
            "${S}/applications/dns/dist/resolve.hvt" --domain-name=mirageos.org
    fi

    if want https-fetch; then
        build device-usage/http-fetch &&
        check https-fetch "Received body length: [1-9]" \
            solo5-vmnet -- solo5-hvt --mem=128 -- \
            "${S}/device-usage/http-fetch/dist/http-fetch.hvt"
    fi

    if want egress-deny; then
        # With an allow-list that excludes everything the guest needs, the
        # fetch must fail and solo5-vmnet must have dropped its traffic.
        build device-usage/http-fetch
        timeout 60 solo5-vmnet --verbose --allow=10.255.255.255/32 -- \
            solo5-hvt --mem=128 -- \
            "${S}/device-usage/http-fetch/dist/http-fetch.hvt" \
            >"${WORK}/egress-deny.log" 2>&1
        if grep -q "dropped IPv4 packet" "${WORK}/egress-deny.log" &&
            ! grep -q "Received body length" "${WORK}/egress-deny.log"; then
            echo "PASS egress-deny"
            PASS=$((PASS + 1))
        else
            echo "FAIL egress-deny"
            tail -10 "${WORK}/egress-deny.log" | sed 's/^/    /'
            FAIL=$((FAIL + 1))
            FAILED="${FAILED} egress-deny"
        fi
    fi

    if want guest-to-guest; then
        # One unikernel serves HTTP, another fetches from it over vmnet.
        build applications/static_website_tls &&
        build device-usage/http-fetch && {
            solo5-vmnet -- solo5-hvt --mem=128 -- \
                "${S}/applications/static_website_tls/dist/https.hvt" \
                >"${WORK}/server.log" 2>&1 &
            server=$!
            ip=""
            for _ in $(seq 1 40); do
                ip="$(grep -o 'ip=192\.168\.[0-9]*\.[0-9]*' \
                    "${WORK}/server.log" | head -1 | cut -d= -f2)"
                [ -n "${ip}" ] && break
                sleep 0.25
            done
            if [ -z "${ip}" ]; then
                echo "FAIL guest-to-guest (server did not come up)"
                FAIL=$((FAIL + 1))
                FAILED="${FAILED} guest-to-guest"
            else
                check guest-to-guest "Moved_permanently" \
                    solo5-vmnet -- solo5-hvt --mem=128 -- \
                    "${S}/device-usage/http-fetch/dist/http-fetch.hvt" \
                    --uri="http://${ip}/"
            fi
            kill "${server}" 2>/dev/null
            wait "${server}" 2>/dev/null
        }
    fi
else
    skip "dns https-fetch egress-deny guest-to-guest" "--no-network"
fi

echo
echo "${PASS} passed, ${FAIL} failed, ${SKIP} skipped"
[ ${FAIL} -eq 0 ] || { echo "failed:${FAILED}"; exit 1; }
