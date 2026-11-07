#!/usr/bin/env bash
# CI and local qualification share the pinned producer and mandatory native tests.
# There is no runtime-policy fallback when admission or image verification fails.
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
cd -- "$root"
export CARGO_INCREMENTAL=0 CAVO_NATIVE_REQUIRED=1 CAVO_MANAGED_REQUIRED=1
export PYTHONDONTWRITEBYTECODE=1

prepare_llvm() {
    local asset digest archive prefix
    if [[ -n ${CAVO_LLVM_BIN:-} ]]; then
        [[ $("$CAVO_LLVM_BIN/llvm-config" --version) == 23.1.2 ]]
        return
    fi
    case "$(uname -s)-$(uname -m)" in
        Linux-x86_64)
            asset=LLVM-23.1.2-Linux-X64.tar.zst
            digest=6382de1c1a210ce5a5cc49d18bc8444d137742e7cbf9b19f4ae602bb1ab52534 ;;
        Darwin-arm64)
            asset=LLVM-23.1.2-macOS-ARM64.tar.xz
            digest=d7c26fc6177e42842e2d1ffaad31aec057c56a924392b1a23d830abe2c5d53b1 ;;
        *) printf '%s\n' 'This qualification script supports Linux x86_64 and macOS ARM64.' >&2; return 1 ;;
    esac
    prefix="$root/target/cavo-ci/llvm-23.1.2"
    if [[ ! -d $prefix ]]; then
        mkdir -p -- "$root/target/cavo-ci"
        archive=$(mktemp "$root/target/cavo-ci/llvm-download.XXXXXX")
        trap 'rm -f -- "$archive"' EXIT
        curl --fail --location --retry 3 \
            "https://github.com/llvm/llvm-project/releases/download/llvmorg-23.1.2/$asset" \
            --output "$archive"
        printf '%s  %s\n' "$digest" "$archive" | shasum -a 256 --check
        mkdir -- "$prefix"
        if [[ $asset == *.zst ]]; then
            zstd --decompress --long=30 --stdout "$archive" | \
                tar --extract --file - --strip-components=1 --directory "$prefix"
        else
            tar -xJf "$archive" --strip-components=1 -C "$prefix"
        fi
        rm -f -- "$archive"
        trap - EXIT
    fi
    export CAVO_LLVM_BIN="$prefix/bin"
    [[ $("$CAVO_LLVM_BIN/llvm-config" --version) == 23.1.2 ]]
}

prepare_sdk() {
    local source="$root/target/cavo-ci/llam" build="$root/target/cavo-ci/llam-build"
    [[ $(git -C "$source" rev-parse HEAD) == f0ea03c87be4a880b88a3b03bec48334762eb3d4 ]]
    cmake -S "$source" -B "$build" -G Ninja \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_C_COMPILER="$CAVO_LLVM_BIN/clang" \
        -DCMAKE_CXX_COMPILER="$CAVO_LLVM_BIN/clang++" \
        -DCMAKE_ASM_COMPILER="$CAVO_LLVM_BIN/clang" \
        -DLLVM_DIR="$CAVO_LLVM_BIN/../lib/cmake/llvm" \
        -DLLAM_MANAGED_TOOLING=required -DLLAM_PREEMPT_TOOLING=off \
        -DLLAM_EXPERIMENTAL_ASYNC_PREEMPT=ON
    cmake --build "$build" --target llam_runtime llam_managed_pass --parallel 4
    cargo build --workspace --locked --offline
    export CAVO_LLAM_SDK="$root/target/cavo-native-sdk/llam-3.0.0"
    target/debug/cavoite sdk --llam-source "$source" --llam-build "$build" -o "$CAVO_LLAM_SDK"
    if [[ -n ${GITHUB_ENV:-} ]]; then
        printf 'CAVO_LLVM_BIN=%s\nCAVO_LLAM_SDK=%s\n' "$CAVO_LLVM_BIN" "$CAVO_LLAM_SDK" >> "$GITHUB_ENV"
    fi
}

smoke() {
    : "${CAVO_LLVM_BIN:?Set CAVO_LLVM_BIN to the LLVM 23.1.2 bin directory}"
    : "${CAVO_LLAM_SDK:?Set CAVO_LLAM_SDK to the prepared LLAM 3.0.0 SDK}"
    target/debug/cavoite doctor
    local status=0
    target/debug/cavoite run examples/native/basic.cavo || status=$?
    if [[ $status != 42 ]]; then
        printf 'Expected example exit status 42, got %s\n' "$status" >&2
        return 1
    fi
}

case "${1:-}" in
    prepare) prepare_llvm; prepare_sdk ;;
    check)
        cargo test --workspace --locked --offline
        cargo test --workspace --release --locked --offline
        smoke ;;
    smoke) smoke ;;
    *) printf 'Usage: %s prepare|check|smoke\n' "$0" >&2; exit 2 ;;
esac
