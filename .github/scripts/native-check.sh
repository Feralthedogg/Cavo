#!/usr/bin/env bash
# CI and local qualification share the pinned producer and mandatory native tests.
# There is no runtime-policy fallback when admission or image verification fails.
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
cd -- "$root"
export CARGO_INCREMENTAL=0 CAVO_NATIVE_REQUIRED=1 CAVO_MANAGED_REQUIRED=1
export PYTHONDONTWRITEBYTECODE=1

fetch_bottle() {
    local name=$1 digest=$2 destination=$3 token
    token=$(curl --fail --silent --show-error \
        "https://ghcr.io/token?service=ghcr.io&scope=repository:homebrew/core/$name:pull" | \
        python3 -c 'import json,sys; print(json.load(sys.stdin)["token"])')
    curl --fail --location --retry 3 \
        --header "Authorization: Bearer $token" \
        "https://ghcr.io/v2/homebrew/core/$name/blobs/sha256:$digest" \
        --output "$destination"
    printf '%s  %s\n' "$digest" "$destination" | shasum -a 256 --check
}

prepare_macos_llvm() (
    if [[ ${GITHUB_ACTIONS:-} != true ]]; then
        printf '%s\n' 'For local macOS builds, set CAVO_LLVM_BIN to a qualified LLVM 23.1.2 installation.' >&2
        return 1
    fi
    local bottles cellar prefix
    mkdir -p -- "$root/target/cavo-ci"
    bottles=$(mktemp -d "$root/target/cavo-ci/bottles.XXXXXX")
    trap 'rm -f -- "$bottles/llvm--23.1.2.arm64_tahoe.bottle.tar.gz" "$bottles/z3--5.1.0.arm64_tahoe.bottle.tar.gz"; rmdir -- "$bottles"' EXIT
    # The official Darwin archive lacks a shared LLVM target. Pin the qualified
    # Homebrew producer and its Z3 SONAME rather than tracking current formulae.
    # homebrew-core: llvm@3a7173a0f17234264c8711d59918002522d13623,
    #               z3@af6aac9be7aa9bb9158db6607c13be5711f21090.
    fetch_bottle z3 5968f6ca3a4c4f2b12e4711b9ca7556fa65a82937f1af7a2a210456ab754adb7 \
        "$bottles/z3--5.1.0.arm64_tahoe.bottle.tar.gz"
    fetch_bottle llvm bc2ff4fa3f9359d3b8b49d70cb1782f9b63040d050ca1316c047d65ed799ec6e \
        "$bottles/llvm--23.1.2.arm64_tahoe.bottle.tar.gz"
    export HOMEBREW_NO_AUTO_UPDATE=1 HOMEBREW_NO_INSTALL_CLEANUP=1
    export HOMEBREW_NO_INSTALLED_DEPENDENTS_CHECK=1
    prefix=$(brew --prefix)
    cellar=$(brew --cellar)
    if [[ ! -f $prefix/opt/zstd/lib/libzstd.1.dylib ]]; then
        brew install --formula zstd
    fi
    # Dependencies are provided explicitly: installing the current Z3 formula
    # would replace the ABI 5.1 required by this pinned LLVM bottle.
    for package in z3 llvm; do
        if brew list --versions "$package" >/dev/null 2>&1; then
            brew unlink "$package"
        fi
    done
    brew install --formula --force --overwrite --ignore-dependencies \
        "$bottles/z3--5.1.0.arm64_tahoe.bottle.tar.gz" \
        "$bottles/llvm--23.1.2.arm64_tahoe.bottle.tar.gz"
    [[ -f $prefix/opt/z3/lib/libz3.5.1.dylib ]]
    [[ -f $cellar/llvm/23.1.2/lib/libLLVM.23.1.dylib ]]
    [[ $("$cellar/llvm/23.1.2/bin/llvm-config" --version) == 23.1.2 ]]
)

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
            prepare_macos_llvm
            CAVO_LLVM_BIN="$(brew --cellar)/llvm/23.1.2/bin"
            export CAVO_LLVM_BIN
            return ;;
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
