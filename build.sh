#!/usr/bin/env bash

set -euo pipefail

REPOSITORY_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SELF_PATH="${REPOSITORY_DIR}/$(basename "${BASH_SOURCE[0]}")"
PRESENTATION_BUILD_SCRIPT="build.sh"
PRESENTATION_FIGURES_SCRIPT="figures.py"
PRESENTATION_REQUIREMENTS="requirements.txt"
DEFAULT_PYTHON_PACKAGES=(matplotlib numpy seaborn)
SUPPORTED_PYTHONS=(python3.14 python3.13 python3.12 python3.11 python3)
MINIMUM_PYTHON="3.11"
MARP_PACKAGE="@marp-team/marp-cli"
BUILD_ENV_DIR="${BUILD_ENV_DIR:-}"
OWNED_ENV_DIR=""

log() {
    printf '%s\n' "$*" >&2
}

fail() {
    printf 'error: %s\n' "$*" >&2
    exit 1
}

require_command() {
    local name="$1"
    command -v "$name" >/dev/null 2>&1 || fail "missing required command: ${name}"
}

require_dist_directory() {
    [ -n "${DIST_PDF:-}" ] || fail "DIST_PDF is not set"
    mkdir -p "${DIST_PDF}"
}

marp_sources() {
    local presentation_dir="$1"
    local source
    for source in "${presentation_dir}"/*.md; do
        [ -e "${source}" ] || continue
        if head -n 10 "${source}" | grep -q '^marp: *true'; then
            printf '%s\n' "${source}"
        fi
    done
}

is_presentation() {
    local presentation_dir="$1"
    [ -d "${presentation_dir}" ] || return 1
    [ -f "${presentation_dir}/${PRESENTATION_BUILD_SCRIPT}" ] && return 0
    [ -n "$(marp_sources "${presentation_dir}")" ]
}

discover_presentations() {
    local candidate
    for candidate in "${REPOSITORY_DIR}"/*/; do
        candidate="${candidate%/}"
        if is_presentation "${candidate}"; then
            printf '%s\n' "${candidate}"
        fi
    done
}

supports_minimum_version() {
    local interpreter="$1"
    "${interpreter}" -c "import sys; \
        major, minor = \"${MINIMUM_PYTHON}\".split(\".\"); \
        sys.exit(0 if sys.version_info >= (int(major), int(minor)) else 1)" \
        2>/dev/null
}

select_python() {
    local interpreter
    for interpreter in "${SUPPORTED_PYTHONS[@]}"; do
        if command -v "${interpreter}" >/dev/null 2>&1 \
            && supports_minimum_version "${interpreter}"; then
            printf '%s\n' "${interpreter}"
            return 0
        fi
    done
    fail "no python >= ${MINIMUM_PYTHON} found"
}

prepare_env() {
    local env_dir="$1"
    local presentation_dir="$2"
    mkdir -p "${env_dir}"
    if [ ! -x "${env_dir}/python/bin/python" ]; then
        local interpreter
        interpreter="$(select_python)"
        log "creating python environment in ${env_dir} with ${interpreter}"
        "${interpreter}" -m venv "${env_dir}/python"
        "${env_dir}/python/bin/pip" install --quiet --upgrade pip
        "${env_dir}/python/bin/pip" install --quiet "${DEFAULT_PYTHON_PACKAGES[@]}"
    fi
    if [ -f "${presentation_dir}/${PRESENTATION_REQUIREMENTS}" ]; then
        "${env_dir}/python/bin/pip" install --quiet \
            -r "${presentation_dir}/${PRESENTATION_REQUIREMENTS}"
    fi
    if [ ! -x "${env_dir}/node/node_modules/.bin/marp" ]; then
        log "installing ${MARP_PACKAGE} in ${env_dir}"
        mkdir -p "${env_dir}/node"
        npm install --silent --no-fund --no-audit \
            --prefix "${env_dir}/node" "${MARP_PACKAGE}" >/dev/null
    fi
}

enter_env() {
    local env_dir="$1"
    PATH="${env_dir}/python/bin:${env_dir}/node/node_modules/.bin:${PATH}"
    export PATH
    export PYTHONPATH="${REPOSITORY_DIR}${PYTHONPATH:+:${PYTHONPATH}}"
}

build_figures() {
    local presentation_dir="$1"
    if [ -f "${presentation_dir}/${PRESENTATION_FIGURES_SCRIPT}" ]; then
        log "building figures for $(basename "${presentation_dir}")"
        (
            cd "${presentation_dir}"
            python "${PRESENTATION_FIGURES_SCRIPT}"
        ) || return 1
    else
        log "no figures script in $(basename "${presentation_dir}"), skipping"
    fi
}

build_pdf() {
    local presentation_dir="$1"
    local source
    local target
    while read -r source; do
        [ -n "${source}" ] || continue
        target="${DIST_PDF}/$(basename "${source%.md}").pdf"
        log "building ${target}"
        marp "${source}" --pdf --allow-local-files -o "${target}" </dev/null \
            || return 1
    done < <(marp_sources "${presentation_dir}")
}

build() {
    local presentation_dir="$1"
    build_figures "${presentation_dir}" || return 1
    build_pdf "${presentation_dir}" || return 1
}

load_overrides() {
    local presentation_dir="$1"
    local override="${presentation_dir}/${PRESENTATION_BUILD_SCRIPT}"
    if [ -f "${override}" ] && [ "${override}" != "${SELF_PATH}" ]; then
        log "using build script of $(basename "${presentation_dir}")"
        source "${override}"
    fi
}

build_presentation() {
    local presentation_dir="$1"
    local env_dir="$2"
    (
        load_overrides "${presentation_dir}" || return 1
        prepare_env "${env_dir}" "${presentation_dir}" || return 1
        enter_env "${env_dir}" || return 1
        build "${presentation_dir}"
    )
}

resolve_presentation() {
    local name="$1"
    local candidate="${name}"
    [ -d "${candidate}" ] || candidate="${REPOSITORY_DIR}/${name}"
    is_presentation "${candidate}" \
        || fail "not a presentation directory: ${name}"
    (cd "${candidate}" && pwd)
}

cleanup() {
    if [ -n "${OWNED_ENV_DIR}" ] && [ -d "${OWNED_ENV_DIR}" ]; then
        log "removing ${OWNED_ENV_DIR}"
        rm -rf "${OWNED_ENV_DIR}"
    fi
}

list_presentations() {
    local presentation_dir
    while read -r presentation_dir; do
        printf '%s\n' "$(basename "${presentation_dir}")"
    done < <(discover_presentations)
}

main() {
    if [ "${1:-}" = "--list" ]; then
        list_presentations
        return 0
    fi
    require_command python3
    require_command npm
    require_dist_directory
    local env_dir="${BUILD_ENV_DIR}"
    if [ -z "${env_dir}" ]; then
        env_dir="$(mktemp -d "${TMPDIR:-/tmp}/petnica-build-XXXXXX")"
        OWNED_ENV_DIR="${env_dir}"
    fi
    trap cleanup EXIT
    local -a presentations=()
    local name
    if [ "$#" -eq 0 ]; then
        while read -r name; do
            presentations+=("${name}")
        done < <(discover_presentations)
    else
        for name in "$@"; do
            presentations+=("$(resolve_presentation "${name}")")
        done
    fi
    [ "${#presentations[@]}" -gt 0 ] || fail "no presentations found"
    local presentation_dir
    local -a failed=()
    for presentation_dir in "${presentations[@]}"; do
        log "== $(basename "${presentation_dir}")"
        if ! build_presentation "${presentation_dir}" "${env_dir}"; then
            failed+=("$(basename "${presentation_dir}")")
            log "failed: $(basename "${presentation_dir}")"
        fi
    done
    if [ "${#failed[@]}" -gt 0 ]; then
        fail "failed presentations: ${failed[*]}"
    fi
    log "done, pdfs in ${DIST_PDF}"
}

main "$@"
