#!/usr/bin/env bash

build_pdf() {
    local presentation_dir="$1"
    local source
    local name
    local work
    local status
    for source in "${presentation_dir}"/*.tex; do
        [ -e "${source}" ] || continue
        name="$(basename "${source%.tex}")"
        work="$(mktemp -d "${TMPDIR:-/tmp}/latex-build-XXXXXX")"
        status=0
        (
            cd "${presentation_dir}"
            latexmk -pdf -silent -interaction=nonstopmode \
                -outdir="${work}" "${name}.tex"
        ) || status=1
        if [ "${status}" -eq 0 ]; then
            mv "${work}/${name}.pdf" "${DIST_PDF}/${name}.pdf" || status=1
        fi
        rm -rf "${work}"
        [ "${status}" -eq 0 ] || return 1
    done
}
