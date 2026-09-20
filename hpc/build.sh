#!/usr/bin/env bash

build_pdf() {
    local presentation_dir="$1"
    local source
    for source in "${presentation_dir}"/*.odp; do
        [ -e "${source}" ] || continue
        soffice --headless --convert-to pdf --outdir "${DIST_PDF}" \
            "${source}" >/dev/null || return 1
    done
}
