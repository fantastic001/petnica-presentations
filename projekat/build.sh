#!/usr/bin/env bash

build_pdf() {
    local presentation_dir="$1"
    local source
    local name
    for source in "${presentation_dir}"/*.tex; do
        [ -e "${source}" ] || continue
        name="$(basename "${source%.tex}")"
        (
            cd "${presentation_dir}"
            latexmk -pdf -silent -interaction=nonstopmode "${name}.tex"
            latexmk -c "${name}.tex"
            rm -f "${name}.nav" "${name}.snm" "${name}.vrb" "${name}.toc"
        ) || return 1
        cp "${presentation_dir}/${name}.pdf" "${DIST_PDF}/${name}.pdf" \
            || return 1
    done
}
