# Petnica prezentacije

Svaka prezentacija živi u svom direktorijumu. Direktorijum se gradi ako
ima Marp fajl (`marp: true` u zaglavlju) ili svoj `build.sh`. Ako ima i
`figures.py`, slike se prave pre PDF-a, a slike stoje uz prezentaciju.

Formati koji se grade:

| Format | Kako se gradi |
|---|---|
| Marp markdown | podrazumevano, `marp` |
| LaTeX (`fp`, `git-predavanje`, `projekat`, `projekat-letnji`, `tla_plus`) | `build.sh` u tom direktorijumu, `latexmk` |
| LibreOffice (`hpc`) | `build.sh` u tom direktorijumu, `soffice` |

## Gradnja

```sh
make                 # sve prezentacije
make llm             # samo jedna
make check           # provera da nijedan slajd nije izgubio tekst
make clean           # briše dist
```

`DIST_PDF` određuje gde idu PDF-ovi, podrazumevano `dist/`:

```sh
DIST_PDF=/putanja/do/izlaza ./build.sh naucni-metod
```

Bez argumenta `build.sh` gradi sve prezentacije. `./build.sh --list`
ispisuje koje je našao.

## Okruženje

`build.sh` pravi privremeno okruženje u `TMPDIR`: Python virtuelno
okruženje sa `matplotlib`, `numpy` i `seaborn`, i lokalnu instalaciju
`@marp-team/marp-cli`. Okruženje se briše na kraju. Ako prezentacija ima
`requirements.txt`, i on se instalira. Za ponovnu upotrebu okruženja
između gradnji postavi `BUILD_ENV_DIR` na stalnu putanju.

Traži se Python 3.11 ili noviji, jer ga zahteva `figures_framework`.

## Sopstvena gradnja po prezentaciji

Ako direktorijum prezentacije ima svoj `build.sh`, on se učitava i može
da zameni ove funkcije:

| Funkcija | Argumenti | Podrazumevano radi |
|---|---|---|
| `prepare_env` | direktorijum okruženja, direktorijum prezentacije | pravi Python i Marp okruženje |
| `enter_env` | direktorijum okruženja | dodaje okruženje u `PATH` |
| `build_figures` | direktorijum prezentacije | pokreće `figures.py` iz tog direktorijuma |
| `build_pdf` | direktorijum prezentacije | Marp gradi PDF u `DIST_PDF` |

`build` poziva `build_figures` pa `build_pdf`. Pri pokretanju
`figures.py` radni direktorijum je direktorijum prezentacije.
