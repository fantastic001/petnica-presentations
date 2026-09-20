DIST_PDF ?= $(CURDIR)/dist
BUILD := ./build.sh
PRESENTATIONS := $(shell $(BUILD) --list)
PYTHON := $(shell test -x .venv/bin/python && echo .venv/bin/python || echo python3)

export DIST_PDF

.PHONY: all build check clean $(PRESENTATIONS)

all: build

build:
	$(BUILD)

$(PRESENTATIONS):
	$(BUILD) $@

check:
	$(PYTHON) tools/check_slides.py

clean:
	rm -rf "$(DIST_PDF)"
