
.PHONY: build run

MAKEFILE_DIR:=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))

all: clean build run

build:
	cd ${MAKEFILE_DIR}Haskell_Partitions && cabal build --enable-profiling --profiling-detail=late # -O0

run:
	HASKELL_EXE=$(shell cd ${MAKEFILE_DIR}Haskell_Partitions && cabal list-bin all); \
	echo $$HASKELL_EXE; \
	$$HASKELL_EXE +RTS -p

clean:
	rm -rf ${MAKEFILE_DIR}Haskell_Partitions/dist-newstyle/