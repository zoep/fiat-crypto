#!/usr/bin/env bash

set -x

CACHE_DIR="$HOME/.cache/vos"
PREV_ARCHIVE="${CACHE_DIR}/vos-${COQ_VERSION}-${PREV}.tar.gz"
CUR_ARCHIVE="${CACHE_DIR}/vos-${COQ_VERSION}-${CUR}.tar.gz"

tar -xzf "${PREV_ARCHIVE}" || true
mkdir -p "${CACHE_DIR}"

rm -f finished.ok
(make "$@" TIMED=1 2>&1 && touch finished.ok) | tee -a time-of-build.log
python "./etc/coq-scripts/timing/make-one-time-file.py" "time-of-build.log" "time-of-build-pretty.log" || exit $?
rm -f "${CUR_ARCHIVE}"
tar -czf "${CUR_ARCHIVE}" time-of-build.log src coqprime || exit $?

git update-index --assume-unchanged _CoqProject
git status
git diff

cat time-of-build-pretty.log
make "$@" TIMED=1 || exit $?
