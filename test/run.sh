#!/usr/bin/env bash

set -e
set -u

cd $(dirname "$0")
TEST_DIR=$(pwd)
PKG_DIR=$(dirname "$TEST_DIR")

# Make Node complain about deprecations more loudly.
export NODE_PENDING_DEPRECATION=1
export NODE_OPTIONS="--trace-warnings"

cd "$PKG_DIR"
npm link packages/babel-plugin-transform-es2015-modules-reify
cd node_modules
rm -rf reify babel-plugin-transform-es2015-modules-reify/node_modules/reify
ln -s .. reify

cd "$TEST_DIR"

rm -rf .cache
export REIFY_PARSER=babylon

mocha \
    --require "../node" \
    --reporter spec \
    --full-trace \
    run.js

rm -rf .cache
export REIFY_PARSER=acorn

mocha \
    --require "../node" \
    --reporter spec \
    --full-trace \
    run.js

# Run tests again using test/.cache.
mocha \
    --require "../node" \
    --reporter spec \
    --full-trace \
    run.js
