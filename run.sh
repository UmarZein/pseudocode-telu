#!/usr/bin/env bash
cargo r && clang -lm program.o -o program && ./program
