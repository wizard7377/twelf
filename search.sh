#!/bin/sh
GLOBS=lib/**/*
FORMAT="Outside of \`./%f\` change each occurence of \`%O\` to \`%a.%O\`%~"
PATTERN='(?<=module type )\S+'
result=$(ug -P -o --iglob="$GLOBS" --format="$FORMAT" "$PATTERN")
echo "$result"