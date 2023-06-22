SCRIPT_PATH=$(dirname "$(realpath "$0")")

sudo -s -- <<EOF
cargo +nightly flamegraph \
  --bench benches \
  --features nightly \
  --manifest-path "$SCRIPT_PATH/benches/Cargo.toml" \
  --output "$SCRIPT_PATH/benches/target/criterion/report/flamegraph.svg" \
  --root \
  --deterministic \
  -- --bench -- "$@"

TARGET_DIR="$SCRIPT_PATH/benches"
while [ ! -d "$TARGET_DIR/target" ]; do
  TARGET_DIR=$(dirname "$TARGET_DIR")
  if [ "$TARGET_DIR" = "/" ]; then
    echo "Could not find target directory"
    exit 1
  fi
done

# Since we run cargo as root, it will give make build files root permissions. We don't want that
chown -R "$USER" "$TARGET_DIR/target"
EOF