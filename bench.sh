SCRIPT_PATH=$(dirname "$(realpath "$0")")

cargo +nightly bench --features nightly --manifest-path "$SCRIPT_PATH/benches/Cargo.toml" -- "$@"

TARGET_DIR="$SCRIPT_PATH/benches"
while [ ! -d "$TARGET_DIR/target" ]; do
  TARGET_DIR=$(dirname "$TARGET_DIR")
  if [ "$TARGET_DIR" = "/" ]; then
    echo "Could not find target directory"
    exit 1
  fi
done

cp -r "$TARGET_DIR/target/criterion" "$SCRIPT_PATH/criterion"
# Make the violin plots white for the GitHub README, invisible on the website
# And use sed -i.bak for macOS (BSD) sed
find "$SCRIPT_PATH/criterion" -name "*.svg" -exec sed -i.bak 's/fill="none"\/>/fill="white"\/>/g' {} \;
find "$SCRIPT_PATH/criterion" -name "*.svg.bak" -exec rm {} \;