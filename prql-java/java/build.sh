#!/bin/sh
set -e

JAVA_SRC_HOME=$1
ARCH="$(uname -m)"
KERNEL_NAME="$(uname -s)"
KERNEL_VERSION="$(uname -r)"

echo JAVA_SRC_HOME="$JAVA_SRC_HOME"

cd "$JAVA_SRC_HOME"
# cd prql-java/
cd ../

echo Platform Info: "$ARCH" "$KERNEL_NAME" "$KERNEL_VERSION"

echo building...
cargo build --release
echo building successfully
ls -la ../target/release

if [ "$KERNEL_NAME" = 'Linux' ]; then
  if [ "$ARCH" = 'arm64' ] || [ "$ARCH" = 'aarch64' ]; then
    target='libprql_java-linux-aarch64.so'
  elif [ "$ARCH" = 'x86_64' ]; then
    target='libprql_java-linux64.so'
  else
    target='libprql_java-linux32.so'
  fi
  cp -f ../target/release/libprql_java.so java/src/test/resources/${target}
elif [ "$KERNEL_NAME" = 'Darwin' ]; then
  if [ "$ARCH" = 'arm64' ] || [ "$ARCH" = 'aarch64' ]; then
    target='libprql_java-osx-arm64.dylib'
  elif [ "$ARCH" = 'x86_64' ]; then
    target='libprql_java-osx-x86_64.dylib'
  else
    echo [ERROR] have not support $ARCH:$$KERNEL_NAME yet
    exit 1
  fi
  cp -f ../target/release/libprql_java.dylib java/src/test/resources/${target}
fi

ls -la ./java/src/main/resources
