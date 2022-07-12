// Copyright (c) Facebook, Inc. and its affiliates. All Rights Reserved.
// Original License: https://github.com/facebook/rocksdb/blob/main/LICENSE.Apache
package org.prql.prql4j;

import java.io.IOException;

public class Environment {
  private static final String OS = System.getProperty("os.name").toLowerCase();
  private static final String ARCH = System.getProperty("os.arch").toLowerCase();
  private static boolean MUSL_LIBC;

  static {
    try {
      final Process p = new ProcessBuilder("/usr/bin/env", "sh", "-c", "ldd /usr/bin/env | grep -q musl").start();
      MUSL_LIBC = p.waitFor() == 0;
    } catch (final IOException | InterruptedException e) {
      MUSL_LIBC = false;
    }
  }

  public static boolean isAarch64() {
    return ARCH.contains("aarch64");
  }

  public static boolean isPowerPC() {
    return ARCH.contains("ppc");
  }

  public static boolean isS390x() {
    return ARCH.contains("s390x");
  }

  public static boolean isWindows() {
    return (OS.contains("win"));
  }

  public static boolean isFreeBSD() {
    return (OS.contains("freebsd"));
  }

  public static boolean isMac() {
    return (OS.contains("mac"));
  }

  public static boolean isAix() {
    return OS.contains("aix");
  }

  public static boolean isUnix() {
    return OS.contains("nix") ||
        OS.contains("nux");
  }

  public static boolean isMuslLibc() {
    return MUSL_LIBC;
  }

  public static boolean isSolaris() {
    return OS.contains("sunos");
  }

  public static boolean isOpenBSD() {
    return (OS.contains("openbsd"));
  }

  public static boolean is64Bit() {
    if (ARCH.contains("sparcv9")) {
      return true;
    }
    return (ARCH.indexOf("64") > 0);
  }

  public static String getSharedLibraryName(final String name) {
    return name;
  }

  public static String getSharedLibraryFileName(final String name) {
    return appendLibOsSuffix("lib" + getSharedLibraryName(name));
  }

  /**
   * Get the name of the libc implementation
   *
   * @return the name of the implementation,
   *    or null if the default for that platform (e.g. glibc on Linux).
   */
  public static /* @Nullable */ String getLibcName() {
    if (isMuslLibc()) {
      return "musl";
    } else {
      return null;
    }
  }

  private static String getLibcPostfix() {
    final String libcName = getLibcName();
    if (libcName == null) {
      return "";
    }
    return "-" + libcName;
  }

  public static String getJniLibraryName(final String name) {
    if (isUnix()) {
      final String arch = is64Bit() ? "64" : "32";
      if (isPowerPC() || isAarch64()) {
        return String.format("%s-linux-%s%s", name, ARCH, getLibcPostfix());
      } else if (isS390x()) {
        return String.format("%s-linux-%s", name, ARCH);
      } else {
        return String.format("%s-linux%s%s", name, arch, getLibcPostfix());
      }
    } else if (isMac()) {
      if (is64Bit()) {
        final String arch;
        if (isAarch64()) {
          arch = "arm64";
        } else {
          arch = "x86_64";
        }
        return String.format("%s-osx-%s", name, arch);
      } else {
        return String.format("%s-osx", name);
      }
    } else if (isFreeBSD()) {
      return String.format("%s-freebsd%s", name, is64Bit() ? "64" : "32");
    } else if (isAix() && is64Bit()) {
      return String.format("%s-aix64", name);
    } else if (isSolaris()) {
      final String arch = is64Bit() ? "64" : "32";
      return String.format("%s-solaris%s", name, arch);
    } else if (isWindows() && is64Bit()) {
      return String.format("%s-win64", name);
    } else if (isOpenBSD()) {
      return String.format("%s-openbsd%s", name, is64Bit() ? "64" : "32");
    }

    throw new UnsupportedOperationException(String.format("Cannot determine JNI library name for ARCH='%s' OS='%s' name='%s'", ARCH, OS, name));
  }

  public static /*@Nullable*/ String getFallbackJniLibraryName(final String name) {
    if (isMac() && is64Bit()) {
      return String.format("%s-osx", name);
    }
    return null;
  }

  public static String getJniLibraryFileName(final String name) {
    return appendLibOsSuffix("lib" + getJniLibraryName(name));
  }

  public static /*@Nullable*/ String getFallbackJniLibraryFileName(final String name) {
    final String fallbackJniLibraryName = getFallbackJniLibraryName(name);
    if (fallbackJniLibraryName == null) {
      return null;
    }
    return appendLibOsSuffix("lib" + fallbackJniLibraryName);
  }

  private static String appendLibOsSuffix(final String libraryFileName) {
    if (isUnix() || isAix() || isSolaris() || isFreeBSD() || isOpenBSD()) {
      return libraryFileName + ".so";
    } else if (isMac()) {
      return libraryFileName + ".dylib";
    } else if (isWindows()) {
      return libraryFileName + ".dll";
    }
    throw new UnsupportedOperationException();
  }

  public static String getJniLibraryExtension() {
    if (isWindows()) {
      return ".dll";
    }
    return (isMac()) ? ".dylib" : ".so";
  }
}
