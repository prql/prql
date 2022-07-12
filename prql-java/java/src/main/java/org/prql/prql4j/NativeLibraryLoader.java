// Copyright (c) Facebook, Inc. and its affiliates. All Rights Reserved.
// Original License: https://github.com/facebook/rocksdb/blob/main/LICENSE.Apache
package org.prql.prql4j;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;

public class NativeLibraryLoader {
    //singleton
    private static final NativeLibraryLoader instance = new NativeLibraryLoader();
    private static boolean initialized = false;

    private static final String sharedLibraryName = Environment.getSharedLibraryName("prql_java");
    private static final String jniLibraryName = Environment.getJniLibraryName("prql_java");
    private static final /* @Nullable */ String fallbackJniLibraryName =
            Environment.getFallbackJniLibraryName("prql_java");
    private static final String jniLibraryFileName = Environment.getJniLibraryFileName("prql_java");
    private static final /* @Nullable */ String fallbackJniLibraryFileName =
            Environment.getFallbackJniLibraryFileName("prql_java");
    private static final String tempFilePrefix = "libprql_javajni";
    private static final String tempFileSuffix = Environment.getJniLibraryExtension();

    public static NativeLibraryLoader getInstance() {
        return instance;
    }

    public synchronized void loadLibrary(final String tmpDir) throws IOException {
        try {
            // try dynamic library
            System.loadLibrary(sharedLibraryName);
            return;
        } catch (final UnsatisfiedLinkError ule) {
            // ignore - try from static library
        }

        try {
            // try static library
            System.loadLibrary(jniLibraryName);
            return;
        } catch (final UnsatisfiedLinkError ule) {
            // ignore - then try static library fallback or from jar
        }

        if (fallbackJniLibraryName != null) {
            try {
                // try static library fallback
                System.loadLibrary(fallbackJniLibraryName);
                return;
            } catch (final UnsatisfiedLinkError ule) {
                // ignore - then try from jar
            }
        }

        // try jar
        loadLibraryFromJar(tmpDir);
    }

    void loadLibraryFromJar(final String tmpDir)
            throws IOException {
        if (!initialized) {
            System.load(loadLibraryFromJarToTemp(tmpDir).getAbsolutePath());
            initialized = true;
        }
    }

    File loadLibraryFromJarToTemp(final String tmpDir)
            throws IOException {
        InputStream is = null;
        try {
            // attempt to look up the static library in the jar file
            String libraryFileName = jniLibraryFileName;
            is = getClass().getClassLoader().getResourceAsStream(libraryFileName);

            if (is == null) {
                // is there a fallback we can try
                if (fallbackJniLibraryFileName == null) {
                    throw new RuntimeException(libraryFileName + " was not found inside JAR.");
                }

                // attempt to look up the fallback static library in the jar file
                libraryFileName = fallbackJniLibraryFileName;
                is = getClass().getClassLoader().getResourceAsStream(libraryFileName);
                if (is == null) {
                    throw new RuntimeException(libraryFileName + " was not found inside JAR.");
                }
            }

            // create a temporary file to copy the library to
            final File temp;
            if (tmpDir == null || tmpDir.isEmpty()) {
                temp = File.createTempFile(tempFilePrefix, tempFileSuffix);
            } else {
                final File parentDir = new File(tmpDir);
                if (!parentDir.exists()) {
                    throw new RuntimeException(
                            "Directory: " + parentDir.getAbsolutePath() + " does not exist!");
                }
                temp = new File(parentDir, libraryFileName);
                if (temp.exists() && !temp.delete()) {
                    throw new RuntimeException(
                            "File: " + temp.getAbsolutePath() + " already exists and cannot be removed.");
                }
                if (!temp.createNewFile()) {
                    throw new RuntimeException("File: " + temp.getAbsolutePath() + " could not be created.");
                }
            }
            if (!temp.exists()) {
                throw new RuntimeException("File " + temp.getAbsolutePath() + " does not exist.");
            } else {
                temp.deleteOnExit();
            }

            // copy the library from the Jar file to the temp destination
            Files.copy(is, temp.toPath(), StandardCopyOption.REPLACE_EXISTING);

            // return the temporary library file
            return temp;

        } finally {
            if (is != null) {
                is.close();
            }
        }
    }

    private NativeLibraryLoader() {
    }
}
