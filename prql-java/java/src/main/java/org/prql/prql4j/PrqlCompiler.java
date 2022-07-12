package org.prql.prql4j;

import java.io.IOException;

public class PrqlCompiler {
    public static native String toSql(String query);
    public static native String toJson(String query);

    static {
        try {
            NativeLibraryLoader.getInstance().loadLibrary(null);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
