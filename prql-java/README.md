# prql-java

`prql-java` offers rust bindings to the `prql-compiler` rust library. It
exposes a java native method `public static native String toSql(String query)`.

## Installation

```xml
<dependency>
    <groupId>org.prqllang</groupId>
    <artifactId>prql-java</artifactId>
    <version>${PRQL_VERSION}</version>
</dependency>
```

## Usage

```java
import org.prqllang.prql4j.PrqlCompiler;

class Main {
    public static void main(String[] args) {
        String sql = PrqlCompiler.toSql("from table");
        System.out.println(sql);
    }
}
```
