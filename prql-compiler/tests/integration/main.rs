// Re-enable on windows when duckdb supports it
// https://github.com/wangfenjin/duckdb-rs/issues/62
#![cfg(not(any(target_family = "windows", target_family = "wasm")))]

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use insta::{assert_snapshot, glob};

    #[test]
    fn test() {
        // TODO: we could have a trait rather than mods for each of these?
        let mut pg_client = postgres::connect();
        let duckdb_conn = duckdb::connect();
        let sqlite_conn = sqlite::connect();

        // for each of the queries
        glob!("queries/**/*.prql", |path| {
            // read
            let prql = fs::read_to_string(path).unwrap();

            if prql.contains("skip_test") {
                return;
            }

            // compile
            let sql = prql_compiler::compile(&prql).unwrap();

            // save both csv files as same snapshot
            assert_snapshot!("", sqlite::query_csv(&sqlite_conn, &sql));
            assert_snapshot!("", duckdb::query_csv(&duckdb_conn, &sql));

            if let Some(pg_client) = &mut pg_client {
                assert_snapshot!("", postgres::query_csv(pg_client, &sql));
            }
        });
    }

    /// Return a path relative to the root `integration` path.
    fn path(relative_path: &str) -> String {
        // Insired by insta's approach to finding a file in a test path.
        let root = env!("CARGO_MANIFEST_DIR");
        Path::new(root)
            .join("tests/integration")
            .join(relative_path)
            .canonicalize()
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned()
    }

    fn load_schema() -> String {
        fs::read_to_string(path("data/chinook/schema.sql")).unwrap()
    }

    mod sqlite {
        use super::path;
        use rusqlite::{types::ValueRef, Connection};

        pub fn connect() -> Connection {
            Connection::open(path("data/chinook/chinook.db")).unwrap()
        }

        pub fn query_csv(conn: &Connection, sql: &str) -> String {
            let mut statement = conn.prepare(sql).unwrap();

            let csv_header = statement.column_names().join(",");
            let column_count = statement.column_count();

            let csv_rows = statement
                .query_map([], |row| {
                    Ok((0..column_count)
                        .map(|i| match row.get_ref_unwrap(i) {
                            ValueRef::Null => "".to_string(),
                            ValueRef::Integer(i) => i.to_string(),
                            ValueRef::Real(r) => r.to_string(),
                            ValueRef::Text(t) => String::from_utf8_lossy(t).to_string(),
                            ValueRef::Blob(_) => unimplemented!(),
                        })
                        .collect::<Vec<_>>()
                        .join(","))
                })
                .unwrap()
                .into_iter()
                .take(100) // truncate to 100 rows
                .map(|r| r.unwrap())
                .collect::<Vec<String>>()
                .join("\n");

            csv_header + "\n" + &csv_rows
        }
    }

    mod duckdb {
        use chrono::{DateTime, Utc};
        use duckdb::{types::FromSql, types::ValueRef, Connection};

        use super::load_schema;
        use super::path;

        pub fn connect() -> Connection {
            let conn = Connection::open_in_memory().unwrap();
            let schema = load_schema();
            conn.execute_batch(&schema).unwrap();
            let root = path("");
            conn.execute_batch(format!(
                "
                COPY invoices FROM '{root}/data/chinook/invoices.csv' (AUTO_DETECT TRUE);
                COPY customers FROM '{root}/data/chinook/customers.csv' (AUTO_DETECT TRUE);
                COPY employees FROM '{root}/data/chinook/employees.csv' (AUTO_DETECT TRUE);
                COPY tracks FROM '{root}/data/chinook/tracks.csv' (AUTO_DETECT TRUE);
                COPY albums FROM '{root}/data/chinook/albums.csv' (AUTO_DETECT TRUE);
                COPY genres FROM '{root}/data/chinook/genres.csv' (AUTO_DETECT TRUE);
                COPY playlist_track FROM '{root}/data/chinook/playlist_track.csv' (AUTO_DETECT TRUE);
                COPY playlists FROM '{root}/data/chinook/playlists.csv' (AUTO_DETECT TRUE);
                COPY media_types FROM '{root}/data/chinook/media_types.csv' (AUTO_DETECT TRUE);
                COPY artists FROM '{root}/data/chinook/artists.csv' (AUTO_DETECT TRUE);
                COPY invoice_items FROM '{root}/data/chinook/invoice_items.csv' (AUTO_DETECT TRUE);
            ")
            .as_str()).unwrap();

            conn
        }

        pub fn query_csv(conn: &Connection, sql: &str) -> String {
            let mut statement = conn.prepare(sql).unwrap();

            // execute here so number of columns is known before we start parsing it
            statement.execute([]).unwrap();

            let csv_header = statement.column_names().join(",");
            let column_count = statement.column_count();

            let csv_rows = statement
                .query_map([], |row| {
                    Ok((0..column_count)
                        .map(|i| {
                            let value = row.get_ref_unwrap(i);
                            match value {
                                ValueRef::Null => "".to_string(),
                                ValueRef::Int(i) => i.to_string(),
                                ValueRef::TinyInt(i) => i.to_string(),
                                ValueRef::HugeInt(i) => i.to_string(),
                                ValueRef::BigInt(i) => i.to_string(),
                                ValueRef::Float(r) => r.to_string(),
                                ValueRef::Double(r) => r.to_string(),
                                ValueRef::Text(t) => String::from_utf8_lossy(t).to_string(),
                                ValueRef::Timestamp(_, _) => {
                                    let dt = DateTime::<Utc>::column_result(value).unwrap();
                                    dt.format("%Y-%m-%d %H:%M:%S").to_string()
                                }
                                t => unimplemented!("{t:?}"),
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(","))
                })
                .unwrap()
                .into_iter()
                .take(100) // truncate to 100 rows
                .map(|r| r.unwrap())
                .collect::<Vec<String>>()
                .join("\n");

            csv_header + "\n" + &csv_rows
        }
    }

    mod postgres {
        use std::time::SystemTime;

        use chrono::{DateTime, Utc};
        use postgres::types::{FromSql, Type};
        use postgres::{Client, NoTls, Row};

        pub fn connect() -> Option<Client> {
            let host = std::env::var("POSTGRES_HOST").ok()?;

            let client = Client::connect(&format!("host={} user=postgres", host), NoTls).unwrap();

            Some(client)
        }

        pub fn query_csv(client: &mut Client, sql: &str) -> String {
            let statement = client.prepare(sql).unwrap();

            let csv_header = statement
                .columns()
                .iter()
                .map(|c| c.name())
                .take(100) // truncate to 100 rows
                .collect::<Vec<_>>()
                .join(",");

            let rows = client.query(&statement, &[]).unwrap();

            fn get<'a, T: ToString + FromSql<'a>>(row: &'a Row, idx: usize) -> String {
                row.get::<usize, Option<T>>(idx)
                    .map(|v| v.to_string())
                    .unwrap_or_default()
            }

            let mut csv_rows = vec![csv_header];
            for row in rows.into_iter().take(100) {
                csv_rows.push(
                    (0..row.len())
                        .map(|i| match row.columns()[i].type_() {
                            &Type::BOOL => get::<bool>(&row, i),
                            &Type::INT2 => get::<i16>(&row, i),
                            &Type::INT4 => get::<i32>(&row, i),
                            &Type::INT8 => get::<i64>(&row, i),
                            &Type::TEXT | &Type::VARCHAR => get::<String>(&row, i),
                            &Type::JSON | &Type::JSONB => get::<String>(&row, i),
                            &Type::FLOAT4 => get::<f32>(&row, i),
                            &Type::FLOAT8 => get::<f32>(&row, i),
                            &Type::TIMESTAMPTZ | &Type::TIMESTAMP => get::<Timestamp>(&row, i),
                            t => unimplemented!("postgres type {t}"),
                        })
                        .collect::<Vec<_>>()
                        .join(","),
                );
            }

            csv_rows.join("\n")
        }

        struct Timestamp(SystemTime);
        impl<'a> FromSql<'a> for Timestamp {
            fn from_sql(
                ty: &Type,
                raw: &'a [u8],
            ) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
                SystemTime::from_sql(ty, raw).map(Timestamp)
            }

            fn accepts(ty: &Type) -> bool {
                SystemTime::accepts(ty)
            }
        }
        impl ToString for Timestamp {
            fn to_string(&self) -> String {
                let dt = DateTime::<Utc>::from(self.0);
                dt.format("%Y-%m-%d %H:%M:%S").to_string()
            }
        }
    }
}
