
# old apprach: dump to .sql and read with postgres
# problem was incompatible SQL syntax and forward table referencing

# FROM alpine:3.16.0 as sqlite
# RUN apk add sqlite sed

# COPY chinook.db .
# RUN sqlite3 chinook.db .dump > chinook.sql

# remove the PRAGMA line
# RUN sed -i 's/^PRAGMA foreign_keys=OFF;$//' chinook.sql
# RUN sed -i 's/INTEGER PRIMARY KEY AUTOINCREMENT/SERIAL PRIMARY KEY/g' chinook.sql
# RUN sed -i 's/NVARCHAR/VARCHAR/g' chinook.sql
# RUN sed -i 's/BEGIN TRANSACTION;/BEGIN TRANSACTION;SET CONSTRAINTS ALL DEFERRED;/g' chinook.sql

# place the .sql to be run after postgres initdb
# COPY chinook.db /docker-entrypoint-initdb.d/chinook.sql

FROM postgres:14.4

# install pgloader
RUN apt-get update && apt-get install -y pgloader

# allow password-less logins
ENV POSTGRES_HOST_AUTH_METHOD=trust

COPY /data/chinook.db /
RUN echo "pgloader /chinook.db postgresql://postgres:pass@unix:/var/run/postgresql:/postgres" > /docker-entrypoint-initdb.d/load-chinook.sh
