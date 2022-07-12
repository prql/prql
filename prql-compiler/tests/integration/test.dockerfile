FROM ubuntu

# insert pre-built test binary & tests
COPY test .
COPY src/ src/

# also insert chinook database
COPY chinook.db .
COPY chinook/ .

ENTRYPOINT test
