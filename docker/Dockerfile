# pyle, as a container: `pyle serve` by default, with the same binary for the
# administrative commands (`docker exec pyle pyle client list`, and so on).
#
# Build context is the repository root:  docker build -f docker/Dockerfile .

# ---- Build ----
# No official Lean image: elan installs exactly the toolchain lean-toolchain
# pins, as `lake` would locally.
FROM debian:bookworm-slim AS build
# `build-essential` for the `cc` that compiles the C shims under ffi/,
# `libssl-dev` for the OpenSSL headers they include.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git build-essential libssl-dev \
    && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/root/.elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
      | sh -s -- -y --no-modify-path --default-toolchain none
WORKDIR /src
COPY lean-toolchain lakefile.lean lake-manifest.json ./
COPY Pyle.lean Main.lean ./
COPY Pyle ./Pyle
COPY ffi ./ffi
# The one executable, not the default targets: neither the test driver nor
# the proofs have a place in the image.  It links the Lean toolchain's own
# static OpenSSL, so OpenSSL fixes reach the image with a toolchain bump rather
# than from apt; libssl-dev above is for the shims' headers.
RUN lake build pyle

# ---- Runtime ----
FROM debian:bookworm-slim AS runtime
# `curl` is for the health check.  No libssl: the binary carries its own.
RUN apt-get update && apt-get install -y --no-install-recommends curl \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/.lake/build/bin/pyle /usr/local/bin/

# The configuration under /pyle/config, the state under /pyle/data: a
# deployment mounts the first read-only and the second as a volume that
# outlives the container.  The configuration names the state by absolute path
# ("database": "/pyle/data/pyle.db", "rootKeyFile": "/pyle/data/root.key") and
# listens on every address of the container ("host": "0.0.0.0").
ENV PYLE_CONFIG=/pyle/config/pyle.json
# An unprivileged account with a fixed uid, so a deployment can own the state
# directory to it.
RUN useradd --system --uid 991 --home-dir /pyle --no-create-home pyle \
    && mkdir -p /pyle/config /pyle/data && chown pyle /pyle/data && chmod 700 /pyle/data
USER pyle
WORKDIR /pyle/data

EXPOSE 8420
VOLUME ["/pyle/data"]

# `/healthz` answers 200 once the database does.  The port is the
# configuration's, 8420 unless it says otherwise.
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s \
  CMD curl -fs -o /dev/null http://127.0.0.1:8420/healthz || exit 1

ENTRYPOINT ["pyle"]
CMD ["serve"]