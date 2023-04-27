FROM ubuntu:23.04

# Install dependencies
RUN apt-get update -y && \
    apt-get install -y --no-install-recommends \
        ca-certificates \
        elan \
        git \
        && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Install Lean
COPY lean-toolchain /
RUN elan default "$(cat /lean-toolchain)" && rm /lean-toolchain
