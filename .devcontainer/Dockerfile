FROM mcr.microsoft.com/devcontainers/base:ubuntu

RUN apt-get update \
    && apt-get install -y --no-install-recommends curl git ca-certificates \
    && rm -rf /var/lib/apt/lists/*

USER vscode

RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain leanprover/lean4:stable

ENV PATH="/home/vscode/.elan/bin:${PATH}"

# elan は toolchain を遅延取得するため、ビルド時に明示的にダウンロードしておく
RUN lean --version
