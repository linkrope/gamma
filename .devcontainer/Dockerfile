FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

RUN apt-get update \
    && apt-get install --no-install-recommends --yes \
        build-essential \
        ca-certificates \
        curl \
        unzip \
        xz-utils \
    && rm -rf /var/lib/apt/lists/*

USER vscode

RUN curl --fail --location --silent --show-error https://dlang.org/install.sh | bash -s ldc-1.41.0

ENV DLANG_HOME=/home/vscode/dlang
ENV PATH=${DLANG_HOME}/ldc-1.41.0/bin:${PATH}
ENV LIBRARY_PATH=${DLANG_HOME}/ldc-1.41.0/lib
ENV LD_LIBRARY_PATH=${DLANG_HOME}/ldc-1.41.0/lib
ENV DC=ldc2
