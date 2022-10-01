FROM gitpod/workspace-full:latest

USER root

ARG DMD_VERSION=2.100.2
ARG DMD_BUILD=$DMD_VERSION-0
RUN wget http://downloads.dlang.org/releases/2.x/$DMD_VERSION/dmd_${DMD_BUILD}_amd64.deb
RUN sudo dpkg -i dmd_${DMD_BUILD}_amd64.deb

USER gitpod
# apply user-specific settings

# give back control
USER root
