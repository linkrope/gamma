FROM gitpod/workspace-full:latest

USER root

ARG DMD_VERSION=2.100.2
ARG DMD_BUILD=dmd_${DMD_VERSION}-0_amd64.deb
RUN wget http://downloads.dlang.org/releases/2.x/$DMD_VERSION/$DMD_BUILD
RUN sudo dpkg -i $DMD_BUILD

USER gitpod
# apply user-specific settings

# give back control
USER root
