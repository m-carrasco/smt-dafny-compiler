FROM ubuntu:22.04

ARG USER_ID
ARG GROUP_ID

# Create a new group and user with the specified IDs
RUN groupadd -g $GROUP_ID mygroup && \
    useradd -u $USER_ID -g $GROUP_ID -m -d /home/ubuntu ubuntu

RUN apt-get update && apt-get install --no-install-recommends -y sudo
RUN echo 'ubuntu ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers
RUN chown -R ubuntu:mygroup /home/ubuntu
USER ubuntu

RUN sudo apt-get install --no-install-recommends -y dotnet-sdk-8.0 dotnet-sdk-6.0 git llvm-dev pip default-jdk wget make unzip
RUN sudo pip install lit==16.0.5post0
RUN sudo ln -s /usr/bin/FileCheck-14 /usr/local/bin/FileCheck
RUN sudo ln -s /usr/bin/not-14 /usr/local/bin/not 

ENV SDC_FILE_CHECK=/usr/local/bin/FileCheck
ENV SDC_NOT=/usr/local/bin/not
ENV SDC_SRC_DIR="/home/ubuntu/smt-dafny-compiler"
ENV PATH="/home/ubuntu/.local/bin:${PATH}"

ENV DAFNY_SRC_DIR="/home/ubuntu/dafny"
COPY --chown=ubuntu:mygroup external/dafny $DAFNY_SRC_DIR
RUN cd $DAFNY_SRC_DIR && make exe && make z3-ubuntu
ENV SDC_DAFNY="${DAFNY_SRC_DIR}/Scripts/dafny"

COPY --chown=ubuntu:mygroup . ${SDC_SRC_DIR}

WORKDIR $SDC_SRC_DIR
RUN cd src/ && dotnet test && dotnet build
