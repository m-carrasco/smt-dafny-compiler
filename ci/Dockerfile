FROM ubuntu:24.04

ARG USER_ID
ARG GROUP_ID

# Modify the existing ubuntu user's UID and GID
RUN groupmod -g $GROUP_ID ubuntu && \
    usermod -u $USER_ID -g $GROUP_ID ubuntu && \
    chown -R $USER_ID:$GROUP_ID /home/ubuntu

RUN apt-get update && apt-get install --no-install-recommends -y sudo 
RUN echo 'ubuntu ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers
USER ubuntu

# Add Microsoft repository for dotnet 6.0
RUN sudo apt-get install --no-install-recommends -y software-properties-common && \
    sudo add-apt-repository ppa:dotnet/backports && \
    sudo apt-get update

RUN sudo apt-get install --no-install-recommends -y dotnet-sdk-8.0 dotnet-sdk-6.0 wget git llvm-dev pip default-jdk make unzip && \
    sudo apt-get clean && \
    sudo rm -rf /var/lib/apt/lists/*

RUN sudo pip install --break-system-packages lit==16.0.5post0 z3-solver==4.11.2
RUN sudo ln -s /usr/bin/FileCheck-18 /usr/local/bin/FileCheck
RUN sudo ln -s /usr/bin/not-18 /usr/local/bin/not 

ENV SDC_FILE_CHECK=/usr/local/bin/FileCheck
ENV SDC_NOT=/usr/local/bin/not
ENV SDC_SRC_DIR="/home/ubuntu/smt-dafny-compiler"
ENV PATH="/home/ubuntu/.local/bin:${PATH}"

ENV DAFNY_SRC_DIR="/home/ubuntu/dafny"
COPY --chown=ubuntu:mygroup external/dafny $DAFNY_SRC_DIR
RUN cd $DAFNY_SRC_DIR && make exe && make z3-ubuntu
ENV SDC_DAFNY="${DAFNY_SRC_DIR}/Scripts/dafny"

RUN mkdir /home/ubuntu/slot
# SLOT is dynamically linked to Z3. 
# Make sure that that the dependency is available and compatible.
COPY --chown=ubuntu:mygroup --from=slot /root/slot /home/ubuntu/slot

COPY --chown=ubuntu:mygroup . ${SDC_SRC_DIR}
WORKDIR $SDC_SRC_DIR
RUN cd src/ && dotnet test && dotnet build
RUN lit -vvv integration-tests/
