FROM ubuntu:22.04
USER root

RUN apt-get update && apt-get install -y wget curl git

# Required to build NuSMV
RUN apt-get -y install build-essential
RUN apt-get -y install zip
RUN apt-get -y install flex bison
RUN apt-get -y install zlib1g-dev
RUN apt-get -y install libexpat-dev

# Required for PyNuSMV
RUN apt-get -y install python3 python3-dev libpython3-dev
RUN apt-get -y install python3-pip
RUN apt-get -y install swig
RUN apt-get -y install patchelf

RUN pip3 install --upgrade pip
RUN pip3 install setuptools

#RUN git clone --recursive --depth=1 https://github.com/davidebreso/pynusmv
COPY pynusmv /pynusmv

RUN cd pynusmv && python3 setup.py install