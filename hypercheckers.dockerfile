FROM hyperalloy/pynusmv
USER root

RUN apt-get update && apt-get install -y wget git

# install AutoHyper dependencies

RUN apt-get install -y dotnet-sdk-8.0
RUN wget http://www.lrde.epita.fr/dload/spot/spot-2.13.tar.gz
RUN tar -xvf spot-2.13.tar.gz spot-2.13/
RUN apt-get install -y build-essential
RUN cd spot-2.13 && ./configure --prefix ~/usr && make && make install && cd .. && rm -rf spot-2.13 && rm -rf spot-2.13.tar.gz
COPY AutoHyper/app/bait.jar /root/usr/bin/bait.jar
COPY AutoHyper/app/rabit.jar /root/usr/bin/rabit.jar
COPY AutoHyper/app/forklift.jar /root/usr/bin/forklift.jar
COPY AutoHyper/app/roll.jar /root/usr/bin/roll.jar
ENV PATH /root/usr/bin/:${PATH}

RUN apt-get update && apt-get install -y python3
ENV PYTHONPATH=/root/usr/lib/python3.10/site-packages/

# install AutoHyper
COPY AutoHyper /AutoHyper
RUN cd AutoHyper && cd src/AutoHyper && dotnet build -c "release" -o ../../app -p:DOTNET_VERSION=net8
COPY AutoHyper/app/paths.json /AutoHyper/app/paths.json
ENV PATH /AutoHyper/app:${PATH}

# install HyperQB dependencies
RUN apt-get update && apt-get install -y cmake zlib1g-dev
RUN git clone --recursive --depth=1 https://github.com/ltentrup/quabs
RUN cd quabs && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE=Release .. && make
ENV PATH /quabs/build:${PATH}

# install HyperQB
RUN git clone --recursive --depth=1 https://github.com/TART-MSU/HyperQB
RUN apt-get install -y ocaml ocamlbuild
RUN ln -s /usr/bin/ocamlbuild /usr/bin/ocamlbuild.native
RUN cd HyperQB && cd src/expression/ && make && cp bin/genqbf ../../exec/genqbf_partialmulti && make clean
RUN cd HyperQB/src/cplusplus && rm genqbf && ./build.sh
COPY hyperqb/parser.py /HyperQB/exec/parser.py
COPY hyperqb/hyperqb /HyperQB/hyperqb
RUN chmod +x /HyperQB/hyperqb
ENV PATH /HyperQB:${PATH}
COPY hyperqb/genqbfv5 /HyperQB/src/genqbfv5
RUN cd HyperQB && cd src/genqbfv5/ && make && cp bin/genqbf ../../exec/genqbf_v5  && make clean

# additional QBF solvers

RUN git clone --recursive --depth=1 https://github.com/MikolasJanota/cqesto
RUN cd cqesto && ./configure && cd build && make
ENV PATH /cqesto/build:${PATH}

RUN git clone --recursive --depth=1 https://github.com/MikolasJanota/qfun
RUN cd qfun && sed -i '1s/.*/cmake_minimum_required(VERSION 3.22)/' CMakeLists.txt && ./configure && cd build && make
ENV PATH /qfun/build:${PATH}

RUN git clone --recursive --depth=1 https://github.com/fslivovsky/qute
RUN cd qute && mkdir build && cd build && cmake .. && make
ENV PATH /qute:${PATH}

# benchmarking
RUN apt update && apt-get install -y linux-tools-common linux-tools-generic
RUN cp /usr/lib/linux-tools/*-generic/perf /usr/bin/perf








