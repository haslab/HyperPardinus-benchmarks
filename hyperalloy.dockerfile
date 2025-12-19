FROM hyperalloy/hypercheckers
USER root

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ENV PATH /root/.ghcup/bin/:/root/.cabal/bin/:${PATH}
RUN apt update && apt install -y libgmp3-dev

# install HyperSmv

COPY . /
RUN cd /HyperSMV && cabal install hypersmv.cabal --overwrite-policy=always --ghc-options="-O2"

# install electrod

RUN apt-get install -y autoconf
RUN apt-get install -y opam
RUN opam init --disable-sandboxing
RUN eval $(opam env)
RUN opam update
RUN cd /HyperPardinus/electrod && make setup && make release
RUN cp /HyperPardinus/electrod/electrod.exe /HyperPardinus/electrod/electrod
ENV PATH=/HyperPardinus/electrod:${PATH}

# install HyperAlloy

RUN apt-get update && apt-get install -y openjdk-17-jre vim

RUN cd /HyperPardinus && ./gradlew clean build -x test  
ENV PATH=/HyperPardinus:${PATH}

# install nuxmv

RUN apt install -y qemu-user qemu-user-static binfmt-support
RUN wget -O nuXmv.tar.xz https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.1.0-linux64.tar.xz && tar -xvf nuXmv.tar.xz nuXmv-2.1.0-linux64/ && rm -rf nuXmv.tar.xz
COPY nuXmv/nuXmv /root/usr/bin/nuXmv
COPY hyperalloy /root/usr/bin/hyperalloy

# set up benchmarks 

RUN pip install fire

CMD hyperalloy



