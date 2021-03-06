FROM ubuntu:18.04

MAINTAINER Sebastien Macke <lanjelot@gmail.com>

ENV DEBIAN_FRONTEND=noninteractive 

RUN apt-get update && apt-get install -y python3-dev build-essential libgmp-dev libmpfr-dev libmpc-dev git python3-pip
RUN python3 -m pip install requests pycryptodomex PyCrypto gmpy2

WORKDIR /opt/cryptopal
COPY ./cryptopal.py ./

CMD ["python3", "cryptopal.py", "-v"]
