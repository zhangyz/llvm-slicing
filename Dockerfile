FROM ubuntu:trusty
MAINTAINER Zhang Yingzhou <zhangyz@njupt.edu.cn>

RUN apt-get update && \
    apt-get -y install clang-3.3 llvm-3.3 llvm-3.3-dev llvm-3.3-runtime graphviz && \
    rm -rf /var/lib/apt/lists/* && \
    cp /usr/bin/opt-3.3 /usr/local/bin/opt
    
ADD /bin/llvm-slicing_llvm-3.3_x86-64_Ubuntu-12.04.2.tar.bz2 /usr/local/bin 

CMD ["llvm-slicing", "-h"]
