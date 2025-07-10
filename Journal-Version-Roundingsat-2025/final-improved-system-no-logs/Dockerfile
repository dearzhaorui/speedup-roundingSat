FROM alpine:latest

# Install dependencies
RUN apk update
RUN apk add git g++ cmake make boost-dev wget

# Compile RoundingSAT
RUN git clone https://gitlab.com/MIAOresearch/software/roundingsat.git
WORKDIR /roundingsat/build
RUN cmake -DCMAKE_BUILD_TYPE=Release -Dsoplex=ON ..
RUN make

# Provide RoundingSAT executable as executable to call when starting container
# CMD [ "/roundingsat/build/roundingsat" ]
ENTRYPOINT [ "/roundingsat/build/roundingsat" ]
