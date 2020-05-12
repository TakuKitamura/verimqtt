all:
	make -C src/mqtt-packet-parser compile && pushd src/mqtt-base && cargo run && popd
compile:
	make -C src/mqtt-packet-parser compile
server:
	pushd src/mqtt-base && cargo run && popd