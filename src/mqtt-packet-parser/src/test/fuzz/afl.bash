CC=/root/afl-2.52b/afl-gcc
HOME=/root/verimqtt/src/mqtt-packet-parser
SRC=$HOME/src
OUT=$HOME/out
KREMLIB=/root/kremlin/kremlib
INCLUDE=/root/kremlin/include

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Const.c -o $OUT/Const.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Common.c -o $OUT/Common.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Debug.c -o $OUT/Debug.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Disconnect.c -o $OUT/Disconnect.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Publish.c -o $OUT/Publish.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Connect.c -o $OUT/Connect.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/Main.c -o $OUT/Main.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $OUT/kremlinit.c -o $OUT/kremlinit.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $SRC/debug_ffi.c -o $OUT/debug_ffi.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $SRC/ffi.c -o $OUT/ffi.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 -c $SRC/callMain.c -o $OUT/callMain.o

$CC -I $KREMLIB -I $INCLUDE -I $OUT -Wall -Werror -Wno-unused-variable -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE -D_DEFAULT_SOURCE -Wno-parentheses -std=c11 $OUT/Const.o $OUT/Common.o $OUT/Debug.o $OUT/Disconnect.o $OUT/Publish.o $OUT/Connect.o $OUT/Main.o $OUT/kremlinit.o $OUT/debug_ffi.o $OUT/ffi.o $OUT/callMain.o $KREMLIB/dist/generic/libkremlib.a -o ./mqttPacketParser.out