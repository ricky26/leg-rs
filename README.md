Leg is an ARM THUMB emulator written in Rust.

Designed to be embedded in other software, leg comes as a crate and with a binary which can be used to test the emulator (also called `leg`).

### Status
Some things work (at least a little bit).

### Building code for Leg
Leg currently only accepts a chunk of THUMB-2 instructions - you can use the Android NDK, which contains compilers, linkers and GDB for ARM processors.

An example makefile might look like so:
```makefile
CFLAGS=-mthumb -nodefaultlibs -nostartfiles -fPIE -Wl,-Tldscript -g -DLEG

all: start

a.out: main.c
	arm-linux-androideabi-gcc $(CFLAGS) main.c

start: a.out
	arm-linux-androideabi-objcopy -O binary a.out start

.PHONY: disasm
disasm: start
	arm-linux-androideabi-objdump -marm -Mforce-thumb -b binary -D start

```

You can then run this with `cargo run leg -- -p -g 0.0.0.0:8084 start`, which will pause at startup and listen for GDB connections on `0.0.0.0:8084`.