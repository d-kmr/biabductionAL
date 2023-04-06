# Biabduction solver for Symbolic Heap Separation Logic with Arrays and Lists

<b>[Contents]</b><br>
build.sh          : build script of biabdAL
src/              : source files of biabdAL
egppl??.bi        : example input files (handwritten)<br>


<b>[Requirements for biabdAL]</b><br>
- Ubuntu family OS (Ubuntu, Linux Mint, etc)<br>
- dependencies: linux-vdso, libstdc++, libgmp, libpthread, libm, libdl, libgcc_s, libc<br>
<br>
<br>
<b>[Build]</b><br>
./build.sh<br>
<br>
<br>
<b>[Usage]</b><br>
./biabdAL -f FILE [-balimit NUM|-nooutput|-debug]<br>
<br>
<b>[Options]</b><br>
  -balimit NUM  : set limit number of iteration (default: -1 (nolimit))<br>
  -nooutput     : avoid showing solutions (only shows the number of solutions)<br>
  -debug          : show detailed outputs<br>
  


