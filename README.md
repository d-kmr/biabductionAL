# Biabduction solver for Symbolic Heap Separation Logic with Arrays and Lists

<b>[Contents]</b><br>
<table>
build.sh&#009;          : build script of biabdAL<br>
src/              : source files of biabdAL<br>
testfiles/        : example input files (handwritten)<br>
slactestfiles/    : experimental files for SLAC<br>
</table>
<br>
<b>[Requirements for build biabdAL]</b><br>
- make<br>
- opam (OCaml, ocamlopt, ocamlyacc, ocamllex, ocamlfind, z3-package, ANSITerminal-package)<br>
<br>
<b>[Build]</b><br>
./build.sh<br>
<br>
<b>[Usage]</b><br>
./biabdAL -f FILE [-balimit NUM|-nooutput|-debug]<br>
<br>
<b>[Options]</b><br>
  -balimit NUM  : set limit number of iteration (default: -1 (nolimit))<br>
  -nooutput     : avoid showing solutions (only shows the number of solutions)<br>
  -debug          : show detailed outputs<br>
  


