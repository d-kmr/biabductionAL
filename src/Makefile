TARGET=biabdAL
PARSER=slsyntax_parser_entl
LEXER=slsyntax_lexer_entl
CMXS=tools.cmx ftools.cmx slsyntax.cmx $(PARSER).cmx $(LEXER).cmx smtsyntax.cmx

all:
	ocamlfind ocamlopt -package ANSITerminal -c tools.ml ftools.ml slsyntax.ml smtsyntax.ml 
	ocamllex $(LEXER).mll
	ocamlyacc $(PARSER).mly
	ocamlopt -c $(PARSER).mli
	ocamlopt -c $(LEXER).ml
	ocamlopt -c $(PARSER).ml
	ocamlfind ocamlopt -o $(TARGET) -package z3,ANSITerminal -thread -linkpkg $(CMXS) smttoz3.ml sltosmt.ml satcheck.ml biabdData.ml biabdLs.ml biabdArr.ml biabd.ml biabd_main.ml

clean:
	rm -f *.cmo *.cmi *.cmx *.mli *.o *~
