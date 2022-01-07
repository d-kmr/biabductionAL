// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// # of terms in Array part: 0
// # of terms in List  part: 5

// limit: none
// # of solutions: 16
// time: 0.565

// limit: 10
// # of solutions: 1
// time: 0.137


Ls(a,b) * Ls(c,d) * Ls(d,a)
|-
Ls(b,c) * Ls(a,x)
