// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// # of terms in Array part: 0
// # of terms in List  part: 6

// limit: none
// # of solutions: 26
// time: 3.995

// limit: 10
// # of solutions: 4
// time: 0.146


Ls(a,b) * Ls(c,d) * Ls(d,a)
|-
Ls(b,c) * Ls(x,y)