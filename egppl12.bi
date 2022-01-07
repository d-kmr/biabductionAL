// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// egppl02 + egppl07
// # of terms in Array part: 4
// # of terms in List  part: 4

// limit: none
// # of solutions: 110
// time: 3.149

// limit: 10
// # of solutions: 45
// time: 0.706


Arr(a,b) * Ls(a',b') * Ls(c',d') * Ls(d',a')
|-
Arr(x,y) * Ls(b',c')


