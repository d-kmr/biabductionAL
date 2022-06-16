// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// egppl01 + egppl06
// # of terms in Array part: 3
// # of terms in List  part: 3

// limit: none
// # of solutions: 10
// time: 0.291

// limit: 10
// # of solutions: 10
// time: 0.245


Arr(t,b) * Ls(a',b') * Ls(c',a')
|-
Arr(a,b) * Arr(t,t) * Ls(b',c')


