// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// # of terms in Array part: 6
// # of terms in List  part: 0

// limit: none
// # of solutions: 31
// time: 21.838

// limit: 10
// # of solutions: 6
// time: 0.361

Arr(a,b) * Arr(c,d)
|-
Arr(a,c) * Arr(x,y)
