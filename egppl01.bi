// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// # of terms in Array part: 3
// # of terms in List  part: 0

// limit: none
// # of solutions: 2
// time: 0.154

// limit: 10
// # of solutions: 2
// time: 0.146

Arr(t,b)
|-
Arr(a,b) * Arr(t,t)
