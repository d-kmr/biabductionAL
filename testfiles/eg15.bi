// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// egppl05 + egppl10
// # of terms in Array part: 7
// # of terms in List  part: 7

Arr(a,b) * Arr(c,d) * Arr(z,z) * Ls(a',b') * Ls(c',d') * Ls(e',a')
|-
Arr(a,c) * Arr(x,y) * Ls(b',c') * Ls(x',y')
