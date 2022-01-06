// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// egppl04 + egppl09
// # of terms in Array part: 6
// # of terms in List  part: 6
// # of solutions: 416
// time: 64.38

Arr(a,b) * Arr(c,d) * Ls(a',b') * Ls(c',d') * Ls(d',a')
|-
Arr(a,c) * Arr(x,y) * Ls(b',c') * Ls(x',y')
