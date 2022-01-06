// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// F(p,q,r,s) := a0->(a1*a2->a3*..*a(m-1)->am * Arr() |- ->() * Ls(b0,b1) * .. * Ls(b(n-1),bn)
// F(2,1)

a0 -> (next: a1)
|-
Ls(b0, b1)
