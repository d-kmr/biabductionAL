// Syntax
// (term)      t := <string> | <int> | t "+" t
// (pure atom) p := t "=" t | t "<>" t | t "<" t | t "<=" t | t ">" t | t ">=" t | "True" | "False" | (P)
// (pure)      P := p | P "&" P | P "|" P | "All" <string>(',' <string>)* P | "Ex" <string>(',' <string>)* P
// (spat atom) s := "Emp" | t "->(*:" t ")" | "Arr(" t "," t ")" | "Ls(" t "," t ")"
// (spat)      S := s | S "*" S
// (symb.heap) SH := P "&&" S
// (biabd.query) e := SH "|-" S

// biabduction example from our program analyzer

// limit: none
// solutions: 11
// time: 1.492

// limit: 10
// solutions: 5
// time: 0.573


(t960'@hat+21)->(*:0)
* (t959'@hat+10)->(*:0)
* (t958'@hat+6)->(*:0)
* Arr (t960'@hat, (t960'@hat+20))
* Arr (t959'@hat, (t959'@hat+9))
* Arr (t958'@hat, (t958'@hat+5))
|-
Arr (strm@bar, (strm@bar+(1-1)))