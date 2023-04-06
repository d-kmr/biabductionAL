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
// solutions: 4
// time: 0.364

(ret@bar!=0)
& (((ret@bar+1)<(t157'@hat+2)) || ((t157'@hat+255)<(ret@bar+1)))
& ((ret@bar+1)!=(t157'@hat+1))
& ((ret@bar+1)!=ret@bar)
& ((ret@bar+1)!=(t159'@hat+6))
& ((ret@bar+1)!=t157'@hat)
& ((ret@bar<t157'@hat) || ((t157'@hat+255)<ret@bar))
& (ret@bar!=(t159'@hat+6))
& (t15'@bar!=0)
& (t157'@hat<=(t157'@hat+255))
& (t164'@tilde==37)
& ((t157'@hat+1)<=(t157'@hat+255))
& (continue@bar==0)
& ((t28'@bar==0) || (t28'@bar==0))
& ((t157'@hat+2)<=(t157'@hat+255))
& ((ret@bar<(t157'@hat+1)) || ((t157'@hat+254)<ret@bar))
& (ret@bar!=t157'@hat)
& (ret@bar!=(t159'@hat+5))
&&
(t152'@hat+47)->(*:0)
* Arr (t152'@hat, (t152'@hat+46))
* Arr (t153'@hat, (t153'@hat+1023))
|-
(ret@bar+1)->(*:t28'@bar)
* Arr (ret@bar, ret@bar)
