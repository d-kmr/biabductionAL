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
// solutions: 2
// time: 0.261

(ret@bar!=0)
& (((ret@bar+1)<(t171'@hat+2)) || ((t171'@hat+255)<(ret@bar+1)))
& ((ret@bar+1)!=(t171'@hat+1))
& ((ret@bar+1)!=ret@bar)
& ((ret@bar+1)!=(t173'@hat+6))
& ((ret@bar+1)!=t171'@hat)
& ((ret@bar<t171'@hat) || ((t171'@hat+255)<ret@bar))
& (ret@bar!=(t173'@hat+6))
& (t15'@bar!=0)
& (t171'@hat<=(t171'@hat+255))
& (t178'@tilde!=37)
& ((t171'@hat+1)<=(t171'@hat+255))
& (continue@bar==0)
& ((t90'@bar==0) || (t90'@bar==0))
& ((t171'@hat+2)<=(t171'@hat+255))
& ((ret@bar<(t171'@hat+1)) || ((t171'@hat+254)<ret@bar))
& (ret@bar!=t171'@hat)
& (ret@bar!=(t173'@hat+5))
&&
(t152'@hat+47)->(*:0)
* Arr (t152'@hat, (t152'@hat+46))
* Arr (t153'@hat, (t153'@hat+1023))
|-
(ret@bar+1)->(*:t90'@bar)
* Arr (ret@bar, ret@bar)