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
// solutions: NoAnswer
// time: 0.053


(t667'@bar!=s@bar)
& (t668'@bar<=1073741824)
& (t668'@bar<=1073741824)
& (1073741824<t669'@bar)
&&
t667'@bar->(next_in:t666'@bar, avail_in:t668'@bar, total_in:t670'@bar, next_out:t672'@bar, avail_out:t676'@tilde, total_out:t671'@bar, msg:t678'@tilde, state:t679'@tilde, zalloc:t680'@tilde, zfree:t681'@tilde, opaque:t682'@tilde, data_type:t683'@tilde, adler:t684'@tilde, reserved:t685'@tilde)
* s@bar->(z:t667'@bar, avail_in:t668'@bar, avail_out:t669'@bar, total_in:t670'@bar, total_out:t671'@bar, next_in:t666'@bar, next_out:t672'@bar)
|-
Emp
