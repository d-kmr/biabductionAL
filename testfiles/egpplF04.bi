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
// solutions: 1
// time: 0.066

(t12'@bar!=s@bar)
& (t12'@bar!=(t5'@hat+22))
& (t12'@bar!=(t4'@hat+23))
& (s@bar!=(t5'@hat+22))
& (s@bar!=(t4'@hat+23))
& (t23'@bar==(t16'@bar+(t21'@bar-t17'@bar)))
& (t20'@bar!=(t15'@bar+(t18'@bar-t11'@bar)))
& (ret@bar!=0)
&&
(t4'@hat+23)->(*:0)
* (t5'@hat+22)->(*:0)
* s@bar->(z:t12'@bar, avail_in:t13'@bar, avail_out:t14'@bar, total_in:t15'@bar, total_out:t16'@bar, next_in:t11'@bar, next_out:t17'@bar)
* t12'@bar->(next_in:t18'@bar, avail_in:t19'@bar, total_in:t20'@bar, next_out:t21'@bar, avail_out:t22'@bar, total_out:t23'@bar, msg:t24'@bar, state:t25'@bar, zalloc:t26'@bar, zfree:t27'@bar, opaque:t28'@bar, data_type:t29'@bar, adler:t30'@bar, reserved:t31'@bar)
* Arr (t4'@hat, (t4'@hat+22))
* Arr (t5'@hat, (t5'@hat+21))
|-
Emp
