\ unsigned natural numbers of dynamical length in 32+ bit ANS Forth
\ 2015 ver 2.1
\ started by Lars-Erik Svahn, Sweden
\ I appreciate enhancements and other feedback
\ lehs@hotmail.se 
\ forthmath.blogspot.se

: ?undef ( -- flag ) bl word find nip 0= ; 
\ flag is true if word undefined 

base @ hex

\ miscellanous

: 0! 0 swap ! ;
: 1+! 1 swap +! ;
: u2/ 1 rshift ;
?undef u/ [if] : u/ 0 swap um/mod nip ; [then]
?undef umod [if] : umod 0 swap um/mod drop ; [then]
?undef cell- [if] : cell- cell - ; [then]
?undef rdrop [if] : rdrop r> drop ; [then]
?undef .r [if] : .r >r 0 <# #S #> r> over - spaces type ; [then]
?undef s>f [if] : s>f s>d d>f ; [then]
?undef f>s [if] : f>s f>d d>s ; [then]

: d256*  \ ud -- 256ud
  over 8 lshift rot 0FF000000 and 018 rshift
  rot 8 lshift or ;

: sqrtf \ m -- n       floor
  0 d>f fsqrt f>s ;

: sqrtc \ m -- n	ceiling
  1- sqrtf 1+ ;

0400 constant 1k
0800 constant 2k
cell negate constant -cell

: log~ \ n -- #binary digits 
  0 swap begin swap 1+ swap u2/ ?dup 0= until ;

    8 cell * constant bits
     bits 1- constant bits-1
 bits-1 log~ constant lbits
cell log~ 1- constant lcell

: 2/mod \ n -- r q
  dup 1 and swap u2/ ;

: 4/mod \ n -- r q
  dup 3 and swap 2 rshift ;

: 8/mod \ n -- r q
  dup 7 and swap 3 rshift ;

: bits/mod \ n -- r q
  dup bits-1 and swap lbits rshift ;

: 256/mod \ n -- r q
  dup 0FF and swap 8 rshift ;

\ extra stacks for singel numbers

: clst ( ad -- )  dup ! ;
: stdrops ( m ad -- )  swap cells negate swap +! ; 
: stdrop ( ad -- ) -cell swap +! ;
: >st ( n ad -- )  cell over +! @ ! ;
: st> ( ad -- n )  dup @ @ -cell rot +! ;
: >st> ( n ad -- m )  dup @ @ -rot @ ! ;
: st@ ( ad -- n )  @ @ ;
: st! ( n ad -- )  @ ! ;
: st+! ( n ad -- )  @ +! ;
: stpick ( m ad -- xm )  @ swap cells - @ ;
: stpatch ( n m ad -- )  @ swap cells - ! ;
: stpatad ( n m ad -- )  @ swap cells - +! ;
: stdepth ( ad -- n )  dup @ swap - lcell rshift ;

: .st \ ad -- 
  dup @ cell+ swap cell+
  ?do i @ . cell
  +loop ;

: >st# \ xn ... x1 n ad -- 
  swap 0
  ?do cell over +! swap over @ !
  loop drop ;

: stack \ size -- 
  allocate throw dup constant clst ;

2k stack xs

: >xs ( n -- )  xs >st ;
: xs> ( -- n )  xs st> ;
: >xs> ( m -- n)  xs >st> ;
: xs@ ( -- n )  xs st@ ;
: xs! ( n -- )  xs st! ;
: xs+! ( n -- )  xs st+! ; 
: xsdrop ( -- )  xs stdrop ; 
: xsdepth ( -- #bytes )  xs stdepth ;

2k stack ys 

: >ys ( n -- )  ys >st ;
: ys> ( -- n )  ys st> ;
: >ys> ( m -- n)  ys >st> ;
: ys@ ( -- n )  ys st@ ;
: ys! ( n -- )  ys st! ;
: ys+! ( n -- )  ys st+! ; 
: ysdrop ( -- )  ys stdrop ; 
: ysdepth ( -- n )  ys stdepth ;

2k stack zs 

: >zs ( n -- )  zs >st ;
: zs> ( -- n )  zs st> ;
: >zs> ( m -- n)  zs >st> ;
: zs@ ( -- n )  zs st@ ;
: zs! ( n -- )  zs st! ;
: zs+! ( n -- )  zs st+! ; 
: zsdrop ( -- )  zs stdrop ; 
: zsdepth ( -- n )  zs stdepth ;

: drop-all ( -- )  xsdrop ysdrop zsdrop ;

\ pseudo random numbers

  variable rnd 

: reset_seed 0ABCDEF1 rnd ! ; reset_seed

: rand \ -- u
  rnd @ 08088405 * 1+ dup rnd ! ;

: random \ u1 -- u2
  rand um* nip ;
  

\ big integers based on cell "digits"

\ main stack
\ pointer stack in high mem towards low mem
\ array stack in low mem towards high mem

0A000 constant maxv
maxv cell + allocate throw aligned constant v$0
v$0 maxv + constant b0
variable bvp

\ extra stack
08000 constant maxx
maxx cell + allocate throw aligned constant x$0
x$0 maxx + constant x0
variable xp

\ extra pad
02000 dup allocate throw constant pad1 
pad1 + cell - constant pad2

: rez \ a n -- a' n'	delete leading zero ascii 48
  dup 1 =
  if exit
  then over c@ 030 =
  if 1- swap 1+ swap recurse
  then ;

: asc>  0F and ;		\ ascii number to binary number
: >asc  030 or ;		\ reverse
: vst!  b0 cell - bvp ! v$0 bvp @ ! ;

vst! 	\ initialize stack för dynamical numbers

: nextfree ( -- a )  bvp @ @ ;
: first ( -- a )  bvp @ cell + @ ;	\ big on tos
: second ( -- a )  bvp @ 2 cells + @ ;	\ big on second
: third ( -- a )  bvp @ 3 cells + @ ;	\ big on third
: vp+ ( -- )  -cell bvp +! ;		\ stack pointer

: tov \ ad --		ad of number array to stack
  vp+ bvp @ ! ;

: bempty ( -- f )  nextfree v$0 = ;
: len1 ( -- n )  nextfree first - ;	\ get length to first
: len2 ( -- n )  first second - ;
: len3 ( -- n )  second third - ;
: top$ ( -- a n )  first len1 ;
: sec$ ( -- a n )  second len2 ;
: thi$ ( -- a n )  third len3 ;

: vdigit \ n --		put single "digit" on stack
  nextfree tuck ! cell+ tov ;

: bsconstant \ n -- 
  create , does> @ vdigit ;
  
: dvdigit \ ud -- 	put double "digit" number on stack
  swap nextfree dup >r 2! 2 cells r> + tov ;

: bdconstant \ d --
  create , , does> 2@ dvdigit ;

: vpush \ a n --	put string on stack
  rez >xs nextfree xs@ over + tov xs> cmove ;

: bpush \ a n --	put any number array on stack
  nextfree over aligned		 \ a n nxt na
  2dup + cell - 0!		      \ a n nxt na 
  over + tov              \ a n nxt
  swap cmove ;

: bpusha \ a n --	put aligned number array on stack
  nextfree 2>r 2r@ swap cmove
  2r> + tov ;

: bdupall \ v -- v u	      allocate array of same size as btos
  nextfree len1 + tov ;

: bdrop  cell bvp +! ;
: bdup  top$ bpusha ;
: vdup  top$ vpush ;
: bover  sec$ bpusha ;
: boover  thi$ bpusha ;

: bvariable \ n -- 
  create allocate throw cell , , does> ; 
   
: b! \ v -- | ad --
  dup cell+ @ first nextfree over - rot swap >r r@ cmove
  r> swap ! bdrop ;

: b@ \ -- v | ad --
  2@ bpusha ;

: xstack!  x0 cell - xp ! x$0 xp @ ! ; xstack!	\ xtra stack
: xp+ ( -- )  -cell xp +! ;
: tox ( a -- )  xp+ xp @ ! ; 
: xnext ( -- ad )  xp @ @ ;
: xfirst ( -- ad )  xp @ cell+ @ ;
: xsecond ( -- ad )  xp @ 2 cells + @ ;
: xthird ( -- ad )  xp @ 3 cells + @ ;
: xlen ( -- n )  xnext xfirst - ;
: xpush ( a n -- ) rez >xs xnext xs@ over + tox xs> cmove ;

: bxpush ( a n -- ) >xs xnext xs@ over + tox xs> cmove ; 
: xdrop  cell xp +! ;
: xempty ( -- f )  xnext x$0 = ;

: >bx ( v -- )  top$ bxpush bdrop ;
: bx! ( v -- v )  top$ bxpush ;
: bx  ( -- v )  xfirst xnext over - bpusha ;
: bx> ( -- v )  bx xdrop ;

: by  \ -- v	y is the second value on x-stack
  xsecond xfirst over - bpusha ;

: bz  ( -- v )  xthird xsecond over - bpusha ;
: v>x ( v -- )  top$ bdrop xpush ;
: vx  ( -- v )  xfirst xnext over - vpush ;
: vx> ( -- v )  vx xdrop ;

: vy  \ -- v
  xsecond xfirst over - vpush ;

: bnip  >bx bdrop bx> ;
: bswap  >bx >bx by bx> xdrop ;
: vswap  v>x v>x vy vx> xdrop ;
: brot  >bx bswap bx> bswap ;
: btuck  bswap bover ;
: b2swap brot >bx brot bx> ;
: b2dup bover bover ;
: b2drop bdrop bdrop ;
: b3dup boover boover boover ;

: reztop  top$ xpush bdrop bx> ;      \ clean leading asczeros
: vzero  [char] 0 nextfree tuck c! 1+ tov ;
: bzero 0 vdigit ;                    \ small bigintegers
: bone  1 vdigit ;
: btwo  2 vdigit ;
: bthree 3 vdigit ;
: bten  0A vdigit ;

: byte1@ \ v -- v | -- b  get least significant byte of tos
  first c@ ;

: byte2@ \ v -- v | -- b  least sign byte on second number
  second c@ ;

: <vtop  \ delete unwanted leading asc zeros
  begin len1 2 <
     if exit then nextfree 1- c@ 0=	
  while -1 bvp @ +! 
  repeat ;

: <top  \ delete unwanted leading zeros
  begin len1 cell > 0=
     if nextfree 0! exit
     then nextfree cell - @ 0= 		
  while -cell bvp @ +! 
  repeat nextfree 0! cell len1 3 and - 3 and bvp @ +! ; 

: bs/mod \ v -- q | n -- r  	v=nq+r 
  >xs bdupall nextfree cell - 0!
  0 0 len1 cell -
  do i second + @ swap xs@ um/mod i first + ! -cell
  +loop <top xsdrop bnip ;

: vr< \ u v -- u v | -- f	compare numbers as asc strings
  reztop <vtop vswap reztop <vtop vswap
  len2 len1 2dup <
  if 2drop true exit
  then dup >zs > 
  if zsdrop false exit
  then first nextfree 1- 
  do i zs@ - c@ i c@ 2dup = 0=
     if zsdrop < if true else false then unloop exit
     then 2drop -1
  +loop zsdrop false ;

: vr= \ u v -- u v | -- f	
  vr< if false exit then
  vswap vr< if vswap false exit then vswap true ;

: v2/  \ v -- v/2
\ divide asc number by 2
  nextfree first >xs 0 >ys
  begin xs@ c@ over xs@ >
  while asc> 2/mod ys> + >asc xs@ c!
     negate 5 and >ys 1 xs+!
  repeat reztop <vtop 2drop xsdrop ysdrop ;

: v>byte \ u -- v | -- f b
\ divide asc-string by 256 leaving rest b. f true if v=0
  xsdepth false >ys 8 0
  do nextfree 1- c@ 1 and >xs v2/ vzero vr= bdrop
     if true ys! leave then
  loop xsdepth swap - 0 tuck
  do 2* xs> + loop ys> swap ; 

: nth ( n -- b/0 )  1+ bvp @ swap cells + 
  dup b0 = if drop 0 else @ then ; 

: len# \ n -- m 
  dup nth swap 1- nth ?dup
  if swap else v$0 swap then - ; 

: bpick \ bn ... b0 -- bn ... b0 bm | m -- 
  dup nth swap len# bpusha ;

: xnth ( n -- b/0 )  1+ xp @ swap cells + 
  dup x0 = if drop 0 else @ then ; 

: xlen# \ n -- m 
  dup xnth swap 1- xnth ?dup
  if swap else x$0 swap then - ; 

: bxpick \ xn ... x0 -- xn ... x0 xm | m --
  dup xnth swap xlen# bpusha ;

: #>bx \ bn ... b0 -- bn ... bm  x: -- bm-1 ... b0 | m --
  0 do >bx loop ;

: #bx> \ -- bm-1 ... b0  x: bm-1 ... b0 -- | m --
  0 do bx> loop ;

: bdepth \ -- n 
  040 0					\ depth of stack
  do i nth 0= if i leave then loop ; 

: v>b  \ convert asc-number to digital bignumber
  pad 1k 2dup + pad
  do v>byte i c!
     if drop i 1+ 0! i pad - 1+ cell+ leave then
  loop bdrop bpush <top ; 

: s>b \ -- v | n --	convert single to big
  0 <# #s #> vpush v>b ;

: b>s  \ u -- | -- n	conv big to single
  first @ bdrop ;

: d>b \ -- v | d --
  <# #s #> vpush v>b ;

: b>d  \ u -- | -- d
  top$ 5 < if @ 0 else 2@ swap then bdrop ;

: v  bl parse vpush ; 		\ 'v 12345' put asc numb on tos
: b  v v>b ;	       		\ put bigint on tos 
: cl vst! xstack! ;		\ clear stacks

: .v  cr bdepth ?dup		\ print asc numb stack
  if 0 do i nth i len# type cr loop then ;

: .bytes cr bdepth ?dup		\ print byte string stack
  if 0 do i nth i len# 0
          do i over + c@ base @ >xs
             hex 0 <# # # #> type space xs> base !
          loop drop cr
       loop
  then ;

: b+_s>=f \ u v -- u+v		u >= v
  len2 nextfree over len1 - dup bvp @ +! erase
  0 >xs nextfree first 
  do i over - @ i @ 0 tuck d+ xs> 0 d+ >xs i ! cell
  +loop drop xs> ?dup if nextfree cell bvp @ +! ! then ;

: b+ \ u v -- u+v		adding bigint
  len2 len1 < 0=
  if b+_s>=f
  else bswap b+_s>=f 
  then bnip ;

: br< \ u v -- u v | -- f	bigstack remain less
  len2 len1 2dup u<
  if 2drop true exit
  then dup pad1 ! u>
  if false exit
  then first >xs second >ys 0 >zs 0 pad1 @ cell -
  do ys@ i + @ xs@ i + @ 2dup = 0=
     if drop-all u< if true else false then unloop exit
     then 2drop -cell
  +loop drop-all false ;

: b< \ u v -- | --f		bigstack less
  br< bdrop bdrop ;

: br= \ u v -- u v | -- f
  br< if false exit then
  bswap br< if bswap false exit then bswap true ;

: b= \ u v -- | --f
  br= bdrop bdrop ;

: br> \ u v -- u v | -- f
  br= br< or 0= ;

: b> \ u v -- | --f
  br> bdrop bdrop ;

: br0= \ v -- v | -- f
  len1 cell - first @ or 0= ;

: b0= \ v -- | -- f
  br0= bdrop ;

: b>v$ \ b -- b | -- a n
  pad2 pad1 ! bdup 0A 
  begin dup bs/mod >asc pad1 @ c! -1 pad1 +! br0= until 
  drop bdrop 1 pad1 +! pad1 @ pad2 over - 1+ ;

: b>v  \ b -- b v
  b>v$ vpush ;

: bdec# ( b -- b | -- n )  b>v$ nip ;

: br. \ b -- b
  b>v$ type space ;

: b. \ b --
  br. bdrop ;

: .b  bempty 0=
  if cr br. >bx recurse bx> then ;

: .x  xempty 0=
  if bx> cr br. recurse >bx then ;

: gtx? \ v -- v | -- f		greater than value in bx?
  len1 xlen 2dup <
  if 2drop false exit then >
  if true exit then false 0 xlen cell -
  do first i + @ xfirst i + @ 2dup <
     if 2drop leave then >
     if 0= leave then -cell
  +loop ;

: +x>=y? \ v -- | -- f		add v to bx and compare with y
  bx> b+ bx> br< >bx >bx 0=
  dup if xdrop xdrop then ;	\ 2 xdrop when equal or greater

variable borrow
: b~ \ u v -- |u-v| | -- f
  br< if bswap true else false then >zs
  first len1 + len2 len1 - dup bvp @ +! erase
  false borrow ! first >xs second >ys len1 0
  do i ys@ + @ 0
     borrow @ 0 d-
     i xs@ + @ 0 d-
     abs borrow ! i ys@ + ! cell
  +loop 0 >zs bdrop drop-all <top zs> ;

: b- \ u v -- u-v
  b~ if cr ." negative big!" cr 10 throw then ; 

: |b-| \ u v -- |u-v|
  b~ drop ;

: bsl \ n i -- n1 n0	      big shift left, n < 2^bits
  2dup bits swap - rshift -rot lshift ;

: blshift  \ v -- u | n -- 		big left shift
  bits/mod over 0= 
  if nip first dup rot cells dup >xs + len1 cmove> 
     xs@ bvp @ +! first xs> erase exit
  then cells >ys			\ i  y=4[n/32]
  ys@ first dup >xs + 			\ i f+4[n/32]  x=first
  xs@ over len1 dup >zs cmove>		\ i f+4[n/32]  z=len1
  xs@ ys@ erase
  zs> over + dup xs! swap 0 >zs		\ i f+4[n/32]+len1 f+4[n/32]
  ?do i @ over bsl zs> or i ! >zs cell +loop
  zs@ xs@ ! xs@ cell+ bvp @ ! drop drop-all <top ;

: brshift \ v -- u | n -- 
  8/mod >ys >xs 
  nextfree 0! nextfree first
  do ys@ i + @ 0FFFF and xs@ rshift 0FF and i c!
  loop nextfree ys@ - ys> erase
  <top xsdrop ;

: b1and \ v -- v s
  first @ 1 and vdigit ;

: beven \ v -- v | -- f
  first @ 1 and 0= ;

: bodd \ v -- v | -- f
  beven 0= ;

: b1or \ v -- v'
  first @ 1 or first ! ;

: b2/mod \ v -- r k 
  b1and bswap 1 brshift ;

: msb@ \ v -- v | -- c      most significant byte in value on tos
  nextfree cell- nextfree 1-
  do i c@ ?dup if leave then -1 +loop ;

: msb@2 \ u v -- u v | -- c      most sign byte second for on stack
  first cell- first 1-
  do i c@ ?dup if leave then -1 +loop ;

: z# \ v -- v | -- n      nr of zero bytes in most sign cell tos
  0 >xs nextfree
  begin 1- dup c@ 0=
  while 1 xs+! 
  repeat drop xs> ;

: z#2 \ u v -- u v | -- n
  0 >xs first
  begin 1- dup c@ 0=
  while 1 xs+! 
  repeat drop xs> ;

: blog~ \ v -- v | -- n		8(len-1)+log(byte0)+1
  len1 z# - 1- 3 lshift msb@ log~ + ; \ n is the number of binary digits

: blog~2 \ u v -- u v | -- n 
  len2 z#2 - 1- 3 lshift msb@2 log~ + ;

: blog \ v -- | -- n	 integer part of 2-logarithm
  blog~ 1- bdrop ;

: b1+ bone b+ ;
: b1- bone b- ;
: b2+ btwo b+ ;
: b2- btwo b- ;

: b2* \ v -- 2v
  1 blshift ;

: b2/ \ v -- v/2
  1 brshift ;

: b256* \ v -- 256v
  top$ over 1+ swap cmove>
  bvp @ 1+! 0 first c! ;

: last!> \ n --
  nextfree cell - ! cell bvp @ +! ;

: cell*x \ -- n*v ; x: v -- v | n --
  bzero 0 >xs xnext xfirst 
  do dup i @ um* xs> 0 d+ >xs last!> cell +loop
  xs> nextfree cell - ! drop <top ;

: bs* \ v -- n*v | n --
  >bx cell*x xdrop ;

: bdups* \ v -- v n*v | n -- 
  bzero 0 >xs first second 
  do dup i @ um* xs> 0 d+ >xs last!> cell +loop 
  xs> nextfree cell - ! drop <top ; 

: bitsblshift \ v -- w	       big shift left with number of bits
  top$ over cell+ swap cmove>
  cell bvp @ +! 0 first ! ;

: b* \ u v -- u*v
  len1 len2 < if bswap then
  >bx bzero second first cell - 
  do bitsblshift i @ cell*x b+ -cell +loop
  bnip xdrop <top ;

: brandom \ -- u | n --  the maximal number of decimal digits in u
  bzero 0 do bten b* 10 random s>b b+ loop ;

\ 2^sxn+1=2*2^sxn-[2^sxn]^2*n/2^[2s] 
\ q=t*x/2^[2n]
: b/ \ u v -- q 	Newton-Ralphson on y=2^s/x-A 
  br< if bdrop bdrop bzero exit then          \ qoute < 1
  len1 cell > 0= 
  if b>s bs/mod drop exit then                \ denominator < 2^bits
  blog~ >xs >bx bdup blog~ 2/ 6 + >ys 
  ys@ 2* xs> - dup >xs bone blshift xs>
  if 6 bs* 5 bs/mod drop then 1F 0            \ start value
  do bdup b2* bover bdup b* bx b* 
     ys@ 2* brshift b- 
     br= bnip 
     if leave then
  loop b* ys> 2* brshift 
  begin bover bover bx b* b< while b1- repeat 
  begin bover bover bx b* bx b+ b< 0= while b1+ repeat
  bnip xdrop ; \ t-nq>n <=> t>n+nq

\ Barrett reduction 
\ Faster modulo when repeting [mod d] with same d

variable foo
1k bvariable bar
1k bvariable den

: barmod~ \ w -- v			w < d**2
  bdup
  bar b@ b*
  foo @ brshift				\ w q
  den b@ b* b- 				\ w-qd
  den b@ br<
  if bdrop else b- then ;

: barmod \ w -- v			w < d**2
  bdup den b@ br< 
  if b2drop exit 
  then bdrop bar b@ b*
  foo @ brshift				\ w q
  den b@ b* b- 				\ w-qd
  den b@ br<
  if bdrop else b- then ;

: >bar \ u -- 	 	u is the denominator; precalc for barmod
  blog~ 2* dup foo ! 			\ foo = 2*bitlen
  bone blshift bover b/ bar b! 		\ bar = 2^foo/u
  den b! ;				\ den = u

: b** \ b a -- b^a
  first @ 0= if bdrop bdrop bone exit then
  >bx bzero >bx bone
  begin bover b*
     bone +x>=y?
  until bnip ;

: bmod \ w u -- r
  bover bover b/ b* b- ;
  
: b/mod \ w u -- r q
  bover bover b/ bdup >bx b* b- bx> ;

: bsqrtf \ w -- v                  \ Newton-Ralphson
  br0= if exit then
  blog~ u2/ bone blshift 10 0      \ start value
  do bover bover b/ br=
     b+ b2/ if leave then
  loop bdup bdup b* brot bswap br< bdrop bdrop
  if b1- then ;

: bsqrtc \ w -- v
  b1- bsqrtf b1+ ;

: bfaculty  \ v -- v!
  >bx bzero bone
  begin bswap b1+ gtx? bswap 0=
  while bover b*
  repeat bnip xdrop ;

: bgcd \ v u -- w	greatest common divisor
  br< if bswap then
  begin btuck bmod br0=
  until bdrop ;
false [if]
: gcd \ m n -- d
  2dup u< if swap then
  begin tuck 0 swap um/mod drop dup 0=
  until drop ;
[then]
: blcm \ v u -- w	least common multiple
  bover bover b* brot brot bgcd b/ ;

\ the square-and-multiply-algorithm
: b**mod~ \ u v m -- u^v mod m
  >bx blog~ bswap >bx bone 0	  		\ v 1 | x: m u | l[v] 0
  do i bits/mod cells second + @		\ v w | x: m u | r celli
     1 rot lshift and				\ v w | x: m u | celli & 2^r
     if bx b* by bmod				\ v [w*u]
     then bx bx> b* bx bmod >bx 		\ v [w*u] x<-[x*x]
  loop bnip xdrop xdrop ; 

\ the square-and-multiply-algorithm with Barrett reduction ?
: b**mod \ u v m -- u^v mod m
  bover bone b= if bnip bmod exit then
  >bar blog~ bswap >bx bone 0	
  do i bits/mod cells second + @
     1 rot lshift and
     if bx b* barmod 
     then bx bx> b* barmod >bx
  loop bnip xdrop ; 

: sign-comp  \ t q t' -- t" | f" f f' -- fnew f'
  b* >r r@ xor 2* +
  case 0 of b~ endof
      -1 of b+ true endof
      -2 of b+ false endof
      -3 of b~ 0= endof
  endcase r> ;

variable flag
variable flag11
variable flag12
variable flag21
variable flag22

: binvmod \ u v -- u' 
  false flag !
  false flag11 ! false flag12 !
  false flag21 ! false flag22 !
  btuck bzero bone b2swap bswap
  begin br0= 0=
  while bover bover b/ >bx flag21 @ flag22 @ xor flag !
     b2swap btuck bx flag12 @ flag @ flag11 @
     sign-comp flag12 ! flag11 !
     b2swap btuck bx> flag22 @ flag @ flag21 @
     sign-comp flag22 ! flag21 !
  repeat bdrop bdrop bdrop flag12 @
  if bover |b-| then bswap bmod ;

base !

: loc{ [compile] { ; immediate

\ Single cell computational arithmetic


: .s depth if >r recurse r> dup . then ;

?undef 0> [if] : 0> ( n -- flag )  0 > ; [then]
false [if]
: ugcdl ( a b -- c )              \ Algorithm from Wikipedia
  0 loc{ a b t -- c }
  a b u< if a b to a to b then    \ a>=b as unsigned numbers
  begin b \ while b<>0
  while b to t \ t <- b
     a 0 b um/mod drop to b       \ b <- a(mod b)
     t to a \ a <- t
  repeat a ;
[then]
: ugcd ( a b -- c ) \ a version without local variables
  2dup u< if swap then   \ smallest of a b on top of stack (tos)
  ?dup 0= if exit then   \ return second value if tos is zero
  begin tuck             \ y x y first time b a b
     0 swap um/mod       \ y x 0 y --> y r q
     drop dup 0=         \ y r [r=0]
  until drop ;           \ y

?undef umod [if]
: umod ( u1 u2 -- u3 ) 0 swap um/mod drop ;
[then]

: u*mod ( u1 u2 u3 -- u4 )
  >r r@ umod swap r@ umod um*
  r> um/mod drop ;

?undef bits [if] cell 8 * constant bits [then]
?undef log~ [if]
: log~ ( n -- nr ) \ nr = 1+²log n
  bits here !                \ bits is stored at the address 'here'
  bits 0                     \ do-loop from i=0,...,bits-1
  do 1 rshift ?dup 0=        \ shift tos at right test if zero
     if i 1+ here !          \ if zero store i+1 at 'here'
        leave                \ and leave the loop
     then 
  loop here @ ;
[then]
: u**mod loc{ b a m -- x }
  1                     \ preparation for repeated multiplication
  a log~ 0              \ n 0 n is the number of binary digits in a
  ?do a 1 i lshift and  \ flag the i-th digit of a is 0/1
     if b m u*mod       \ multiply if flag
     then b dup m       \ square b for each i: b b^2 b^4 b^8 ...
     u*mod to b         \ new squared number to b
  loop ;                \ result of the repeated multiplication

: invmod ( a m -- a' ) \ a m must be coprime
  dup 1 0 loc{ a m v c b }
  begin a
  while v a / >r
     c b s>d c s>d r@ 1 m*/ d- d>s to c to b  \ old c become new b
     a v s>d a s>d r> 1 m*/ d- d>s to a to v  \ old a become new v
  repeat b m mod dup to b 0<
  if m b + else b then ;

\ Pseudo prime number tests
?undef rand [if]
variable rnd base @ hex 

: reset_seed 0ABCDEF1 rnd ! ; reset_seed 

: rand ( -- u )
  rnd @ 08088405 * 1+ dup rnd ! ;

: random ( u1 -- u2 ) 
  rand um* nip ;

base ! 
[then]
: fermat ( numb -- flag ) \ numb odd
  dup 2 - random 2 +
  over 1- rot u**mod 1 = ; 
?undef 2/mod [if]
: 2/mod \ n -- r q
  dup 1 and swap 1 rshift ;
[then]
: get-rs 0 loc{ numb r -- r s } \ numb odd
  numb 1-
  begin dup 2/mod swap 0=       \ n qout rest=0
  while nip r 1+ to r
  repeat 2drop 
  r numb 1- r rshift ;

: get-a ( numb -- a )
  2 - random 2 + ;
  
: rabin-miller1 ( numb -- flag )    \ numb odd
  dup get-rs false loc{ numb r s flag } 
  2 s numb u**mod 1 = 
  if true exit
  then r 0 
  ?do 2 s i lshift numb u**mod numb 1- = 
     if true to flag leave then
  loop flag ;

create pnr 
2 c, 3 c, 5 c, 7 c, 11 c, 13 c, 17 c, 19 c, 23 c, 29 c, 31 c, 37 c,

: rabin-miller2 ( numb a -- flag )
  over get-rs false loc{ numb a r s flag }
  a s numb u**mod 1 = 
  if true exit
  then r 0 
  ?do a s i lshift numb u**mod numb 1- = 
     if true to flag leave then
  loop flag ;

cell 4 = 
[if]
: rmx ( numb -- n ) \ 32 bit integers
  dup 2047 u< if drop 1 exit then
  dup 1373653 u< if drop 2 exit then
  dup 25326001 u< if drop 3 exit then
    3215031751 u< if 4 else 5 then ;
[else]
: rmx \ numb -- n 64 bit integers
  dup 2047 u< if drop 1 exit then
  dup 1373653 u< if drop 2 exit then
  dup 25326001 u< if drop 3 exit then
  dup 3215031751 u< if drop 4 exit then
  dup 2152302898747 u< if drop 5 exit then
  dup 3474749660383 u< if drop 6 exit then
  dup 341550071728321 u< if drop 8 exit then
  3825123056546413051 u< if 11 else 12 then ;
[then]

: rabin-miller ( numb -- flag )
  dup rmx 0
  do dup i pnr + c@ rabin-miller2 0=
     if 0= leave then
  loop 0= 0= ;

: fermat-rabin-miller ( numb -- flag ) \ numb odd
  dup fermat
  if rabin-miller
  else 0=
  then ;

: nextprime ( numb -- prime )
  dup 3 u< if drop 2 exit then
  1 or
  begin dup fermat-rabin-miller 0=
  while 2 +
  repeat ;

: prime ( numb -- flag )
  dup 3 u< if 2 = exit then
  dup 1 and 0= if drop false exit then
  rabin-miller ;

\ Square root
?undef sqrtf [if]
: sqrtf \ m -- n
  0 d>f fsqrt f>s ;

: sqrtfslow \ m -- n Newton-Ralphson´s method
  dup 4 u< if dup if drop 1 then exit then
  dup 1- >r 1 rshift
  begin r@ over 0 swap um/mod nip
     over + 1 rshift tuck u> 0=
  until r> drop ;

: sqrtc \ m -- n
  1- sqrtf 1+ ;
[then]
\ Integer factoring

: func ( numb n -- m ) dup um* 1 0 d+ rot um/mod drop ; 

: pollard1 ( numb start -- pfac flag )
  dup dup loc{ numb start alpha beta } 0  \ numb is an odd composite 
  begin drop numb alpha func to alpha
     numb dup beta func func to beta
     alpha beta - abs                  \ |alpha-beta|
     numb ugcd dup numb =              \ gcd flag 
     if false exit 
     then dup 1 = 0=                   \ gcd<>1 
  until true ;

: pollard2 \ numb -- prime numb>1
  dup 1 and 0= if drop 2 exit then
  dup prime if exit then
  dup sqrtf dup * over = 
  if sqrtf exit then -1 2              \ numb 100 0 
  do dup i pollard1                    \ numb pfac flag
     if leave                          \ numb pfac
     then drop                         \ numb
  loop nip ;                           \ pfac

: pollard \ n -- p1 ... pk      
  dup pollard2 2dup =                  \ n q f=
  if drop exit                         \ n
  then dup >r 
  0 swap um/mod nip recurse            \ q n/q
  r> recurse ;

: pollard# \ numb -- p1 ... pk k
  depth >r
  pollard depth r> - 1+ ;

\ Sorting the stack

: lower \ m1 ... mn m n+1 -- m1 ... m ... mi n+1  
\ lower m on stack until next number not is greater
  dup 2 =
  if drop 2dup u>
     if swap
     then 2 exit
  then >r 2dup u> 0= 
  if r> exit
  then r> rot >r 
  1- recurse 1+ r> swap ;

: sort \ m1 ... mn n -- s1 ... sn n o(n²)
  dup 3 <
  if dup 2 =
     if drop 2dup u> 
        if swap 
        then 2 
     then exit
  then dup >r
  1- recurse roll 
  r> lower ;

\ Arithmetical functions

: radical1 ( n -- r )
  1 dup loc{ n radical prime }
  n pollard# sort 0 
  do dup prime = 0=
     if dup radical * to radical
     then to prime 
  loop radical ;
  
: undequ ( a b c -- a b c a=b )
  >r 2dup = r> swap ;

: radical2 ( n -- r )
  1 loc{ n prime }
  n pollard# sort 1 swap 0 
  do over prime =
     if nip
     else over to prime *
     then 
  loop ; 

: radical ( n -- r )
  1 swap
  pollard# sort
  1 swap 0
  do undequ if nip else * then
  loop nip ;

: totients1 ( n -- t )
  1 loc{ tot }
  pollard# sort 0
  do 2dup =
     if tot * to tot
     else 1- tot * to tot
     then
  loop tot ;

: totients ( n -- t )
  1 swap
  pollard# sort
  1 swap 0
  do undequ if * else swap 1- * then
  loop nip ;

: drops 0 ?do drop loop ;

: mobius ( n -- my )
  dup 2 u< if drop 1 exit then
  1 swap
  pollard# sort
  dup true loc{ facts sqrfree } 0
  do 2dup =
     if false to sqrfree
        facts i - drops leave 
     then drop
  loop sqrfree
  if facts 1 and
     if -1
     else 1
     then
  else 0
  then nip ;

: bigomega ( n -- b )
  dup 2 u< if drop 0 exit then
  pollard# dup >r drops r> ;

: smallomega ( n -- s )
  dup 2 u< if drop 0 exit then
  1 swap
  pollard# sort 0 swap 0
  do undequ 0= if 1+ then nip
  loop nip ;

: ** ( b e -- b^e )
  dup 0= if 2drop 1 exit then
  1 swap 0 do over * loop nip ;

: m** ( b e -- d )
  dup 0= if 2drop 1. exit then
  1 swap 1. rot 0
  do 2over m*/ loop 2nip ;

: -1** ( n -- i )
  1 and if -1 else 1 then ;

: unit* ( i j -- k )
  xor 1+ ;

: ufaculty ( u -- u! )
  dup 2 u< if drop 1 exit then
  dup 1- recurse * ;

: umfaculty ( u -- ud )
  dup 2 u< if drop 1. exit then
  dup 1- recurse rot 1 m*/ ;

: oddpart ( a -- i m )
  0 swap
  begin 2/mod swap 0=
  while 1 under+
  repeat 2* 1+ ;

: legendre ( a p -- i )
  tuck dup 1- 2/ swap u**mod dup 1 >
  if swap - else nip then ;

: jacobi ( a n -- j )
  1 loc{ a n unit }
  a n ugcd 1 = 0= if 0 exit then 
  begin n 1 = a 1 = or if unit exit then
     a n mod ?dup 0= if 0 exit then
     oddpart to a 1 and
     if n dup * 1- 3 rshift -1** unit unit* to unit 
     then a n ugcd 1 = 0= if 0 exit then
     n a to n to a
     a 1- n 1- * 2 rshift -1** unit unit* to unit
  again ; 

: kronecker ( a n -- j )
  0 loc{ a n unit }
  n 0= if a abs 1 = if 1 else 0 then exit then
  n dup abs to n 0<
  if a 0< if -1 else 1 then
  else 1
  then to unit
  a dup abs to a \ old_a
  n oddpart to n dup \ old_a i i
  if a 1 and 0= \ old_a i f
     if 2drop 0 exit 
     else 1 and \ old_a f
        if a 7 and 1+ 4 and \ old_a
           if unit negate to unit then \ old_a
        then
     then
  else drop
  then a n jacobi ?dup 0=
  if drop 0 exit then
  unit unit* to unit \ old_a
  0< if n 1- 2/ -1** else 1 then \ ±1
  unit unit* ;

\ Gaussian integers 
\ Typical restriction, the norm must be a single cell integer

: gnorm \ a b -- u 
  dup * swap dup * + ;

: g< \ a b c d -- flag
  gnorm -rot gnorm u> ;

\ print single cell signed numbers without spaces
\ http://www.forth.com/starting-forth/sf7/sf7.html
: .sign-w/o-space \ n --
  dup 0< swap abs 0 <# #s rot sign #> type ;

: g. \ a b --
  2dup 0. d= if d. exit then
  swap dup \ b a a
  if over 
     if dup .sign-w/o-space
     else dup .
     then
  then swap dup 0< 0= \ a b f
  if dup \ a b b
     if swap if ." +" then dup 1 > \ b f
        if .sign-w/o-space else drop then ." i" space
     else 2drop
     then
  else nip dup \ b b 
     if dup -1 < \ b f
        if .sign-w/o-space else ." -" drop then ." i" space
     else drop
     then
  then ;

: .gs depth 2 < if exit then 2>r recurse 2r> 2dup g. ;

: g+ \ a b c d -- a+c b+d
  under+ under+ ;

: g- \ a b c d -- a-c b-d
  negate under+ negate under+ ;

: g* loc{ a b c d -- e f } 
  a c m* b d m* d- d>s a d m* b c m* d+ d>s ;

: g/ loc{ a b c d -- e f }
  c dup m* d dup m* d+ d>f
  a c m* b d m* d+ d>f fover f/
  b c m* a d m* d- d>f frot f/
  fswap f>d d>s f>d d>s ;

: g/' loc{ a b c d -- e f }
  c dup m* d dup m* d+ d>f
  a c m* b d m* d+ d>f fover f/ fround
  b c m* a d m* d- d>f frot f/ fround
  fswap f>d d>s f>d d>s ;

: gmod ( a b c d -- e f )
  2over 2over g/' g* g- ;

: ggcd ( a b c d -- e f ) \ Euclid's algorithm
  0 0 loc{ a b c d s t }
  a b c d g<
  if a c to a to c
     b d to b to d
  then
  begin c d or \ while c+id<>0
  while c to s d to t
     a b c d gmod to d to c
     t to b s to a
  repeat a b ;

: gnormal ( a b -- c d ) \ c>=d and c>=0
  2dup abs swap abs >
  if 0 1 g* then over 0< 
  if negate swap negate swap then ;

\ http://mathworld.wolfram.com/GaussianPrime.html
: gprime1 \ n --flag
  abs dup prime swap 3 and 3 = and ;

: gprime \ a b -- flag 
  over 0= if nip gprime1 exit then
  dup 0= if drop gprime1 exit then
  gnorm prime ;

: .normgp ( a b norm -- )
  cr 8 .r space g. ;

: .gprime loc{ norm -- }
  norm 2 = if 1 1 norm .normgp exit then
  norm sqrtf 1+ 0
  do i 0
     ?do i j gnorm norm =
        if i j gprime 
           if j i norm .normgp then
        then
     loop
  loop ; 

: .gps 1+ 2 do i .gprime loop ;

: gfunc ( a b x y -- u v )
  2dup g* -1 0 g+ 2swap gmod ;

: gpollard1 ( a b c d -- p q flag ) \ a+ib not having factor 2
  2dup loc{ a b alpha1 alpha2 beta1 beta2 } 0.
  begin 2drop a b alpha1 alpha2 gfunc to alpha2 to alpha1
     a b 2dup beta1 beta2 gfunc gfunc to beta2 to beta1
     alpha1 alpha2 beta1 beta2 g-
     a b ggcd 2dup a b d=
     if false exit
     then 2dup gnorm 1 = 0=
  until true ;

: gpollard2 ( a b -- p q )
  false loc{ flag }
  2dup gnorm 1 = if exit then
  2dup 2 0 gmod d0= if 2drop 1 1 exit then
  2dup gprime if exit then -1 1
  do i 0
     do 2dup j i gpollard1
        if true to flag leave then 2drop
     loop flag if leave then
  loop 2swap 2drop ;

: gfac ( a b -- p1 q1 ... pk qk )
  2dup gpollard2 2over 2over gnorm -rot gnorm =
  if 2drop exit
'  then 2dup 2>r g/ recurse 2r> recurse ;

\ Prime functions

: prevprime ( numb -- prime )
  dup 3 u< if drop 2 exit then
  1- 1 or 
  begin dup fermat-rabin-miller 0=
  while 2 -
  repeat ;

?undef under+ 
[if]
: under+ ( a b c -- a+c b ) rot + swap ; 
[then]

: 65536/mod ( n -- r q ) dup 65535 and swap 16 rshift ;

\ bit arrays

: adbit ( i ad -- j a ) swap 8/mod rot + ;

: setbit \ i ad --
  adbit 1 rot lshift over c@ or swap c! ;

: tglbit \ i ad --
  adbit 1 rot lshift over c@ xor swap c! ;

: clrbit \ i ad --
  adbit 1 rot lshift 255 xor over c@ and swap c! ;

: bit@ \ i ad -- bit
  adbit c@ swap rshift 1 and ;

: bit! \ bit i ad --
  rot if setbit else clrbit then ;

: bit? ( i ad -- f ) bit@ negate ;

: bitarray \ bits -- ad | n -- bit
  8/mod swap 0= 0= negate + allocate throw
  create dup ,
  does> @ swap 8/mod rot + bit@ ;

\ multiple byte read/write in arrays

variable ebuf
1 ebuf ! ebuf c@ negate
[if] \ little-endian
: mb! ( n ad i -- ) 2>r ebuf ! ebuf 2r> cmove ;
: mb@ ( ad i -- n ) ebuf 0 over ! swap cmove ebuf @ ;
[else] \ big-endian
: mb! ( n ad i -- ) 2>r ebuf ! ebuf cell + r@ - 2r> cmove ;
: mb@ ( ad i -- n ) ebuf 0 over ! cell + over - swap cmove ebuf @ ;
[then]

\ the sieve of Eratosthenes 
\ 0xfffff constant plim
\ 82025 constant pi_plim
  16777215 constant plim      
  1077871 constant pi_plim    
\ 100000000 constant plim \ 100000000 takes 6 times 
\ 5761455 constant pi_plim \ longer time to load

plim bitarray prime_ constant pbuf
\ prime_ ( n -- flag ) n<plim

: resetsieve ( -- )
  pbuf plim 8/mod swap 0= 0= - + pbuf 
  do true i ! cell +loop ;

: sieve ( -- )
  resetsieve
  0 pbuf clrbit 
  1 pbuf clrbit
  plim sqrtf 1+ 2
  do i pbuf bit@
     if plim 1+ i dup *
        do i pbuf clrbit j +loop
     then 
  loop ; sieve 

plim prevprime constant pmax_

: nextprime_ ( numb -- prime ) \ numb<pmax_
  dup 3 u< if drop 2 exit then
  1 or
  begin dup prime_ 0=
  while 2 +
  repeat ;

: prevprime_ ( numb -- prime )
  dup 3 u< if drop 2 exit then
  1- 1 or 
  begin dup prime_ 0=
  while 2 -
  repeat ;

: prime ( n -- flag ) dup plim u> if prime else prime_ negate then ;
: nextprime ( numb -- prime ) dup pmax_ u< if nextprime_ else nextprime then ;
: prevprime ( numb -- prime ) dup plim u< if prevprime_ else prevprime then ;

plim 65536/mod swap 0= 0= - constant breaknumbers
pi_plim 2* allocate throw constant pnrbuf 
breaknumbers cells allocate throw constant breaks 

: init_pnr ( -- )
  0 pad ! 0 breaks ! 
  1 pi_plim 1+ 1 
  do nextprime_ dup \ p p
     65536/mod pad @ = 0= \ p r flag
     if 1 pad +! \ p r
        i 1- pad @ cells breaks + ! \ p r
     then pnrbuf i 1- 2* + 2 mb! 1+ \ p+1
  loop drop ; init_pnr 
\ it takes less than a second to store all primes less than 2^24

: newintbreaks ( i j x -- i' j' ) 
  >r 2dup + 2/ dup
  cells breaks + @ r> u> \ i j k flag 
  if -rot nip else nip then ; 

: pnr@ ( n -- p ) \ n<1077871 
  1- dup >r 2* pnrbuf + 2 mb@ 
  breaknumbers 0 
  begin r@ newintbreaks 2dup - 2 u< 
  until rdrop nip 16 lshift + ; 

: newintpnr ( i j x -- i' j' ) 
  >r 2dup + 2/ dup pnr@ r> u> \ i j k flag 
  if -rot nip else nip then ; 

: fpi pi ;

: pi ( x -- n ) >r pi_plim 1+ 0  \ x<16777215
  begin r@ newintpnr 2dup - 2 u< \ i j flag 
  until rdrop nip ;


\ NESTED SETS WITH CARTESIAN PRODUCTS

\ Stacks_____

: cs negate 2/ ;
: listflag 1 and ;

: objsize \ bc -- n 
  dup 0< if cs 1+ else drop 1 then ;

: >stack ( n ad -- )  cell over +! @ ! ;
: stack> ( ad -- n )  dup @ @ -cell rot +! ;
: >stack> ( n ad -- m )  dup @ @ -rot @ ! ;
: stack@ ( ad -- n )  @ @ ;
: stack! ( n ad -- )  @ ! ;
: stack+! ( n ad -- )  @ +! ;

1 23 lshift cells allocate throw dup constant xst dup ! 

: >xst ( n -- )  xst >stack ;
: xst> ( -- n )  xst stack> ;
: >xst> ( n -- m )  xst >stack> ;
: xst@ ( -- n )  xst @ @ ;
: xst! ( n -- )  xst @ ! ;
: xst+! ( n -- )  xst @ +! ;

: >>xst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >xst loop r> >xst ;
: xst>> ( -- x1 ... xn bc )  xst@ >r xst> cs 0 ?do xst> loop r> ;

1 23 lshift cells allocate throw dup constant yst dup ! 

: >yst ( n -- )  yst >stack ;
: yst> ( -- n )  yst stack> ;
: >yst> ( n -- m )  yst >stack> ;
: yst@ ( -- n )  yst @ @ ;
: yst! ( n -- )  yst @ ! ;
: yst+! ( n -- )  yst @ +! ;

: >>yst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >yst loop r> >yst ;
: yst>> ( -- x1 ... xn bc )  yst@ >r yst> cs 0 ?do yst> loop r> ; 

cell 1- log~ constant cellshift

: stack-depth ( ad -- n )  dup @ swap - cellshift rshift ;
: stack-cl ( ad -- )  dup ! ;
: stack-empty ( ad -- flag )  dup @ = ;

1 24 lshift cells allocate throw dup constant zst dup ! 

: >zst ( n -- )  zst >stack ;
: zst> ( -- n )  zst stack> ;
: >zst> ( n -- m )  zst >stack> ;
: zst@ ( -- n )  zst @ @ ;
: zst! ( n -- )  zst @ ! ;
: zst+! ( n -- )  zst @ +! ;

: >>zst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >zst loop r> >zst ;
: zst>> ( -- x1 ... xn -n )  zst@ >r zst> cs 0 ?do zst> loop r> ;

: showx xst stack-depth if xst> >r recurse r> dup . >xst then ;
: showy yst stack-depth if yst> >r recurse r> dup . >yst then ;
: showz zst stack-depth if zst> >r recurse r> dup . >zst then ;

: >zet ( s -- | -- s)
  >>yst yst> dup >xst cs 0 ?do yst> >zst loop xst> >zst ; 

: zet> ( -- s | s -- )
  zst> dup >yst cs 0 ?do zst> >xst loop yst> >xst xst>> ; 

\ Set manipulations_____

\ bundle code bc=-(2n+1)
\ z1...zn bc

: setdrop \ ad -- 
  dup @ @ cs cells cell+ negate swap +! ;

: setdup \ ad -- 
  >r
  r@ @ @ cs cells                 \ n'
  r@ @ over -                     \ n' ad1
  r@ @ cell+                      \ n' ad1 ad2
  rot cell+ dup r> +! cmove ;

: setover \ ad --
  dup >r @ @ cs cells cell+       \ nr of bytes 1'st set 
  r@ @ swap -                     \ ad to 2'nd set
  dup @ cs cells cell+ dup >r -   \ ad to 3'rd set
  cell+ r> r@ @ cell+             \ ad to move to
  swap dup r> +! cmove ;

: setcopy loc{ ad1 ad2 -- }
  ad1 @ @ cs cells             \ n'
  ad1 @ over - swap cell+      \ ad1-n' n
  ad2 @ cell+ over ad2 +! swap cmove ;

: setmove \ ad1 ad2 --
  swap dup rot setcopy setdrop ;

: adn1 zst@ cs cells zst @ over - swap cell+ ;
: adn2 adn1 drop cell - dup @ cs cells tuck - swap cell+ ;
: adn3 adn2 drop cell - dup @ cs cells tuck - swap cell+ ;

: zdup  zst setdup ;
: zdrop  zst setdrop ;
: zover  adn2 tuck zst @ cell+ swap cmove zst +! ;
: zswap  zover adn2 adn3 rot + move zdrop ;
: znip  zswap zdrop ;
: ztuck  zswap zover ;
: zrot  zst>> zswap >>zst zswap ; 

\ Output of sets_____

0 value addr1

: addr1- \ -- 
  addr1 1- to addr1 ;

: fillad$ \ addr n -- 
  dup 1- negate addr1 + dup to addr1 swap move addr1- ;

: n>addr1 \ n -- 
  0 <# #s #> fillad$ ;

: a>addr1 \ c -- 
  addr1 c! addr1- ;

: cardinality \ -- n | s --
  zst> cs dup >xst 0
  ?do zst@ 0<
     if zst@ dup cs negate xst+! >r zdrop r> cs 1+
     else zst> drop 1
     then
  +loop xst> ;

: foreach \ -- n 0 | s -- z1...zn
  zdup cardinality zst> drop 0 ;

: closep \ -- bc asc
  zst@ dup listflag if [char] ) else [char] } then ;

: openp \ bc -- asc
  listflag if [char] ( else [char] { then ;

: list$ \ ad -- ad n | s -- 
  dup to addr1 false loc{ addr2 flag }
  closep a>addr1
  foreach 
  ?do flag if [char] , a>addr1 then zst@ 0<
     if addr1 recurse 2drop
     else zst> n>addr1
     then flag 0= if true to flag then
  loop openp a>addr1
  addr1 1+ addr2 over - 1+ ; 

1 20 lshift dup allocate throw swap cell - + constant printbuf

: zet. \ -- | s -- 
  zst@ 0=
  if zst> .
  else printbuf list$ type
  then ; 

: set. \ yst,xst -- 
  zst setcopy zet. ;

\ Analyzing sets_____

: ?obj \ x -- 0,1,2
  dup 0<
  if listflag
     if 1 else 2 then
  else drop 0
  then ;

: _split \ ad --   ad=yst,zst 
  dup >r @ cell - @ 0< 0=
  if r@ stack> 2 + r@ stack> swap r@ >stack r> >stack exit then
  r@ stack>
  r@ xst setmove
  xst@ cs 1+ 2* + r@ >stack
  xst r> setmove ;

: ysplit \ -- | s -- s' x  in yst stack
  yst _split ;

: zsplit \ -- | s -- s' x
  zst _split ;

\ Set equal, subset and membership_____

: zetmerge \ -- | s s' -- s" 
  zst yst setmove
  yst@ zst> + 
  yst zst setmove
  zst! ;
  
: ymerge yst xst setmove xst@ yst> + xst yst setmove yst! ;
: zmerge zetmerge ;

: vmerge \ -- | v v'-- v" 
  zst yst setmove
  yst@ zst> + 1+
  yst zst setmove
  zst! ;

: _fence \ ad -- | x -- {x} 
  dup >r stack@ ?obj 
  case 0 of -2 r@ >stack endof 
       1 of r@ stack@ 1- r@ >stack endof
       2 of r@ stack@ 2 - r@ >stack endof
  endcase rdrop ;

: xfence xst _fence ;
: yfence yst _fence ;
: zfence zst _fence ;

: set-sort2 \ -- | s -- n1...nk -2k
  0 loc{ counter } 0 >xst 0 >yst
  foreach
  ?do zst@ ?obj
     case 0 of counter 1+ to counter zst> endof
          1 of zfence xst zst setmove zetmerge zst xst setmove endof
          2 of zfence yst zst setmove zetmerge zst yst setmove endof
     endcase
  loop counter sort 2* negate >zet
  xst zst setmove zetmerge
  yst zst setmove zetmerge ;

: adswap \ ad1 ad2 -- 
  over @ over @ swap rot ! swap ! ; 

: singlepart \ ad1 ad2 -- ad
  tuck 2dup @ locals| p ad | swap                \ ad2 ad2 ad1
  do i @ p <                                     \ ad2 flag
     if ad i adswap ad cell + to ad then cell    \ ad2 cell
  +loop ad adswap ad ;                           \ ad 

: qsort \ ad1 ad2 --      pointing on first and last cell in array
  begin
    2dup < 0= if 2drop exit then
    2dup - negate 1 rshift >r \ keep radius (half of the distance)
    2dup singlepart 2dup - >r >r \ ( R: radius distance2 ad )
    r@ cell - swap r> cell+ swap \ ( d-subarray1 d-subarray2 )
    2r> u< if 2swap then recurse \ take smallest subarray first
  again \ tail call optimization by hand
;

: qsort~ \ ad1 ad2 --      pointing on first and last cell
  2dup < 
  if 2dup singlepart >r
     swap r@ cell - recurse
     r> cell + swap recurse 
  else 2drop 
  then ; \ problem with sorting sorted big set

: set-sort \ -- | s -- n1...nk -2k ???
  xst @ cell+ 0 locals| counter ad1 | 0 >yst
  foreach
  ?do zst@ ?obj
     case 0 of counter 1+ to counter zst> >xst endof
          1 of zfence yst zst setmove zetmerge zst yst setmove endof
          2 of zfence yst zst setmove zetmerge zst yst setmove endof
     endcase
  loop ad1 dup counter 1- cells + qsort counter 2* negate >xst
  xst zst setmove 
  yst zst setmove zetmerge ;

: next-element-ad \ ad1 -- ad2
  dup @ objsize cells - ;

: smember \ n -- flag | s -- 
  zst@ cs false loc{ m flag } 
  foreach 
  ?do zst@ 0< 
     if m zst@ cs 1+ - to m zdrop 
     else m 1- to m dup zst> 2dup > 
        if false to flag 2drop 
           m cells negate zst +! leave 
        then = 
        if true to flag 
           m cells negate zst +! leave 
        then 
     then 
  loop drop flag ; 

: vect= \ s -- flag | s' --
\ s non empty list not including non empty sets
  dup zst@ = 0=
  if zdrop cs 0 ?do drop loop false exit
  then true loc{ flag } zst> drop cs 0
  ?do flag
     if zst> = 0= if false to flag then
     else zst> 2drop 
     then
  loop flag ;

: vector= \ -- flag | s s' --
  zet> vect= ;

: vmember \ -- flag | s s' --
  zswap zst yst setmove
  zst@ cs false loc{ m flag }
  foreach
  ?do zst@ ?obj 
    case 0 of m 1 - to m zst> drop endof
         1 of m zst@ cs 1+ - to m 
              yst zst setcopy vector=
              if true to flag
                 m cells negate zst +! leave
              then endof
         2 of m zst@ cs 1+ - to m 
              zst@ cs 1+ cells negate zst +! endof
    endcase
  loop yst setdrop flag ;

: secobjad \ -- ad | x y -- x y
  zst @ zst@ 0< if zst@ cs 1+ cells - else cell - then ;

: routout \ -- x | x s -- s
  secobjad dup @ swap dup cell+ swap zst@ cs 1+ cells move zst> drop ;

0 value 'subset  
: subset \ -- flag | s s' --
  'subset execute ;

: zet= \ -- flag | s s' --
  zover zover subset
  if zswap subset
  else zdrop zdrop false
  then ; 

: zet-member \ -- flag | s s' -- 
  zswap zst yst setmove
  begin zst@                         \ set not empty?
  while zsplit zst@ ?obj 2 =      \ element is a set?
     if yst zst setcopy zet=  
        if yst setdrop zdrop true exit then
     else zst@ ?obj if zdrop else zst> drop then
     then 
  repeat yst setdrop zdrop false ;

: member \ -- flag | x s --
  secobjad @ ?obj
  case 0 of routout smember endof
       1 of vmember endof
       2 of zet-member endof
  endcase ;

:noname \ -- flag | s s' --          \ the subset code
  zst @ cell - 2@ or 0=
  if zdrop zdrop true exit then      \ true if both sets are empty
  zswap zst yst setmove
  begin yst@                         \ set is not empty?
  while ysplit yst@ ?obj
     if yst zst setmove zover member
     else yst> zdup smember 
     then 0= if yst setdrop zdrop false exit then
  repeat yst> drop zdrop true ; to 'subset

\ Set algebra_____

: reduce \ -- | s -- s' 
  0 >yst foreach
  ?do zfence zdup zst> drop
     yst zst setcopy member
     if zdrop
     else yst zst setmove
        zetmerge zst yst setmove
     then
  loop yst zst setmove ;

: union \ -- | s s' -- s"
  zetmerge set-sort reduce ;

: intersection \ -- | s s' -- s" 
  0 >xst zst yst setmove
  begin zst@
  while zsplit zfence zdup zst> drop
     yst zst setcopy member
     if xst zst setmove zetmerge zst xst setmove
     else zdrop
     then 
  repeat zdrop yst setdrop
  xst zst setmove reduce ; 

: diff \ s s' -- s" 
  0 >xst zst yst setmove 
  begin zst@
  while zsplit zfence zdup zst> drop
     yst zst setcopy member
     if zdrop 
     else xst zst setmove zetmerge zst xst setmove
     then
  repeat zdrop yst setdrop
  xst zst setmove reduce ;

: multincl \ s x -- s'
  0 >xst zfence zst yst setmove
  begin zst@
  while zsplit yst zst setcopy union zfence
     xst zst setmove zetmerge zst xst setmove
  repeat zdrop yst setdrop xst zst setmove ;

: powerset \ s -- s'
  zst@ 0= if -2 >zst exit then
  zsplit zfence zst yst setmove recurse
  zdup yst zst setmove zst> drop multincl
  zetmerge ;

: cartprod \ s s' -- s"
  zst yst setmove
  zst xst setcopy xst> drop cardinality 0 0 >zst
  ?do xfence -1 xst+! 
     yst setdup
     begin yst@
     while ysplit yfence -1 yst+!
        xst zst setcopy
        yst zst setmove vmerge
        zfence
        zetmerge
     repeat yst> drop xst setdrop 
  loop yst setdrop ;

\ {x1,...,xn} -- {{x1},...,{xn}}
: infence \ -- | s -- s' 
  0 >xst foreach 
  ?do zfence zfence
     xst zst setmove zetmerge
     zst xst setmove 
  loop xst zst setmove ; 

\ p(A,k)=p(A\{f(A)},k)+(p(A\{f(A)},k-1)%f(A))
: power# \ n -- | s -- s' 
  ?dup 0= if zdrop 0 >zst zfence exit then 
  dup 1 = if drop infence exit then 
  dup zdup cardinality = 
  if drop zfence exit then 
  dup 1 = if drop infence exit then 
  zsplit zfence zst xst setmove 
  dup zdup recurse 
  zswap 1- recurse xst zst setmove 
  zst> drop multincl 
  zetmerge ; 

\ from rosetta code
: choose \ n k -- nCk 
  1 swap 0
  ?do over i - i 1+ */
  loop nip ;

\ {s1,...,sn} -- s1U...Usn
: multiunion \ -- | s -- s'
  foreach 0 >zst
  ?do zetmerge
  loop set-sort reduce ;

\ {s1,...,sn} s' -- {s1Us',...,snUs'}
: zetcup \ -- | s s' -- s"
  zst xst setmove 0 >yst foreach
  ?do xst zst setcopy union zfence
     yst zst setmove zetmerge zst yst setmove
  loop xst setdrop yst zst setmove ;

\ {s1,...,sn} s' -- {s1&s',...,sn&s'}
: zetcap \ -- | s s' -- s"
  zst xst setmove 0 >yst foreach
  ?do xst zst setcopy intersection zfence
     yst zst setmove zetmerge zst yst setmove
  loop xst setdrop yst zst setmove ;

\ {s1,...,sn} {t1,...,tm} -- {siUtj}ij
: zetunion \ -- | s s' -- s"
  0 >xst zst yst setmove foreach
  ?do yst zst setcopy
     zswap zetcup
     xst zst setmove union
     zst xst setmove
  loop yst setdrop xst zst setmove ; 

: functions \ -- | s s' -- s"
  secobjad @ 0= if zdrop -2 >zst exit then
  secobjad @ -2 = if cartprod infence exit then
  zswap zsplit zfence zst xst setmove
  zover recurse zswap xst zst setmove
  zswap cartprod infence zetunion ;

\ Input of sets_____

0 create match ,
true value sort?

: { \ --
  1 match +! depth >xst true to sort? ;

: } \ x1...xk -- 
  depth xst> - 2* negate
  -1 match +! >zet sort?
  if set-sort2 then reduce match @
  if zet> then true to sort? ; 

: q  xst stack-cl yst stack-cl zst stack-cl 0 match ! abort ;

: (  { ;

: ) \ x1...xk --
  depth xst> - 2* 1+ negate 
  -1 match +! >zet match @ if zet> then ; 

\ cond ( n -- flag )
: all dup = ;
: odd 1 and ; 
: even 1 xor ;
: 1mod4 4 mod 1 = ; 
: 3mod4 4 mod 3 = ; 
: sqr dup sqrtf dup * = ;
: sqrfree dup radical = ;
: twinprime dup prime over 2 + prime rot 2 - prime or and ;  
: ntwinprime dup prime swap twinprime 0= and ;
: semiprime bigomega 2 = ;
: primepower smallomega 1 = ;
: biprime smallomega 2 = ;

: 2sqrsum dup 0 
  ?do dup i dup * - dup
     0< if drop false leave then 
     sqr if true leave then
  loop nip ;

\ 30 70 | odd
: | \ m n -- x1...xk 
  swap ' loc{ xt }
  ?do i xt execute if i then loop false to sort? ;

\ relations (A,B,R), R subset of AxB

: unfence zst> drop ;
: yzcopy1 yst zst setcopy ;
: yzcopy2 yst setover yst zst setmove ;

: domain \ (A,B,R) -- A
  unfence zdrop zdrop ;

: codomain \ (A,B,R) -- B
  unfence zdrop znip ;

: rel \ (A,B,R) -- R
  unfence znip znip ;

: image \ R -- s
  { foreach ?do unfence zst> zst> drop loop } ;

: coimage \ R -- s
  { foreach ?do unfence zst> drop zst> loop } ;

: subimage \ R s -- s'
  zst yst setmove
  { foreach 
  ?do unfence zst> zst> yst zst setcopy smember 0=
     if drop then
  loop } yst setdrop ;

: subcoimage \ R s -- s'
  zst yst setmove
  { foreach 
  ?do unfence zst> zst> yst zst setcopy swap smember 0=
     if drop then
  loop } yst setdrop ;

: func? \ -- flag | (A,B,R) --
  unfence znip 
  zst yst setmove true 
  begin zst@ 
  while zsplit zst> yst zst setcopy >zst zfence 
     subimage cardinality 1 = 0=
     if 0= zdrop yst setdrop exit then
  repeat zdrop yst setdrop ;

: eval \ x -- y | f --
  >zst zfence subimage unfence zst> ;

: pair \ s1 s2 -- (s1,s2)
  zswap zst@ 2 - zswap zst@ 2 - + 1- >zst ;

: triplet \ s1 s2 s3 -- (s1,s2,s3)
  zrot zst@ 2 - zrot zst@ 2 - zrot zst@ 2 - + + 1- >zst ;

: composition \ (A,B,R) (B,C,S) -- (A,C,SR) 
  0 >xst
  unfence zrot zdrop zrot unfence       \ C S A B R 
  zst yst setmove zdrop zswap           \ C A S
  zst yst setmove                       \ R S in yst 
  zswap zover zover cartprod            \ A C A×C 
  begin zst@ 
  while zsplit infence
     yzcopy1 zover zsplit znip subcoimage
     zst xst setmove
     yzcopy2 zover zsplit zdrop unfence subimage 
     xst zst setmove intersection zst@ zdrop 
     if unfence unfence zst> unfence >zst -5 >zst zfence
        xst zst setmove zetmerge zst xst setmove
     else zdrop
     then 
  repeat zdrop yst setdrop yst setdrop
  xst zst setmove triplet ;

: path? \ x y -- flag | E --
  swap >zst zfence 
  begin zover zover ztuck subimage      \ E s s s'
     union zdup dup smember             \ E s s" f
     if drop zdrop zdrop zdrop true exit then
     zswap zover zet=                   \ E s" s=s"
     if drop zdrop zdrop false exit then
  again ;

: ipair \ m n -- | -- (m,n)
  2>r ( 2r> ) ;

: loopset \ V -- s
  { foreach ?do ( zst> dup ) loop } ;

: rand-pair \ |V| -- | -- s
  dup random 1+ swap random 1+ ipair ; 

: rand-digraph \ |V| |E| -- | -- (V,E)
  { over 1+ 1 ?do i loop } 
  0 >zst 
  begin over rand-pair zfence union zdup cardinality over = 
  until 2drop 
  pair ; 

: rand-noloop-digraph \ |V| |E| -- | -- (V,E)
  { over 1+ 1 ?do i loop } 
  0 >zst 
  begin over rand-pair zfence union 
     zover loopset diff 
     zdup cardinality over = 
  until 2drop pair ; 

: sourceset \ (V,E) -- s 
  unfence image diff ; 

: sinkset \ (V,E) -- s 
  unfence coimage diff ; 

: xzmerge \ s -- 
  xst zst setmove
  zswap zetmerge 
  zst xst setmove ; 
  
: xzmergered
  xst zst setmove
  zswap zetmerge 
  set-sort reduce
  zst xst setmove ; 
  
: toposort \ (V,E) -- s
  0 >xst                           \ empty set in x
  zdup sourceset zst yst setmove   \ source nodes in y
  unfence znip                     \ drop V keep E
  begin yst@                       \ while source nodes left
  while ysplit yst> dup            \ remove node m
     zdup >zst zfence zdup xzmerge \ add m to the set in x
     subimage                      \ set of all n: m?n
     begin zst@                    \ while that set non empty
     while zsplit zst> zswap       \ remove node n, E tos
        2dup ipair zfence diff     \ E:=E\{(m,n)}
        dup zdup >zst zfence       \ build set of all nodes..
        subcoimage zst@ 0=         \ ..pointing at n
        if >yst yfence ymerge      \ add n to y-set if empty
        else drop                  \ else drop n
        then zdrop zswap           \ drop set, swap E back
     repeat zdrop drop             \ drop empty set and node m
  repeat yst> drop zst@ zdrop      \ drop empty set and E
  if xst setdrop 0 >zst            \ if |E|>0 flag with empty set
  else xst zst setmove             \ else move the x-set to zst
     zst> 1- >zst                  \ mark it as ordered list
  then ; 

: dag? \ -- f | (V,E) -- 
  toposort zst@ 0= 0= zdrop ;

: rand-acyclic-digraph \ m n -- | -- (V,E)
  begin 2dup rand-noloop-digraph zdup dag? 0=
  while zdrop
  repeat 2drop ;

\ Permutation groups

\ The number of permutations in a set
: ord \ -- n | s -- s
  zst> zst> 2dup >zst >zst
  cs 1+ swap cs swap / ;

\ The number of elements to be permuted in v
: numb \ -- n | v --
  zst@ cs zdrop ;

\ j=v(i)
: pmaps \ i -- j | v --
  zdrop cells zst @ + @ ;

\ composition of permutations as functions
: permcomp \ v1 v2 -- v1v2
  ( zst@ cs 1+ 1
  do zover zover i pmaps pmaps
  loop ) znip znip ; 

\ generation of cyclic permutation group
: pgen \ v -- s
  zst yst setcopy -1 1
  do zdup yzcopy1 permcomp zdup yzcopy1 vector=
     if numb 1+ i * 2* negate >zst leave then
  loop yst setdrop ; 

\ right coset
: prcoset \ s v -- s' 
  0 >xst
  zst yst setmove
  foreach
  ?do yzcopy1 permcomp zfence xzmerge
  loop yst setdrop xst zst setmove ;

\ left coset
: plcoset \ v s -- s'
  0 >xst
  zswap zst yst setmove
  foreach
  ?do yzcopy1 zswap permcomp zfence xzmerge
  loop yst setdrop xst zst setmove ;

\ componentwise composition of permutation sets
: permset* \ -- | s1 s2 -- s3
  0 >xst 
  zst yst setmove 
  foreach 
  ?do yzcopy1 plcoset 
     xzmergered
  loop yst setdrop 
  xst zst setmove ;

: permgroup? \ -- flag | s -- 
  zdup zdup permset* zet= ; 

\ Generation of standard permutations
: pidentity \ n -- | -- v
  >r ( r> 1+ 1 ?do i loop ) ;
  
: pcirc \ n -- | -- v
  >r ( r> dup 1 ?do i loop )  ;

: proll \ n -- | -- v
  >r ( r@ 1- dup 1 do i loop r> ) ; 

\ The number of element to be permuted in permutations in s
: perm# \ -- n | s -- s
  zst> zst> tuck >zst >zst cs ; 

\ Calculate the inverse permutation
?undef cell/ [if]
cell 4 = [if] : cell/ 2 rshift ; [then]
cell 8 = [if] : cell/ 3 rshift ; [then]
[then]

: pinv \ v -- v'
  zdup adn2 drop adn1 -rot loc{ a2 a1 } cell/ 1
  do i dup 1- cells a2 + @ 1- cells a1 + ! loop znip ;

\ add the inverses to all permutations in s
: adinv \ s -- s'
  0 >xst zdup xzmerge foreach 
  do pinv zfence xzmerge 
  loop xst zst setmove reduce ;

\ generates the group s' from the generators in s
: generate \ s -- s'
  zst yst setcopy 0 >xst foreach
  ?do pgen xzmerge 
  loop xst zst setmove reduce 1
  begin yzcopy1 zswap permset* 
     yzcopy1 permset* ord tuck =
  until yst setdrop drop ;

\ generate set of groups s' from set of generators s
: multigen \ s -- s'
  0 >xst foreach 
  ?do generate zfence xzmerge
  loop xst zst setmove reduce ;

\ generates the group s' from the generators in s, if |s'|=<n
: limgenerate \ n -- flag | s -- s'
  loc{ n }
  0 >xst
  zst yst setcopy
  foreach
  ?do pgen xzmerge 
  loop xst zst setmove reduce
  1
  begin ord n >
     if yst setdrop drop false exit then 
     yzcopy1 zswap permset* 
     ord n >
     if yst setdrop drop false exit then 
     yzcopy1 permset* ord tuck =
  until yst setdrop drop true ;

\ generate set of groups s' from set of generators s
: limmultigen \ n -- | s -- s'
  0 >xst foreach 
  ?do dup limgenerate if zfence xzmerge else zdrop then
  loop xst zst setmove reduce drop ;

\ Set of all subgroups of s
: psubgroups \ s -- s'
  ord dup >r pollard# over r> swap / loc{ n } drops
  perm# pidentity zfence zfence zover zfence zmerge
  zst xst setmove foreach
  do xst zst setcopy zswap multincl 
     n limmultigen xzmergered
  loop xst zst setmove ;

: psub? \ -- flag | s s' --
  zover zswap subset 0= 
  if zdrop false exit 
  then permgroup? ;
  
: pnsub? \ -- flag | s s' --
  zover zover psub? 0= 
  if zdrop zdrop false exit then
  zswap zst yst setmove
  begin zst@
  while zsplit yzcopy1 zover prcoset 
     zswap yzcopy1 plcoset zet= 0=
     if zdrop yst setdrop false exit then
  repeat zdrop yst setdrop true ;

: pnsubgroups \ s -- s'
  zst yst setcopy
  psubgroups
  0 >xst
  begin zst@
  while zsplit zdup yzcopy1 pnsub?
     if zfence xzmerge else zdrop then
  repeat zdrop yst setdrop xst zst setmove ;
  
: setint+ \ n -- | s -- s'
  0 >xst foreach
  ?do zst> over + >zst zfence xzmerge
  loop drop xst zst setmove ;

: set+ \ s s' -- s"
  0 >xst 
  zst yst setmove
  foreach
  ?do zst> yzcopy1 setint+ xzmergered
  loop yst setdrop 
  xst zst setmove ;

1 value num
: numcoprime \ n -- flag
  num ugcd 1 = ;

\ Some finite groups

\ generates the group s' with known order from the generators in s
: #generate \ n -- | s -- s'
  zst yst setcopy 0 >xst foreach
  do pgen xzmerge loop xst zst setmove reduce
  begin yzcopy1 zswap permset* 
     yzcopy1 permset* ord over < 0=
  until yst setdrop drop ;

\ cyclic group of permutations of 1...n
: cyc \ n -- | -- s
  pcirc pgen ;
false [if]
\ symetric group of permutations of 1...n, n<6
: sym \ n -- | -- s 
  loc{ n } n 2 >
  if n pcirc zfence n proll zfence zmerge n ufaculty #generate
  else 2 = if ( 2 1 ) pgen else ( 1 ) pgen then
  then ;
[then]
\ dihedral group of permutations of 1...n
: dih \ n -- | -- s
  dup >r pcirc zfence
  ( 1 r@ ?do i -1 +loop ) zfence 
  zetmerge r> 2* #generate ; 
false [if]
\ alternating group of permutations of 1...n, n<6
: alt \ n -- | -- s   n>2
  dup 3 = if drop ( 2 3 1 ) pgen exit then
  dup 1 and
  if >r 
     { r@ pcirc 
     ( r@ 2 - 1 do i loop r@ 1- r@ r@ 2 - )
     } r> ufaculty 2/ #generate
  else >r 
     { ( r@ 2 do i loop 1 r@ )
     ( r@ 2 - 1 do i loop r@ 1- r@ r@ 2 - )
     } r> ufaculty 2/ #generate
  then ;
[then]
\ quaternion group group of permutations of 1...8
: q8 \ -- s
  { ( 2 4 6 7 3 8 1 5 ) ( 3 5 4 8 7 2 6 1 ) } 8 #generate ;

\ The product of two permutation groups given as a permutation group

: rext \ n -- | v -- v'
  >r ( r> zst@ cs do i 1+ loop )
  1 zst+! zswap 1 zst+! zswap zmerge -1 zst+! ;

: lext \ n -- | v -- v'
  dup >r ( r> zst@ cs - 1+ 1 do i loop ) 1 zst+!
  zswap zst@ tuck cs - loc{ x y }
  1 zst+! foreach
  do zst> y + loop x 1+ >>zst
  zmerge -1 zst+! ;

: multirext \ n -- | s -- s'
  0 >xst foreach
  do dup rext zfence xzmerge
  loop drop xst zst setmove ;

: multilext \ n -- | s -- s'
  0 >xst foreach
  do dup lext zfence xzmerge
  loop drop xst zst setmove ;

\ the product of two groups s and s'
: gprod \ s s' -- s"
  ord zswap ord 2dup +
  dup multirext zswap
  multilext union * #generate ;
  
\ Pseudo isomorphism test

\ the set of cyclic subgroups
: pcsubs \ s -- s'
  0 >xst
  foreach
  do pgen zfence xzmerge
  loop xst zst setmove reduce ;
  
: card<> \ -- flag | s s' -- s s'
  zover cardinality zdup cardinality = 0= ;
  
: vect-sort \ v -- v'
  set-sort zst> 1- >zst ;

\ compute vector of orders of all cyclic subgroups in s
: pscan \ s -- v 
  0 foreach do cardinality swap 1+ loop 
  sort 2* 1+ negate >zet ;

: pseudoiso \ -- flag | s s' --
  card<>
  if zdrop zdrop false exit then 
  pcsubs zswap pcsubs card<>
  if zdrop zdrop false exit then
  pscan zswap pscan vector= ;

\ Fast generation of groups

: reverse-string \ ad n --
  2dup + 1- loc{ ad1 n ad2 } n 2/ 0
  ?do ad1 i + c@ ad2 i - c@ 
     ad1 i + c! ad2 i - c!
  loop ; 

: lex-perm1 \ ad n -- a1
  0 loc{ a1 } 2 - over + 
  do i c@ i 1+ c@ <
     if i to a1 leave then -1
  +loop a1 ;

: lex-perm2 \ ad n a1 -- a2
  0 loc{ a1 a2 } 1- over +
  do a1 c@ i c@ <
     if i to a2 leave then -1
  +loop a2 ;

: lex-perm3 \ a1 a2 --
  over c@ over c@
  swap rot c!
  swap c! ;

: lex-perm4 \ ad n a1 --   reverse from a1+1 to ad+n-1 
  1+ -rot            \ a1+1 ad n
  + over -           \ a1+1 ad+n-(a1+1) 
  reverse-string ; 

: nextp \ ad n -- 
  2dup 2dup          \ ad n ad n ad n
  lex-perm1 dup 0=
  if 2drop 2drop drop exit 
  then dup >r        \ ad n ad n a1
  lex-perm2 r>       \ ad n a2 a1
  tuck swap          \ ad n a1 a1 a2
  lex-perm3          \ ad n a1
  lex-perm4 ;

: n>str \ n -- ad n
  dup 0 do i 49 + pad i + c! loop pad swap ;

: str>vect \ ad n -- | -- s
  loc{ ad n } n dup 0
  do ad i + c@ 15 and >zst loop 2* 1+ negate >zst ;

: sym \ n -- | -- s
  n>str loc{ ad n }
  n dup ufaculty dup 0
  do ad n str>vect 
     ad n nextp
  loop swap 1+ * 2* negate >zst ;

: perm> \ m -- n | s --
  loc{ m } 0
  foreach do zst> m > + loop negate ;
  
: #perm \ -- n | s -- 
  0
  begin zst@ -3 <
  while zsplit zst> zdup perm> +
  repeat zdrop ;

: oddperm \ -- flag | s --
  #perm 1 and ; 

: alt \ n -- | -- s
  n>str loc{ ad n }
  n dup ufaculty dup 0
  do ad n str>vect zdup oddperm
     if zdrop then ad n nextp
  loop swap 1+ * negate >zst ;
  
\ Simple graphs

: subgraph \ -- flag | (V,E) (V',E') -- 
  unfence zrot unfence 
  zrot subset
  zswap subset and ;

: edges~ \ E' V -- E
  2 power# intersection ;

: edges \ E' V -- E
  0 >xst 
  zst yst setmove 
  foreach \ {u,v}?E'
  ?do zdup unfence yzcopy1 member 
     if yzcopy1 member
        if zfence xzmerge
        else zdrop
        then
     else zst> drop zdrop
     then
  loop yst setdrop xst zst setmove ;

: randgraph \ m n v -- | -- (V,E)
  loc{ m n v } 
  0 >xst
  { v 0 do i 1+ loop } 
  zdup 2 power# foreach \ {u,v}
  do n random m < 
     if zfence xzmerge
     else zdrop
     then
  loop xst zst setmove pair ;

\ V={x?V'|y?V" & {x,y}?E'}
\ E={{x,y}?E'|x?V & y?V}
: extend \ E' V" -- (V,E)
  zswap zst yst setmove 
  zst xst setcopy 
  foreach \ v?V"
  do zst> yzcopy1
     begin zst@ 
     while zsplit zdup dup smember
        if xzmerge
        else zdrop
        then
     repeat zet> 2drop
  loop xst zst setmove 
  set-sort reduce
  yst zst setmove 
  zover edges pair ;

: isolated-vertices# \ -- n | (V,E) --
  unfence 0 dup loc{ flag }
  zst yst setmove
  foreach
  do zst> yzcopy1 true to flag
     begin zst@ flag and
     while zsplit dup smember 0= to flag
     repeat zdrop drop flag -
  loop yst zst setmove zdrop ;

: components# \ -- n | (V,E) --
  zdup 0 >xst
  unfence 
  znip zst yst setcopy
  foreach
  do begin yzcopy1 zover
        extend unfence zdrop ztuck zet=
     until zfence xzmerge
  loop yst setdrop 
  xst zst setmove reduce cardinality
  isolated-vertices# + ;

: forest? \ -- flag | (V,E) -- 
  zdup unfence 
  cardinality \ e
  cardinality \ v
  components# \ c
  rot + = ;

: vector-sort \ s -- s'
  set-sort zst> 1- >zst ;

: cycle \ -- flag | E -- 
  zdup multiunion 
  zdup cardinality true loc{ v flag } 
  zover zdup cardinality v = 0=
  if triplet zdrop false exit 
  then pair components# 1 > 
  if zdrop false exit
  then 0 >xst foreach
  do xzmerge
  loop xst zst setmove
  zet> cs sort 2 - 0
  do over = flag and to flag
     over > flag and to flag 
  +loop = flag and ;

: clear-table \ s --
  pad 0 foreach 
  do zst> max
  loop cells erase ;
  
: cyc!check \ n -- flag
  cells pad + 1 over +! @ 2 > ;

\ Test if (V,E) is 2-regular 
: 2-regular \ -- flag | (V,E) --
  unfence zswap clear-table
  begin zst@ 
  while zsplit unfence 
     zst> cyc!check if zst> drop zdrop false exit then 
     zst> cyc!check if zdrop false exit then
  repeat zdrop true ;

\ Testing conjectures

: intcond \ low hi xt -- | -- s   "intervall condition"
  loc{ xt } 
  swap 0 -rot
  ?do i xt execute 
     if i >zst 1+ then
  loop 2* negate >zst ;

: setcond \ xt -- | s -- s'       "set condition"
  loc{ xt } 0
  foreach
  ?do zst> dup xt execute
     if >xst 1+ else drop then
  loop dup 0
  ?do xst> >zst 
  loop 2* negate >zst ;

: intimage \ low hi xt -- | -- s  "intervall image"
  loc{ xt } 
  swap 2dup
  ?do i xt execute >zst
  loop - 2* negate >zst
  set-sort reduce 
;

: setimage \ xt -- | s -- s'      "set image"
  loc{ xt } 0
  foreach 
  ?do zst> xt execute >xst 1+
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst
  set-sort reduce ;

: square dup * ;                \ x → x²
: sqr>prime square nextprime ;  \ x → nextprime(x²)
: sqr<prime square prevprime ;  \ x → prevprime(x²)
: foo dup totients mod ;        \ x → x(mod ?(x)) Euler's totient.

: paircond \ xt -- | s -- s'
  loc{ xt } 0
  foreach
  ?do zdup zet> drop xt execute
     if zst xst setmove 1+ else zdrop then
  loop 6 * negate >xst
  xst zst setmove ;

: pairimage \ xt -- | s -- s'
  loc{ xt } 0
  foreach
  ?do 1+ zet> drop xt execute >xst
  loop dup 0 
  ?do xst> >zst
  loop 2* negate >zst
  set-sort reduce ;

: coprime ugcd 1 = ;
: divide swap mod 0= ; 

: factorset \ n -- set
  pollard# loc{ n }
  n 0 do >zst loop
  n 2* negate >zst 
  set-sort 
  zst> 1- >zst ;

: set-of-factors \ s -- s'
  0 >xst
  foreach
  do zst> factorset zfence xzmerge loop
  xst zst setmove ;

\ rabin-miller strong pseudoprime test

: rs \ u -- s | -- r
  b1- nextfree first 0 >xs
  do i @ if i >ys leave then 1 xs+! cell
  +loop ys> @ bits 0
  do dup 1 and if i leave then u2/
  loop nip xs> lbits lshift +
  dup brshift ;

: digit= \ u -- | n -- f	u=n?
  len1 cell > if drop bdrop false exit then
  first @ = bdrop ;

: pseudo1 \ xsi s m -- | -- f
  b**mod 1 digit= ;

: pseudo2 \ xsi s m -- | r -- f
  >bx bx b1- >bx false >ys 0
  do bover bover i blshift by b**mod
     bx b=
     if true ys! leave then
  loop xdrop xdrop bdrop bdrop ys> ;

: bmiller \ u -- u | -- f		u odd >3
  >bx bx btwo bx rs >zs bover bover
  bx pseudo1 ?dup
  if xdrop bdrop bdrop zsdrop exit
  then bx> zs> pseudo2 ;
\ u is of the form u=1+s*2^r, where s is odd
\ given any number 1 < xsi < u
\ if xsi^s=1[mod u] or
\ if it exist j: 0 =< j < r with
\ xsi^[s*2^j]=-1[mod u]
\ then u is pseudoprime.

: bprime \ b -- flag
  len1 cell >
  if bmiller bdrop
  else b>s prime
  then ;

: bnextprime \ b -- p 
  b1or 
  begin bdup bprime 0=
  while b2+
  repeat ;

: int2cond \ low hi n xt -- | -- s   "intervall two-condition"
  locals| xt n | 
  swap 0 -rot
  ?do i n xt execute 
     if i >zst 1+ then
  loop 2* negate >zst ;

: int2image \ low hi n xt -- | -- s  "intervall image"
  locals| xt n | 
  swap 2dup
  ?do i n xt execute >zst
  loop - 2* negate >zst
  set-sort reduce ;

: set2cond \ n xt -- | s -- s'       "set condition"
  locals| xt n | 0
  foreach
  ?do zst> dup n xt execute
     if >xst 1+ else drop then
  loop dup 0
  ?do xst> >zst 
  loop 2* negate >zst ;

: set2image \ n xt -- | s -- s'      "set image"
  locals| xt n | 0
  foreach 
  ?do zst> n xt execute >xst 1+
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst
  set-sort reduce ;

variable zp
variable cf2

: condition  ' 0 cf2 ! sp@ zp ! ;
: function  ' 2 cf2 ! sp@ zp ! ;
: 2dim  ' -1 cf2 ! sp@ zp ! ;
: syntax  sp@ zp @ - 0= if 0 0 else 1 then cf2 @ ;
: non all ;

\ e.g. 1 20 condition < 7 create-set
: create-set \ m n xt nr -- set
  syntax locals| cf k nr xt n m |
  k cf or
  case 0 of m n xt intcond endof
       1 of m n nr xt int2cond endof
       2 of m n xt intimage endof
       3 of m n nr xt int2image endof
  endcase ;

\ e.g. condition > 5 filter-set
: filter-set \ set xt nr -- set'
  syntax locals| cf k nr xt |
  cf 0< if xt paircond exit then k
  case 0 of xt setcond endof
       1 of nr xt set2cond endof
  endcase ;

\ e.g. 2dim + transform-set
: transform-set \ set xt nr -- set'
  syntax locals| cf k nr xt |
  cf 0< if xt pairimage exit then k
  case 0 of xt setimage endof
       1 of nr xt set2image endof
  endcase ;

: zgaps \ s -- s'
  0 locals| n | 
  foreach 1+
  do zst> zst@ - >xst 
     n 1+ to n
  loop zst> drop
  n 2* negate >xst
  xst zst setmove 
  set-sort reduce ;

: hist \ a1 ... ak k -- a1 ... ai i ak nk 
  2dup 0 locals| n k1 a k |
  begin dup a = k1 and
  while n 1+ to n 
     k1 1- to k1 drop
  repeat k n - a n ;

\ testing for small (fast) single number divisors
\ of big number w in the intervall n,m-1
: sfac \ w -- w ?v | m n -- f 
  beven if 2drop 2 bdup b2/ exit then
  0 locals| flag | 
  do bdup i pnr@ bs/mod 0= 
     if i pnr@ to flag leave then bdrop
  loop flag ;

: sfacset \ b -- set
  0                           \ count of the number of elements
  begin pi_plim 1 sfac ?dup 
  while >zst 2 - bnip
  repeat bdrop >zst reduce ;


\ String stack

: clearbuf \ ad --
  dup cell+ swap ! ;

variable stp

0x4000 constant stlim
stlim allocate throw dup constant stbuf clearbuf
\ ascii buffer, at stbuf is loaded address to first free byte

0x1000 constant stalim
stalim allocate throw dup constant staddr clearbuf
\ address buffer, at staddr is loaded address to first free cell

: clstr  0 stp ! stbuf clearbuf staddr clearbuf ;

: >str \ ad n --    put string on stack
  tuck             \ n ad n
  stbuf @ dup      \ n ad n a a
  staddr @ !       \ n ad n a
  cell staddr +!
  swap move        \ n
  stbuf +! 
  1 stp +! ;

: str@ \ -- ad n
  stp @ cells staddr + @ 
  dup stbuf @ swap - ;

: str> \ -- ad n
  str@ over stbuf !
  cell negate staddr +!
  -1 stp +! ;

: sempty \ -- flag
  stp @ 0= ;

\ addr to the ith string from the bottom of the stack 
: ist@ \ i -- ad n     i=1,...
  dup stp @ = 
  if cells staddr + @ dup stbuf
  else cells staddr + dup @ dup rot cell+ 
  then @ swap - ;

\ addr to the kth string from the top of the stack
: spickad \ k -- ad n
  stp @ swap - ist@ ;

\ print string stack
: .str stp @ 0 ?do cr i spickad type loop ;

: str. str> type ;

\ enter string from commando line
: s [char] " parse >str ;
\ use s" example" >str in definitions

: sdup stp @ ist@ >str ;
: sdrop str> 2drop ;
: sover stp @ 1- ist@ >str ;
: soover stp @ 2 - ist@ >str ;
: snip str> sdrop >str ;
: sswap sover str> str> sdrop >str >str ;
: srot soover str> str> str> sdrop >str >str >str ;
: stuck sswap sover ;
: spick spickad >str ;

: s& \ s1 s2 -- s1&s2
  -1 stp +! 
  staddr @ @
  cell negate staddr +!
  staddr @ ! ;

: clearstrstack \ -- 
  begin sempty 0=
  while sdrop
  repeat ;

\ lenghth of top string 
: sduplen \ s -- s | -- n
  str@ nip ;

\ length of second string
: soverlen \ s1 s2 -- s1 s2 | -- n
  1 spickad nip ;

\ the n leftmost chars in string
: sleft \ s -- s' | n --  
  str> drop swap >str ;

\ the n rightmost chars in string
: sright \ s -- s' | n -- 
  str> rot over swap - /string >str ;

\ split the string after the nth letter
: ssplit \ s -- s' s" | n --
  sdup dup sleft sswap
  sduplen swap - sright ;

\ the address to the jth letter in top string
: stopad \ s1 s2 -- s1 s2 | j -- adj    (in s2) j>0
  str@ drop 1- + ;

\ the address to the ith letter in second string
: ssecad \ s1 s2 -- s1 s2 | i -- adi
  1 spickad drop 1- + ;

\ split s2 if s1 is a part of s2 (true flag)
\ true -> s2=s3&s1&s4
: sanalyze \ s1 s2 -- s1 s3 s1 s4 / s2 | -- flag 
  soverlen                   \ m
  str@ 1 spickad search      \ m ad n f
  if nip sduplen swap -      \ m k-n
     ssplit                  \ m 
     ssplit true    
  else 2drop drop false 
  then ;

\ check if s1 is in s2
: substring \ s1 s2 -- s1 s2 | -- flag
  str@ 1 spickad search nip nip ;

\ replace s2 with s1 wherever in s3
: sreplace \ s1 s2 s3 -- s4
  begin sanalyze
  while snip 3 spick sswap s& s&
  repeat snip snip ;

\ string comparison 
: scomp \ s1 s2 -- | -- n    -1:s1>s2, +1:s1<s2, 0:s1=s2
  str> str> 2swap compare ;

\ put an empty string on the stack
: snull pad 0 >str ; 

\ conc. signs to top string on stack
: schr& \ s -- s' | ch --
  >r str> 2dup + r> swap c! 1+ >str ;

: sbl& bl schr& ;
: s,& [char] , schr& ;
: s.& [char] . schr& ;
: s;& [char] ; schr& ;
: s:& [char] : schr& ;
: s?& [char] ? schr& ;
: s!& [char] ! schr& ;
: s-& [char] - schr& ;
: s|& [char] | schr& ;
: s{& [char] { schr& ;
: s}& [char] } schr& ;

\ same length?
: slen= \ s1 s2 -- | -- flag
  str> nip str> nip = ;

\ remove ending spaces
: strail \ s -- s'  
  str@ -trailing ;

: >capital \ ch -- ch'
  [char] _ and ;

: >common \ ch -- ch'
  [char] ` or ;
 
: capital \ ch --flag
  [char] A [char] Z 1+ within ;

: common \ ch -- flag
  [char] a [char] z 1+ within ;

\ lower letters, eng.
: slower \ s -- s'
  str@ over + swap
  do i c@ capital
     if i c@ >common i c! then
  loop ;

\ upper letters, eng.
: supper \ s -- s'
  str@ over + swap
  do i c@ common
     if i c@ >capital i c! then
  loop ;

\ Unsigned double from string
: str>ud \ s -- s' | -- ud flag
  0. str@ dup >r >number dup >r >str snip 2r> > ;

\ Double from string
: str>d \ s -- s' | -- d flag
  1 stopad c@ [char] - = dup
  if sduplen 1- sright
  then str>ud >r rot if dnegate then r> ;

\ Create string of set or ordered sequence
: set>str \ set -- string   
  snull foreach over >r
  do zst> loop r> 0
  do schr& loop ;

: str>seq \ string -- sequence
  ( sduplen 1+ 1
  do i stopad c@
  loop ) sdrop ;

: seq>set \ seq -- set
  zst> 1+ >zst
  set-sort reduce ;

\ {(104,101,106),(100,117),(103,108,97,100,101)}
: z>s \ seq -- str
  snull s{& foreach
  do set>str s& s,& 
  loop str> 1- >str s}& ;

: snobl \ s -- s'      remove all blanks
  snull snull sbl& srot
  sreplace ;

: sjustabc \ s -- s'   remove all signs but eng. letters
  sduplen 1+ 1
  do i stopad c@ dup common swap capital or 0=
     if bl i stopad c! then
  loop snobl ;

\ s {hello there,all together,sentence}"
: s>z \ string -- set
  str> 1 /string 1- >str
  snull s,& sswap {
  begin sanalyze
  while snip sswap str>seq
  repeat str>seq } sdrop ;

\ union of stringsets
: sunion \ s1 s2 -- s3
  s& snull s,& s" }{" >str srot sreplace
  s>z set-sort reduce z>s ;

: sintersection \ s1 s2 -- s3
  s>z s>z intersection z>s ;

: sdiff \ s1 s2 -- s3
  s>z s>z zswap diff z>s ;

: alphabet \ s -- s'
  { sduplen 1+ 1
  do i stopad c@
  loop } sdrop set>str ;

\ bioinformatics --------------

\ Hamming distance
: hamming \ s1 s2 -- s1 s2 | -- n 
  0 1 spickad drop str@ 0  
  do over i + c@ 
     over i + c@ = 0=
     if rot 1+ -rot then
  loop 2drop ;

\ Wagner-Fischer algorithm

: distad \ s1 s2 -- s1 s2 | i j -- addr
  soverlen 1+ * + cells pad + ;

: distinit \ s1 s2 -- s1 s2 
  soverlen 1+ 0 do i i 0 distad ! loop
  sduplen 1+ 0 do i 0 i distad ! loop ;

\ Levenshtein distance
: editdistance \ s1 s2 -- s1 s2 | -- lev   
  distinit sduplen 1+ 1
  do soverlen 1+ 1
     do i ssecad c@ j stopad c@ =
        if i 1- j 1- distad @ 
        else i 1- j distad @ 1+              \ a deletion
             i j 1- distad @ 1+              \ an insertion
             i 1- j 1- distad @ 1+           \ a substitution
             min min 
        then i j distad !
     loop 
  loop soverlen sduplen distad @ ;

\ -------------------------

?undef sp0 [if]
s0 constant sp0
r0 constant rp0
[then]

: new-data-stack \ u -- 
  dup aligned allocate throw + dup sp0 ! sp! ; 

100000 cells new-data-stack
100001 cells allocate throw 100000 cells + align rp0 ! q
