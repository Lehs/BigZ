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

: >st \ ad n -- 
  tuck             \ n ad n
  stbuf @ dup      \ n ad n a a
  staddr @ !       \ n ad n a
  cell staddr +!
  swap move        \ n
  stbuf +! 
  1 stp +! ;

: st@ \ -- ad n
  stp @ cells staddr + @ 
  dup stbuf @ swap - ;

: st> \ -- ad n
  st@ over stbuf !
  cell negate staddr +!
  -1 stp +! ;

: sempty \ -- flag
  stp @ 0= ;

: ist@ \ i -- ad n     i=1,...
  dup stp @ = 
  if cells staddr + @ dup stbuf
  else cells staddr + dup @ dup rot cell+ 
  then @ swap - ;
  
: spickad \ k -- ad n
  stp @ swap - ist@ ;

: .st stp @ 1+ 1 ?do cr i ist@ type loop ;

: s [char] " parse >st ;

: sdup stp @ ist@ >st ;
: sdrop st> 2drop ;
: sover stp @ 1- ist@ >st ;
: snip st> sdrop >st ;
: sswap sover st> st> sdrop >st >st ;
: soover stp @ 2 - ist@ >st ;
: srot soover st> st> st> sdrop >st >st >st ;
: stuck sswap sover ;
: spick spickad >st ;

: s& \ s1 s2 -- s1&s2
  -1 stp +! 
  staddr @ @
  cell negate staddr +!
  staddr @ ! ;

: sduplen \ s -- s | -- n
  st@ nip ;

: sleft \ s -- s' | n --   the n leftmost chars
  st> drop swap >st ;

: sright \ s -- s' | n --  the n rightmost chars
  st> rot over swap - /string >st ;
  
: ssplit \ s -- s' s" | n --
  sdup dup sleft sswap
  sduplen swap - sright ;

: soverlen \ s1 s2 -- s1 s2 | -- n
  1 spickad nip ;

: firststrlett \ s1 s2 -- s1 s2 | j -- bj
  st@ drop 1- + c@ ;

: secondstrlett \ s1 s2 -- s1 s2 | i -- ai
  1 spickad drop 1- + c@ ;

: sincl \ s1 s2 -- s1 s3 s1 s4 / s2 | -- flag 
  soverlen                   \ m
  st@ 1 spickad search       \ m ad n f
  if nip sduplen swap -      \ m k-n
     ssplit                  \ m 
     ssplit true    
  else 2drop drop false 
  then ;

\ replace s2 with s1 wherever in s3
: sreplace \ s1 s2 s3 -- s4
  begin sincl
  while snip 3 spick sswap s& s&
  repeat snip snip ;

: scomp \ s1 s2 -- | -- n
  st> st> 2swap compare ;

: schr& \ s -- s' | ch --
  >r st> 2dup + r> swap c! 1+ >st ;

: sbl& bl schr& ;
: s,& [char] , schr& ;
: s.& [char] . schr& ;
: s;& [char] ; schr& ;
: s:& [char] : schr& ;
: s?& [char] ? schr& ;
: s!& [char] ! schr& ;
: s-& [char] - schr& ;

: slen= \ s1 s2 -- | -- flag
  st> nip st> nip = ;

: hamming \ s1 s2 -- s1 s2 | -- n
  0 1 spickad drop st@ 0
  do over i + c@ 
     over i + c@ = 0=
     if rot 1+ -rot then
  loop 2drop ;

: indfun \ s1 s2 -- s1 s2 | i j -- n
  1 spickad drop rot 1- + c@
  st@ drop rot 1- + c@ = 1+ ;

: levensh \ s1 s2 -- s1 s2 | i j -- n
  2dup min 0= if max exit then
  over 1- over recurse 1+ >r
  2dup 1- recurse 1+ r> min >r
  over 1- over 1- recurse -rot 
  indfun + r> min ;

: levenshtein \ s1 s2 -- s1 s2 | -- n
  soverlen sduplen levensh ;

: strail \ s -- s'
  st@ -trailing ;

: slower \ s -- s'
  st@ over + swap
  do i c@ [char] A [char] Z 1+ within
     if i c@ [char] ` or i c! then
  loop ;
  
: supper \ s -- s'
  st@ over + swap
  do i c@ [char] a [char] z 1+ within 
     if i c@ [char] _ and i c! then
  loop ;

\ Wagner-Fischer algorithm

: distad \ s1 s2 -- s1 s2 | i j -- addr
  soverlen 1+ * + cells pad + ;

: distinit \ s1 s2 -- s1 s2 
  soverlen 1+ 0 do i i 0 distad ! loop
  sduplen 1+ 0 do i 0 i distad ! loop ;

: firststrlett \ s1 s2 -- s1 s2 | j -- bj
  st@ drop 1- + c@ ;

: secondstrlett \ s1 s2 -- s1 s2 | i -- ai
  1 spickad drop 1- + c@ ;

: editdistance \ s1 s2 -- s1 s2 | -- n
  distinit sduplen 1+ 1
  do soverlen 1+ 1
     do i secondstrlett j firststrlett =
        if i 1- j 1- distad @ 
        else i 1- j distad @ 1+              \ a deletion
             i j 1- distad @ 1+              \ an insertion
             i 1- j 1- distad @ 1+           \ a substitution
             min min 
        then i j distad !
     loop 
  loop soverlen sduplen distad @ ;

