\ gforth-evaluator.fs
\ Single-file gforth port of the evaluator prototype.

decimal

-4095 constant ev-error#
-4094 constant ev-reported-error#
-1 constant ev-no-fileid
variable ev-current-diagnostic
variable ev-diagnostic-count
variable ev-current-program-token
variable ev-log-fileid

: ev-throw ( diag -- )
  ev-current-diagnostic !
  ev-error# throw ;

\ ----------------------------------------------------------------------
\ Basic storage helpers

: ev-xalloc ( u -- addr )
  allocate throw ;

: ev-xresize ( addr u -- addr' )
  resize throw ;

: ev-cells+ ( n addr -- addr' )
  swap cells + ;

: ev-max ( a b -- max )
  2dup < if nip else drop then ;

\ ----------------------------------------------------------------------
\ Persistent strings

: ev-slen@ ( s -- u )
  dup 0= if drop 0 exit then @ ;

: ev-s@ ( s -- c-addr u )
  dup 0= if drop 0 0 exit then
  dup @ swap cell+ swap ;

: ev-scopy ( c-addr u -- s )
  dup cell + ev-xalloc >r
  dup r@ !
  r@ cell+ swap move
  r> ;

: ev-sdup ( s -- s' )
  ev-s@ ev-scopy ;

: ev-sfrom-char ( c -- s )
  cell 1+ ev-xalloc { s }
  1 s !
  s cell+ c!
  s ;

: ev-sempty ( -- s )
  0 0 ev-scopy ;

: ev-sspace ( -- s )
  bl ev-sfrom-char ;

: ev-s. ( s -- )
  ev-s@ type ;

: ev-scat2 { s1 s2 -- s3 }
  s1 ev-s@ { a1 u1 }
  s2 ev-s@ { a2 u2 }
  u1 u2 + { u3 }
  u3 cell + ev-xalloc { s3 }
  u3 s3 !
  s3 cell+ { out }
  a1 out u1 move
  a2 out u1 + u2 move
  s3 ;

: ev-scat3 ( s1 s2 s3 -- s4 )
  ev-scat2 >r ev-scat2 r> drop ;

: ev-scat4 ( s1 s2 s3 s4 -- s5 )
  ev-scat2 >r ev-scat2 r> drop ev-scat2 ;

: ev-u>sptr ( u -- s )
  0 <# #s #> ev-scopy ;

: ev-s= ( s1 s2 -- flag )
  2dup = if 2drop true exit then
  over 0= over 0= and if 2drop true exit then
  over 0= over 0= or if 2drop false exit then
  >r ev-s@ r> ev-s@ compare 0= ;

: ev-char-space? { c -- flag }
  c bl = c 9 = or c 10 = or c 13 = or ;

: ev-upchar { c -- c' }
  c [char] a >= c [char] z <= and if
    c 32 -
  else
    c
  then ;

: ev-trim-range ( c-addr u -- c-addr' u' )
  begin
    dup 0>
  while
    over c@ ev-char-space? 0= if exit then
    1 /string
  repeat
  begin
    dup 0>
  while
    2dup + 1- c@ ev-char-space? 0= if exit then
    1-
  repeat ;

: ev-canon-word ( c-addr u -- s )
  ev-trim-range { addr u }
  cell u + ev-xalloc { s }
  u s !
  u 0 ?do
    addr i + c@ ev-upchar
    s cell+ i + c!
  loop
  s ;

: ev-canon-sptr ( s -- s' )
  ev-s@ ev-canon-word ;

\ ----------------------------------------------------------------------
\ Pointer vectors (single-cell items)

0 cells constant ev-v.count
1 cells constant ev-v.cap
2 cells constant ev-v.data
3 cells constant /ev-vec

: ev-vec-new ( cap -- vec )
  dup 1 < if drop 4 then
  { cap }
  /ev-vec ev-xalloc { vec }
  0 vec ev-v.count + !
  cap vec ev-v.cap + !
  cap cells ev-xalloc vec ev-v.data + !
  vec ;

: ev-vec-count@ ( vec -- n )
  ev-v.count + @ ;

: ev-vec-cap@ ( vec -- n )
  ev-v.cap + @ ;

: ev-vec-data@ ( vec -- addr )
  ev-v.data + @ ;

: ev-vec-grow { vec -- }
  vec ev-vec-cap@ 2* { newcap }
  vec ev-v.data + @ newcap cells ev-xresize { newdata }
  newdata vec ev-v.data + !
  newcap vec ev-v.cap + ! ;

: ev-vec-ensure ( needed vec -- )
  begin
    over over ev-vec-cap@ >
  while
    dup ev-vec-grow
  repeat
  2drop ;

: ev-vec-push ( x vec -- )
  >r
  r@ ev-vec-count@ 1+ r@ ev-vec-ensure
  r@ ev-vec-data@ r@ ev-vec-count@ cells + !
  1 r@ ev-v.count + +!
  rdrop ;

: ev-vec@ ( index vec -- x )
  ev-vec-data@ swap cells + @ ;

: ev-vec-last@ ( vec -- x )
  dup ev-vec-count@ 1- swap ev-vec@ ;

: ev-vec-set ( x index vec -- )
  ev-vec-data@ swap cells + ! ;

: ev-vec-pop ( vec -- x )
  dup ev-vec-count@ 1- dup >r
  over ev-v.count + !
  r> swap ev-vec@ ;

: ev-vec-remove-last ( vec -- )
  dup ev-vec-count@ 0> if -1 swap ev-v.count + +! else drop then ;

\ ----------------------------------------------------------------------
\ Spans, source words, diagnostics

0 cells constant ev-span.source
1 cells constant ev-span.sline
2 cells constant ev-span.scol
3 cells constant ev-span.eline
4 cells constant ev-span.ecol
5 cells constant /ev-span

: ev-span-new { source sline scol eline ecol -- span }
  /ev-span ev-xalloc { span }
  source span ev-span.source + !
  sline span ev-span.sline + !
  scol span ev-span.scol + !
  eline span ev-span.eline + !
  ecol span ev-span.ecol + !
  span ;

: ev-span-cover { span1 span2 -- span }
  span1 0= if span2 exit then
  span2 0= if span1 exit then
  span1 ev-span.source + @
  span1 ev-span.sline + @
  span1 ev-span.scol + @
  span2 ev-span.eline + @
  span2 ev-span.ecol + @
  ev-span-new ;

: ev-span-has-location? ( span -- flag )
  dup 0= if drop false exit then
  dup ev-span.sline + @ 0>
  swap ev-span.scol + @ 0> and ;

: ev-span-start. ( span -- )
  dup ev-span.source + @ ev-s.
  dup ev-span-has-location? if
    [char] : emit dup ev-span.sline + @ .
    [char] : emit ev-span.scol + @ .
  else
    drop
  then ;

0 cells constant ev-word.text
1 cells constant ev-word.span
2 cells constant ev-word.quoted
3 cells constant /ev-word

: ev-word-new { text span quoted -- word }
  /ev-word ev-xalloc { word }
  text word ev-word.text + !
  span word ev-word.span + !
  quoted word ev-word.quoted + !
  word ;

: ev-word-text@ ( word -- s )
  ev-word.text + @ ;

: ev-word-span@ ( word -- span )
  ev-word.span + @ ;

: ev-word-quoted? ( word -- flag )
  ev-word.quoted + @ 0<> ;

variable ev-current-source-lines

0 cells constant ev-diag.msg
1 cells constant ev-diag.reason
2 cells constant ev-diag.span
3 cells constant ev-diag.line
4 cells constant ev-diag.marker
5 cells constant /ev-diag

: ev-source-line@ { span -- s|0 }
  span 0= if 0 exit then
  span ev-span-has-location? 0= if 0 exit then
  ev-current-source-lines @ { lines }
  lines 0= if 0 exit then
  span ev-span.sline + @ dup 1 < if drop 0 exit then
  1- dup lines ev-vec-count@ >= if drop 0 exit then
  lines ev-vec@ ;

: ev-marker-line { span -- s }
  span ev-source-line@ { line$ }
  line$ 0= if ev-sempty exit then
  line$ ev-s@ { addr u }
  span ev-span.scol + @ 1- 0 max { indent }
  span ev-span.sline + @ span ev-span.eline + @ = if
    span ev-span.ecol + @ span ev-span.scol + @ - 1+ 1 max
  else
    1
  then { width }
  indent width + dup cell + ev-xalloc { marker }
  dup marker !
  marker cell+ { out }
  indent 0 ?do
    i u < if
      addr i + c@ dup 9 = if out i + c! else drop bl out i + c! then
    else
      bl out i + c!
    then
  loop
  width 0 ?do [char] ^ out indent + i + c! loop
  marker ;

: ev-diag-new { msg reason span -- diag }
  /ev-diag ev-xalloc { diag }
  msg diag ev-diag.msg + !
  reason diag ev-diag.reason + !
  span diag ev-diag.span + !
  span ev-source-line@ diag ev-diag.line + !
  span ev-marker-line diag ev-diag.marker + !
  diag ;

: ev-error-msg ( msg reason span -- )
  ev-diag-new ev-throw ;

: ev-diag. { diag -- }
  diag ev-diag.msg + @ ev-s.
  diag ev-diag.span + @ { span }
  span 0<> if
    span ev-span-has-location? if
      ."  at "
      span ev-span-start.
    then
  then
  diag ev-diag.reason + @ dup if
    ev-slen@ 0> if
      ." : " ev-s.
    else
      drop
    then
  else
    drop
  then
  ." ."
  diag ev-diag.line + @ dup if
    cr ."     --> "
    span ev-span-start.
    cr ."     " ev-s.
    cr ."     " diag ev-diag.marker + @ ev-s.
  else
    drop
  then ;

: ev-log-open? ( -- flag )
  ev-log-fileid @ ev-no-fileid <> ;

: ev-log-write-raw { c-addr u -- }
  ev-log-open? if
    c-addr u ev-log-fileid @ write-file throw
  else
    2drop
  then ;

: ev-log-write-s { s -- }
  s ev-s@ ev-log-write-raw ;

: ev-log-cr ( -- )
  13 pad c!
  10 pad 1+ c!
  pad 2 ev-log-write-raw ;

: ev-log-span-start { span -- }
  span ev-span.source + @ ev-log-write-s
  span ev-span-has-location? if
    s" :" ev-log-write-raw
    span ev-span.sline + @ ev-u>sptr ev-log-write-s
    s" :" ev-log-write-raw
    span ev-span.scol + @ ev-u>sptr ev-log-write-s
  then ;

: ev-log-diagnostic { diag -- }
  ev-log-open? 0= if drop exit then
  s" Error: " ev-log-write-raw
  diag ev-diag.msg + @ ev-log-write-s
  diag ev-diag.span + @ { span }
  span 0<> if
    span ev-span-has-location? if
      s"  at " ev-log-write-raw
      span ev-log-span-start
    then
  then
  diag ev-diag.reason + @ dup if
    ev-slen@ 0> if
      s" : " ev-log-write-raw
      ev-log-write-s
    else
      drop
    then
  else
    drop
  then
  s" ." ev-log-write-raw
  ev-log-cr ;

: ev-log-close ( -- )
  ev-log-open? if
    ev-log-fileid @ close-file drop
    ev-no-fileid ev-log-fileid !
  then ;

: ev-report-current-diagnostic ( -- )
  ev-current-diagnostic @ dup if
    dup ev-log-diagnostic
    ." Error: " ev-diag. cr
    1 ev-diagnostic-count +!
    0 ev-current-diagnostic !
  else
    drop
  then ;

: ev-literal-error { c-addr u span -- }
  c-addr u ev-scopy 0 span ev-error-msg ;

\ ----------------------------------------------------------------------
\ Scanner support

0 cells constant ev-sc.name
1 cells constant ev-sc.text
2 cells constant ev-sc.addr
3 cells constant ev-sc.len
4 cells constant ev-sc.lines
5 cells constant ev-sc.off
6 cells constant ev-sc.line
7 cells constant ev-sc.col
8 cells constant ev-sc.lastline
9 cells constant ev-sc.lastcol
10 cells constant /ev-sc

: ev-file>sptr { c-addr u -- s }
  c-addr u r/o open-file throw { fd }
  0 0 fd file-size throw d>s { len }
  cell len + ev-xalloc { s }
  len s !
  s cell+ len fd read-file throw drop
  fd close-file drop
  s ;

: ev-split-lines { text$ -- lines }
  16 ev-vec-new { lines }
  text$ ev-s@ { addr u }
  0 { start }
  0 { idx }
  begin
    idx u <
  while
    addr idx + c@ { ch }
    ch 13 = if
      idx 1+ to idx
    else
      ch 10 = if
        addr start + idx start - ev-scopy lines ev-vec-push
        idx 1+ to start
        idx 1+ to idx
      else
        idx 1+ to idx
      then
    then
  repeat
  addr start + u start - ev-scopy lines ev-vec-push
  lines ;

: ev-sc-new { name$ text$ -- sc }
  /ev-sc ev-xalloc { sc }
  name$ sc ev-sc.name + !
  text$ sc ev-sc.text + !
  text$ ev-s@ sc ev-sc.len + ! sc ev-sc.addr + !
  text$ ev-split-lines sc ev-sc.lines + !
  0 sc ev-sc.off + !
  1 sc ev-sc.line + !
  1 sc ev-sc.col + !
  1 sc ev-sc.lastline + !
  1 sc ev-sc.lastcol + !
  sc ;

: ev-sc-from-file ( s -- sc )
  dup ev-s@ ev-file>sptr ev-sc-new ;

: ev-sc-at-end? ( sc -- flag )
  dup ev-sc.off + @ swap ev-sc.len + @ >= ;

: ev-sc-char@ ( sc -- c )
  dup ev-sc.addr + @ swap ev-sc.off + @ + c@ ;

: ev-sc-advance ( sc -- )
  dup ev-sc-char@ { ch }
  dup ev-sc.line + @ over ev-sc.lastline + !
  dup ev-sc.col + @ over ev-sc.lastcol + !
  1 over ev-sc.off + +!
  ch 10 = if
    1 over ev-sc.line + +!
    1 swap ev-sc.col + !
  else
    ch 13 <> if 1 swap ev-sc.col + +! else drop then
  then ;

: ev-sc-position-span { sc -- span }
  sc ev-sc.name + @
  sc ev-sc.line + @
  sc ev-sc.col + @
  sc ev-sc.line + @
  sc ev-sc.col + @
  ev-span-new ;

: ev-sc-last-span { sc -- span }
  sc ev-sc.name + @
  sc ev-sc.lastline + @
  sc ev-sc.lastcol + @
  sc ev-sc.lastline + @
  sc ev-sc.lastcol + @
  ev-span-new ;

: ev-stop-char? { c stop-addr stop-u -- flag }
  false
  stop-u 0 ?do
    c stop-addr i + c@ = if drop true unloop exit then
  loop ;

: ev-sc-line-comment ( sc -- )
  begin
    dup ev-sc-at-end? 0=
  while
    dup ev-sc-char@ 10 = if exit then
    dup ev-sc-advance
  repeat
  drop ;

: ev-sc-skip-whitespace ( sc -- )
  begin
    dup ev-sc-at-end? 0=
  while
    dup ev-sc-char@ ev-char-space?
    0= if exit then
    dup ev-sc-advance
  repeat
  drop ;

: ev-sc-skip-ignorable ( sc -- )
  begin
    dup ev-sc-at-end? 0=
  while
    dup ev-sc-char@ { ch }
    ch ev-char-space? if
      dup ev-sc-advance
    else
      ch [char] \ = if
        dup ev-sc-line-comment
      else
        exit
      then
    then
  repeat
  drop ;

: ev-substr>sptr { base start len -- s }
  base start + len ev-scopy ;

: ev-sc-read-word { stop-addr stop-u sc -- word|0 }
  sc ev-sc-at-end? if 0 exit then
  sc ev-sc.off + @ { start-off }
  sc ev-sc.line + @ { sline }
  sc ev-sc.col + @ { scol }
  sline { eline }
  scol { ecol }
  0 { count }
  false { done }
  begin
    sc ev-sc-at-end? 0= done 0= and
  while
    sc ev-sc-char@ { ch }
    ch ev-char-space?
    ch [char] \ = or
    ch stop-addr stop-u ev-stop-char? or if
      true to done
    else
      sc ev-sc-advance
      sc ev-sc.lastline + @ to eline
      sc ev-sc.lastcol + @ to ecol
      count 1+ to count
    then
  repeat
  count 0= if 0 exit then
  sc ev-sc.addr + @ start-off count ev-substr>sptr
  sc ev-sc.name + @ sline scol eline ecol ev-span-new
  false ev-word-new ;

: ev-sc-read-program-word { stop-addr stop-u sc -- word|0 }
  sc ev-sc-at-end? if 0 exit then
  sc ev-sc.off + @ { start-off }
  sc ev-sc.line + @ { sline }
  sc ev-sc.col + @ { scol }
  sline { eline }
  scol { ecol }
  0 { count }
  false { done }
  begin
    sc ev-sc-at-end? 0= done 0= and
  while
    sc ev-sc-char@ { ch }
    ch ev-char-space?
    ch stop-addr stop-u ev-stop-char? or if
      true to done
    else
      sc ev-sc-advance
      sc ev-sc.lastline + @ to eline
      sc ev-sc.lastcol + @ to ecol
      count 1+ to count
    then
  repeat
  count 0= if 0 exit then
  sc ev-sc.addr + @ start-off count ev-substr>sptr
  sc ev-sc.name + @ sline scol eline ecol ev-span-new
  false ev-word-new ;

: ev-sc-read-quoted { sc -- word|0 }
  sc ev-sc-at-end? if 0 exit then
  sc ev-sc.line + @ { sline }
  sc ev-sc.col + @ { scol }
  sc ev-sc-advance
  sc ev-sc.len + @ sc ev-sc.off + @ - cell + ev-xalloc { buf }
  0 { outlen }
  begin
    sc ev-sc-at-end? 0=
  while
    sc ev-sc-char@ { ch }
    ch [char] " = if
      sc ev-sc-advance
      outlen buf !
      buf
      sc ev-sc.name + @ sline scol sc ev-sc.lastline + @ sc ev-sc.lastcol + @ ev-span-new
      true ev-word-new
      exit
    then
    ch [char] \ = if
      sc ev-sc-advance
      sc ev-sc-at-end? if 0 exit then
      sc ev-sc-char@ { esc }
      esc case
        [char] n of 10 endof
        [char] r of 13 endof
        [char] t of 9 endof
        [char] " of [char] " endof
        [char] \ of [char] \ endof
      endcase
      buf cell+ outlen + c!
      outlen 1+ to outlen
      sc ev-sc-advance
    else
      buf cell+ outlen + ch swap c!
      outlen 1+ to outlen
      sc ev-sc-advance
    then
  repeat
  0 ;

: ev-sc-read-atom { stop-addr stop-u sc -- word|0 }
  sc ev-sc-at-end? if 0 exit then
  sc ev-sc-char@ [char] " = if
    sc ev-sc-read-quoted
  else
    stop-addr stop-u sc ev-sc-read-word
  then ;

: ev-sc-next-word { stop-addr stop-u sc -- word|0 }
  sc ev-sc-skip-ignorable
  stop-addr stop-u sc ev-sc-read-word ;

: ev-sc-next-program-word { stop-addr stop-u sc -- word|0 }
  sc ev-sc-skip-whitespace
  stop-addr stop-u sc ev-sc-read-program-word ;

: ev-sc-next-atom { stop-addr stop-u sc -- word|0 }
  sc ev-sc-skip-ignorable
  stop-addr stop-u sc ev-sc-read-atom ;

: ev-sc-next-line-atoms ( sc -- vec|0 )
  dup ev-sc-at-end? if drop 0 exit then
  8 ev-vec-new { line }
  begin
    dup ev-sc-at-end? 0=
  while
    dup ev-sc-char@ { ch }
    ch [char] \ = if
      dup ev-sc-line-comment
    else
      ch 10 = if
        dup ev-sc-advance
        drop line exit
      else
        ch bl = ch 9 = or ch 13 = or if
          dup ev-sc-advance
        else
          dup 0 0 rot ev-sc-read-atom dup if
            line ev-vec-push
          else
            2drop
          then
        then
      then
    then
  repeat
  drop line ;

: ev-sc-starts-with { c-addr u sc -- flag }
  sc ev-sc.off + @ { off }
  off u + sc ev-sc.len + @ > if false exit then
  sc ev-sc.addr + @ off + u c-addr u compare 0= ;

: ev-sc-parse-until { delim$ sc -- word|0 }
  delim$ ev-s@ { d-addr d-u }
  d-u 0= if
    ev-sempty sc ev-sc-position-span false ev-word-new
    exit
  then
  sc ev-sc.line + @ { sline }
  sc ev-sc.col + @ { scol }
  sc ev-sc.len + @ sc ev-sc.off + @ - cell + ev-xalloc { buf }
  0 { outlen }
  sline { eline }
  scol { ecol }
  false { has-text }
  begin
    sc ev-sc-at-end? 0=
  while
    d-addr d-u sc ev-sc-starts-with if
      d-u 0 ?do sc ev-sc-advance loop
      outlen buf !
      buf
      sc ev-sc.name + @ sline scol ( start )
      has-text if eline else sline then
      has-text if ecol else scol then
      ev-span-new
      false ev-word-new
      exit
    then
    sc ev-sc-char@ { ch }
    buf cell+ outlen + ch swap c!
    outlen 1+ to outlen
    true to has-text
    sc ev-sc-advance
    sc ev-sc.lastline + @ to eline
    sc ev-sc.lastcol + @ to ecol
  repeat
  0 ;

\ ----------------------------------------------------------------------
\ Type system

0 cells constant ev-alias.name
1 cells constant ev-alias.index
2 cells constant /ev-alias

: ev-alias-new { name index -- alias }
  /ev-alias ev-xalloc { alias }
  name alias ev-alias.name + !
  index alias ev-alias.index + !
  alias ;

0 cells constant ev-rel.sub
1 cells constant ev-rel.super
2 cells constant ev-rel.span
3 cells constant /ev-rel

: ev-rel-new { sub super span -- rel }
  /ev-rel ev-xalloc { rel }
  sub rel ev-rel.sub + !
  super rel ev-rel.super + !
  span rel ev-rel.span + !
  rel ;

0 cells constant ev-scanner.key
1 cells constant ev-scanner.delim
2 cells constant /ev-scanner

: ev-scanner-new { key delim -- entry }
  /ev-scanner ev-xalloc { entry }
  key entry ev-scanner.key + !
  delim entry ev-scanner.delim + !
  entry ;

0 cells constant ev-ts.source
1 cells constant ev-ts.lines
2 cells constant ev-ts.types
3 cells constant ev-ts.aliases
4 cells constant ev-ts.rel-size
5 cells constant ev-ts.rel-matrix
6 cells constant ev-ts.scanners
7 cells constant /ev-ts

: ev-ts-new { source lines types aliases rel-size rel-matrix scanners -- ts }
  /ev-ts ev-xalloc { ts }
  source ts ev-ts.source + !
  lines ts ev-ts.lines + !
  types ts ev-ts.types + !
  aliases ts ev-ts.aliases + !
  rel-size ts ev-ts.rel-size + !
  rel-matrix ts ev-ts.rel-matrix + !
  scanners ts ev-ts.scanners + !
  ts ;

: ev-ts-type-count ( ts -- n )
  ev-ts.types + @ ev-vec-count@ ;

: ev-ts-rel-addr { i j ts -- addr }
  ts ev-ts.rel-matrix + @
  i ts ev-ts.rel-size + @ * j + cells + ;

: ev-ts-rel@ { i j ts -- rel }
  i j ts ev-ts-rel-addr @ ;

: ev-ts-rel! { rel i j ts -- }
  rel i j ts ev-ts-rel-addr ! ;

: ev-ts-alias-index { name ts -- n|-1 }
  ts ev-ts.aliases + @ { aliases }
  aliases ev-vec-count@ 0 ?do
    i aliases ev-vec@ { alias }
    name alias ev-alias.name + @ ev-s= if
      alias ev-alias.index + @ unloop exit
    then
  loop
  -1 ;

: ev-ts-contains? ( name ts -- flag )
  ev-ts-alias-index -1 <> ;

: ev-ts-add-alias { name index aliases span -- }
  aliases ev-vec-count@ 0 ?do
    i aliases ev-vec@ { alias }
    name alias ev-alias.name + @ ev-s= if
      s" Duplicate type name " ev-scopy
      name
      ev-scat2 0 span ev-error-msg
    then
  loop
  name index ev-alias-new aliases ev-vec-push ;

: ev-token-unquoted= { token c-addr u -- flag }
  token ev-word-quoted? if false exit then
  token ev-word-text@ ev-s@ c-addr u compare 0= ;

: ev-line-first ( line -- token )
  0 swap ev-vec@ ;

: ev-line-last ( line -- token )
  dup ev-vec-count@ 1- swap ev-vec@ ;

: ev-ts-add-relation { sub super span ts -- }
  sub ts ev-ts-alias-index { i1 }
  super ts ev-ts-alias-index { i2 }
  i1 -1 = if
    s" Unknown type " ev-scopy sub ev-scat2 0 span ev-error-msg
  then
  i2 -1 = if
    s" Unknown type " ev-scopy super ev-scat2 0 span ev-error-msg
  then
  i1 i2 <> if 1 i1 i2 ts ev-ts-rel! then ;

: ev-ts-add-scanner { name delim span scanners -- }
  name ev-canon-sptr { key }
  key ev-slen@ 0= if
    s" Empty scanner name" ev-scopy 0 span ev-error-msg
  then
  delim ev-slen@ 0= if
    s" Empty scanner delimiter" ev-scopy 0 span ev-error-msg
  then
  scanners ev-vec-count@ 0 ?do
    i scanners ev-vec@ { entry }
    key entry ev-scanner.key + @ ev-s= if
      s" Duplicate scanner name " ev-scopy
      name ev-scat2 0 span ev-error-msg
    then
  loop
  key delim ev-scanner-new scanners ev-vec-push ;

: ev-ts-scanner-delim { name ts -- s|0 }
  name ev-canon-sptr { key }
  ts ev-ts.scanners + @ { scanners }
  scanners ev-vec-count@ 0 ?do
    i scanners ev-vec@ { entry }
    key entry ev-scanner.key + @ ev-s= if
      entry ev-scanner.delim + @ unloop exit
    then
  loop
  0 ;

: ev-ts-normalize { ts -- }
  ts ev-ts-type-count { n }
  n 0 ?do
    n 0 ?do
      i j ts ev-ts-rel@ 0= if
        i j = if 3 i j ts ev-ts-rel! then
        j i ts ev-ts-rel@ 1 = if 2 i j ts ev-ts-rel! then
        j i ts ev-ts-rel@ 2 = if 1 i j ts ev-ts-rel! then
        j i ts ev-ts-rel@ 3 = if 3 i j ts ev-ts-rel! then
      else
        i j ts ev-ts-rel@ 1 = if
          j i ts ev-ts-rel@ 0= if 2 j i ts ev-ts-rel! then
          j i ts ev-ts-rel@ 1 = if 3 i j ts ev-ts-rel! 3 j i ts ev-ts-rel! then
          j i ts ev-ts-rel@ 3 = if 3 i j ts ev-ts-rel! then
        else
          i j ts ev-ts-rel@ 2 = if
            j i ts ev-ts-rel@ 0= if 1 j i ts ev-ts-rel! then
            j i ts ev-ts-rel@ 2 = if 3 i j ts ev-ts-rel! 3 j i ts ev-ts-rel! then
            j i ts ev-ts-rel@ 3 = if 3 i j ts ev-ts-rel! then
          else
            i j ts ev-ts-rel@ 3 = if 3 j i ts ev-ts-rel! then
          then
        then
      then
    loop
  loop
  n 0 ?do
    n 0 ?do
      n 0 ?do
        i k ts ev-ts-rel@ dup 0> swap 4 < and if
          i k ts ev-ts-rel@ k j ts ev-ts-rel@ = if
            i k ts ev-ts-rel@ i j ts ev-ts-rel!
          then
        then
      loop
    loop
  loop ;

: ev-ts-relation { name1 name2 ts -- rel }
  name1 0= name2 0= or if 0 exit then
  name1 ts ev-ts-alias-index { i1 }
  name2 ts ev-ts-alias-index { i2 }
  i1 -1 = i2 -1 = or if 0 exit then
  i1 i2 ts ev-ts-rel@ ;

: ev-ts-parse-line { line types aliases rels scanners -- }
  line ev-line-first { head }
  head ev-word-text@ ev-canon-sptr { directive }
  directive ev-s@ s" TYPE" compare 0= if
    line ev-vec-count@ 2 < if
      s" Type definition is too short" ev-scopy 0 head ev-word-span@ ev-error-msg
    then
    types ev-vec-count@ { index }
    1 line ev-vec@ ev-word-text@ types ev-vec-push
    line ev-vec-count@ 1 ?do
      i line ev-vec@ { tok }
      tok ev-word-text@ index aliases tok ev-word-span@ ev-ts-add-alias
    loop
    exit
  then
  directive ev-s@ s" REL" compare 0= if
    line ev-vec-count@ 4 <> if
      s" Malformed relation" ev-scopy 0 head ev-word-span@ ev-error-msg
    then
    2 line ev-vec@ s" <" ev-token-unquoted= 0= if
      s" Malformed relation" ev-scopy 0 head ev-word-span@ ev-error-msg
    then
    1 line ev-vec@ ev-word-text@
    3 line ev-vec@ ev-word-text@
    head ev-word-span@ 3 line ev-vec@ ev-word-span@ ev-span-cover
    ev-rel-new rels ev-vec-push
    exit
  then
  directive ev-s@ s" SCANNER" compare 0= if
    line ev-vec-count@ 3 <> if
      s" Malformed scanner definition" ev-scopy 0 head ev-word-span@ ev-error-msg
    then
    1 line ev-vec@ ev-word-text@
    2 line ev-vec@ ev-word-text@
    head ev-word-span@ 2 line ev-vec@ ev-word-span@ ev-span-cover
    scanners ev-ts-add-scanner
    exit
  then
  s" Unknown directive " ev-scopy head ev-word-text@ ev-scat2
  0 head ev-word-span@ ev-error-msg ;

: ev-ts-load { file$ -- ts }
  file$ ev-sc-from-file { sc }
  sc ev-sc.lines + @ ev-current-source-lines !
  16 ev-vec-new { types }
  32 ev-vec-new { aliases }
  32 ev-vec-new { rels }
  8 ev-vec-new { scanners }
  begin
    sc ev-sc-next-line-atoms dup
  while
    { line }
    line ev-vec-count@ 0> if
      line types aliases rels scanners ev-ts-parse-line
    then
  repeat
  drop
  types ev-vec-count@ { n }
  n n * cells ev-xalloc { matrix }
  n n * 0 ?do 0 matrix i cells + ! loop
  file$ sc ev-sc.lines + @ types aliases n matrix scanners ev-ts-new { ts }
  rels ev-vec-count@ 0 ?do
    i rels ev-vec@ { rel }
    rel ev-rel.sub + @ rel ev-rel.super + @ rel ev-rel.span + @ ts ev-ts-add-relation
  loop
  ts ev-ts-normalize
  ts ;

\ ----------------------------------------------------------------------
\ Type symbols and stack effects

0 constant ev-parse.none
1 constant ev-parse.until
2 constant ev-parse.word
3 constant ev-parse.definition

0 constant ev-define.none
1 constant ev-define.colon
2 constant ev-define.constant
3 constant ev-define.variable

0 constant ev-state.any
1 constant ev-state.interpret
2 constant ev-state.compile

0 cells constant ev-sym.type
1 cells constant ev-sym.pos
2 cells constant ev-sym.explicit
3 cells constant /ev-sym

: ev-sym-new { type pos explicit -- sym }
  /ev-sym ev-xalloc { sym }
  type sym ev-sym.type + !
  pos sym ev-sym.pos + !
  explicit sym ev-sym.explicit + !
  sym ;

: ev-sym-clone ( sym -- sym' )
  dup ev-sym.type + @
  over ev-sym.pos + @
  rot ev-sym.explicit + @
  ev-sym-new ;

: ev-sym= { s1 s2 -- flag }
  s1 ev-sym.type + @ s2 ev-sym.type + @ ev-s=
  s1 ev-sym.pos + @ s2 ev-sym.pos + @ = and ;

0 cells constant ev-spec.left
1 cells constant ev-spec.right
2 cells constant ev-spec.parse-string
3 cells constant ev-spec.parse-mode
4 cells constant ev-spec.define-mode
5 cells constant ev-spec.control-mode
6 cells constant ev-spec.immediate
7 cells constant ev-spec.state-mode
8 cells constant ev-spec.source
9 cells constant ev-spec.origin
10 cells constant ev-spec.max-pos
11 cells constant /ev-spec

: ev-spec-new { left right -- spec }
  /ev-spec ev-xalloc { spec }
  left spec ev-spec.left + !
  right spec ev-spec.right + !
  0 spec ev-spec.parse-string + !
  ev-parse.none spec ev-spec.parse-mode + !
  ev-define.none spec ev-spec.define-mode + !
  0 spec ev-spec.control-mode + !
  0 spec ev-spec.immediate + !
  ev-state.any spec ev-spec.state-mode + !
  0 spec ev-spec.source + !
  0 spec ev-spec.origin + !
  0 spec ev-spec.max-pos + !
  spec ;

: ev-sym-vec-clone { vec -- copy }
  vec ev-vec-count@ 4 ev-max ev-vec-new { copy }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ ev-sym-clone copy ev-vec-push
  loop
  copy ;

: ev-spec-clone { spec -- copy }
  spec ev-spec.left + @ ev-sym-vec-clone
  spec ev-spec.right + @ ev-sym-vec-clone
  ev-spec-new { copy }
  spec ev-spec.parse-string + @ copy ev-spec.parse-string + !
  spec ev-spec.parse-mode + @ copy ev-spec.parse-mode + !
  spec ev-spec.define-mode + @ copy ev-spec.define-mode + !
  spec ev-spec.control-mode + @ copy ev-spec.control-mode + !
  spec ev-spec.immediate + @ copy ev-spec.immediate + !
  spec ev-spec.state-mode + @ copy ev-spec.state-mode + !
  spec ev-spec.source + @ copy ev-spec.source + !
  spec ev-spec.origin + @ copy ev-spec.origin + !
  spec ev-spec.max-pos + @ copy ev-spec.max-pos + !
  copy ;

: ev-spec-with-origin { spec span label -- spec }
  span spec ev-spec.source + !
  label spec ev-spec.origin + !
  spec ;

: ev-spec-with-parse { spec mode delim -- spec }
  delim spec ev-spec.parse-string + !
  mode spec ev-spec.parse-mode + !
  spec ;

: ev-spec-with-define { spec mode -- spec }
  mode spec ev-spec.define-mode + !
  spec ;

: ev-spec-with-control { spec role -- spec }
  role spec ev-spec.control-mode + !
  spec ;

: ev-spec-with-immediate { spec flag -- spec }
  flag spec ev-spec.immediate + !
  spec ;

: ev-spec-with-state { spec mode -- spec }
  mode spec ev-spec.state-mode + !
  spec ;

: ev-spec-left-count ( spec -- n )
  ev-spec.left + @ ev-vec-count@ ;

: ev-spec-right-count ( spec -- n )
  ev-spec.right + @ ev-vec-count@ ;

: ev-parse-uint { c-addr u -- n ok }
  0 { n }
  u 0= if 0 false exit then
  u 0 ?do
    c-addr i + c@ dup [char] 0 >= over [char] 9 <= and 0= if
      drop 0 false unloop exit
    then
    [char] 0 - n 10 * + to n
  loop
  n true ;

: ev-ts-check-type { type span ts -- }
  type ts ev-ts-contains? 0= if
    s" Unknown type " ev-scopy type ev-scat2 0 span ev-error-msg
  then ;

: ev-spec-max-pos { spec -- n }
  0 { m }
  spec ev-spec.left + @ { left }
  spec ev-spec.right + @ { right }
  left ev-vec-count@ 0 ?do
    i left ev-vec@ ev-sym.pos + @ m ev-max to m
  loop
  right ev-vec-count@ 0 ?do
    i right ev-vec@ ev-sym.pos + @ m ev-max to m
  loop
  m spec ev-spec.max-pos + !
  m ;

: ev-parse-type-symbol { text span ts -- sym }
  text ev-s@ { addr u }
  addr { type-addr }
  u { type-u }
  0 { pos }
  false { explicit }
  -1 { bracket }
  -1 { close }
  u 0 ?do
    addr i + c@ [char] [ = if
      i to bracket
      i to type-u
      u i 1+ ?do
        addr i + c@ [char] ] = if
          i to close
          leave
        then
      loop
      close -1 = if
        s" Malformed type symbol " ev-scopy text ev-scat2 0 span ev-error-msg
      then
      addr bracket 1+ + close bracket 1+ - ev-parse-uint { num ok }
      ok 0= if
        s" Malformed wildcard index in " ev-scopy text ev-scat2 0 span ev-error-msg
      then
      num to pos
      true to explicit
      leave
    then
  loop
  type-addr type-u ev-scopy dup span ts ev-ts-check-type
  pos explicit ev-sym-new ;

: ev-tokenize-type-side { text -- vec }
  8 ev-vec-new { result }
  s" <type-side>" ev-scopy text ev-sc-new { sc }
  begin
    0 0 sc ev-sc-next-word dup
  while
    ev-word-text@ result ev-vec-push
  repeat
  drop
  result ;

: ev-parse-type-list { text ts span -- vec }
  text ev-slen@ 0= if 4 ev-vec-new exit then
  text ev-tokenize-type-side { toks }
  toks ev-vec-count@ 4 ev-max ev-vec-new { vec }
  toks ev-vec-count@ 0 ?do
    i toks ev-vec@ span ts ev-parse-type-symbol vec ev-vec-push
  loop
  vec ;

: ev-find-arrow { text -- n|-1 }
  text ev-s@ { addr u }
  u 1 < if -1 exit then
  u 1- 0 ?do
    addr i + c@ [char] - = addr i 1+ + c@ [char] - = and if
      i unloop exit
    then
  loop
  -1 ;

: ev-parse-spec-body { body ts span -- spec }
  body ev-find-arrow { arrow }
  arrow 0< if
    s" Missing -- in stack effect" ev-scopy 0 span ev-error-msg
  then
  body ev-s@ { addr u }
  addr arrow ev-scopy ts span ev-parse-type-list { left }
  addr arrow 2 + + u arrow 2 + - ev-scopy ts span ev-parse-type-list { right }
  left right ev-spec-new { spec }
  spec ev-spec-max-pos drop
  spec ;

: ev-spec-substitute-vec { old new vec -- count }
  0 { count }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ { sym }
    sym old ev-sym= if
      new ev-sym-clone i vec ev-vec-set
      count 1+ to count
    then
  loop
  count ;

: ev-spec-substitute { old new spec -- count }
  old new spec ev-spec.left + @ ev-spec-substitute-vec
  old new spec ev-spec.right + @ ev-spec-substitute-vec
  + ;

: ev-spec-list-substitute { old new list -- }
  list ev-vec-count@ 0 ?do
    old new i list ev-vec@ ev-spec-substitute drop
  loop ;

: ev-spec-increment-wild-vec { amount vec -- }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ { sym }
    sym ev-sym.pos + @ dup 0> if amount + sym ev-sym.pos + ! else drop then
  loop ;

: ev-spec-increment-wild { amount spec -- }
  amount spec ev-spec.left + @ ev-spec-increment-wild-vec
  amount spec ev-spec.right + @ ev-spec-increment-wild-vec
  spec ev-spec-max-pos { max }
  max spec ev-spec.max-pos + !
  spec ev-spec.left + @ { left }
  spec ev-spec.right + @ { right }
  left ev-vec-count@ 0 ?do
    i left ev-vec@ { sym }
    sym ev-sym.pos + @ 0= if
      max 1+ to max
      max sym ev-sym.pos + !
    then
  loop
  right ev-vec-count@ 0 ?do
    i right ev-vec@ { sym }
    sym ev-sym.pos + @ 0= if
      max 1+ to max
      max sym ev-sym.pos + !
    then
  loop
  max spec ev-spec.max-pos + ! ;

: ev-new-sym-like { type pos explicit -- sym }
  type pos explicit ev-sym-new ;

: ev-spec-copy-left ( spec -- vec )
  ev-spec.left + @ ev-sym-vec-clone ;

: ev-spec-copy-right ( spec -- vec )
  ev-spec.right + @ ev-sym-vec-clone ;

: ev-vec-prepend-clones { prefix suffix -- vec }
  prefix ev-vec-count@ suffix ev-vec-count@ + 4 ev-max ev-vec-new { out }
  prefix ev-vec-count@ 0 ?do
    i prefix ev-vec@ ev-sym-clone out ev-vec-push
  loop
  suffix ev-vec-count@ 0 ?do
    i suffix ev-vec@ ev-sym-clone out ev-vec-push
  loop
  out ;

: ev-spec-from-sides { left right template -- spec }
  left right ev-spec-new { spec }
  template ev-spec.parse-string + @ spec ev-spec.parse-string + !
  template ev-spec.parse-mode + @ spec ev-spec.parse-mode + !
  template ev-spec.define-mode + @ spec ev-spec.define-mode + !
  template ev-spec.control-mode + @ spec ev-spec.control-mode + !
  template ev-spec.immediate + @ spec ev-spec.immediate + !
  template ev-spec.state-mode + @ spec ev-spec.state-mode + !
  template ev-spec.source + @ spec ev-spec.source + !
  template ev-spec.origin + @ spec ev-spec.origin + !
  spec ev-spec-max-pos drop
  spec ;

variable ev-sl-cmax
variable ev-sl-conf-prefix
variable ev-sl-conf-incoming
variable ev-sl-conf-actual
variable ev-sl-conf-expected
variable ev-eval-result

: ev-sl-clear-conflict ( -- )
  0 ev-sl-conf-prefix !
  0 ev-sl-conf-incoming !
  0 ev-sl-conf-actual !
  0 ev-sl-conf-expected ! ;

: ev-sl-record-conflict { prefix incoming actual expected -- }
  prefix ev-spec-clone ev-sl-conf-prefix !
  incoming ev-spec-clone ev-sl-conf-incoming !
  actual ev-sym-clone ev-sl-conf-actual !
  expected ev-sym-clone ev-sl-conf-expected ! ;

0 cells constant ev-norm.key
1 cells constant ev-norm.count
2 cells constant ev-norm.assigned
3 cells constant ev-norm.explicit
4 cells constant /ev-norm

: ev-norm-new { key -- entry }
  /ev-norm ev-xalloc { entry }
  key entry ev-norm.key + !
  0 entry ev-norm.count + !
  0 entry ev-norm.assigned + !
  0 entry ev-norm.explicit + !
  entry ;

: ev-find-norm { sym table -- entry|0 }
  table ev-vec-count@ 0 ?do
    i table ev-vec@ { entry }
    sym entry ev-norm.key + @ ev-sym= if
      entry unloop exit
    then
  loop
  0 ;

: ev-norm-touch { sym table -- entry }
  sym table ev-find-norm dup if exit then drop
  sym ev-norm-new dup table ev-vec-push ;

: ev-needs-index? ( entry -- flag )
  dup ev-norm.explicit + @ 0<>
  swap ev-norm.count + @ 2 > or ;

: ev-add-norm-pass1 { sym table -- }
  sym table ev-norm-touch { entry }
  1 entry ev-norm.count + +!
  sym ev-sym.explicit + @ if 1 entry ev-norm.explicit + ! then ;

: ev-add-norm-pass2 { sym table next -- next' }
  sym table ev-find-norm { entry }
  entry ev-needs-index? entry ev-norm.assigned + @ 0= and if
    next 1+ dup entry ev-norm.assigned + !
  else
    next
  then ;

: ev-scan-norm-pass1-vec { vec table -- }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ table ev-add-norm-pass1
  loop ;

: ev-scan-norm-pass2-left { vec table next -- next' }
  vec ev-vec-count@ 1- { idx }
  begin
    idx 0>=
  while
    idx vec ev-vec@ table next ev-add-norm-pass2 to next
    idx 1- to idx
  repeat
  next ;

: ev-scan-norm-pass2-right { vec table next -- next' }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ table next ev-add-norm-pass2 to next
  loop
  next ;

: ev-sym>sptr { sym -- s }
  sym ev-sym.type + @ ev-sdup { base }
  sym ev-sym.pos + @ { pos }
  pos 0> if
    base s" [" ev-scopy ev-scat2
    pos ev-u>sptr ev-scat2
    s" ] " ev-scopy ev-scat2
  else
    base ev-sspace ev-scat2
  then ;

: ev-sym-vec>sptr { vec -- s }
  ev-sempty { out }
  vec ev-vec-count@ 0 ?do
    out i vec ev-vec@ ev-sym>sptr ev-scat2 to out
  loop
  out ;

: ev-spec>sptr { spec -- s }
  s" ( " ev-scopy
  spec ev-spec.left + @ ev-sym-vec>sptr ev-scat2
  s" --  " ev-scopy ev-scat2
  spec ev-spec.right + @ ev-sym-vec>sptr ev-scat2
  s" ) " ev-scopy ev-scat2 ;

: ev-log-definition { name spec -- }
  ev-log-open? 0= if drop drop exit then
  name ev-sspace ev-scat2
  spec ev-spec>sptr ev-scat2
  ev-log-write-s
  ev-log-cr ;

\ Renumbers wildcard indices into a compact, readable form after evaluation.
: ev-spec-list-normalize { list result -- norm }
  result ev-spec-max-pos { max }
  list ev-vec-count@ 0 ?do
    i list ev-vec@ ev-spec-max-pos max ev-max to max
  loop
  max 1+ to max
  list ev-vec-count@ 0 ?do
    max i list ev-vec@ ev-spec-increment-wild
  loop
  max result ev-spec-increment-wild
  16 ev-vec-new { table }
  result ev-spec.left + @ table ev-scan-norm-pass1-vec
  result ev-spec.right + @ table ev-scan-norm-pass1-vec
  list ev-vec-count@ 0 ?do
    i list ev-vec@ { sp }
    sp ev-spec.left + @ table ev-scan-norm-pass1-vec
    sp ev-spec.right + @ table ev-scan-norm-pass1-vec
  loop
  0 { next }
  result ev-spec.left + @ table next ev-scan-norm-pass2-left to next
  result ev-spec.right + @ table next ev-scan-norm-pass2-right to next
  list ev-vec-count@ 0 ?do
    i list ev-vec@ { sp }
    sp ev-spec.left + @ table next ev-scan-norm-pass2-left to next
    sp ev-spec.right + @ table next ev-scan-norm-pass2-right to next
  loop
  table ev-vec-count@ 0 ?do
    i table ev-vec@ { entry }
    entry ev-norm.assigned + @ { assigned }
    entry ev-needs-index? 0= if 0 to assigned then
    entry ev-norm.key + @ ev-sym.type + @
    assigned
    entry ev-norm.explicit + @ 0<>
    ev-sym-new { fresh }
    entry ev-norm.key + @ fresh result ev-spec-substitute drop
    entry ev-norm.key + @ fresh list ev-spec-list-substitute
  loop
  result ;

: ev-spec-join-left { s1 s2 -- vec }
  s1 ev-spec-copy-left { left1 }
  s2 ev-spec.left + @ left1 ev-vec-prepend-clones ;

: ev-spec-join-right { s1 s2 -- vec }
  s2 ev-spec-copy-right { right2 }
  s1 ev-spec.right + @ right2 ev-vec-prepend-clones ;

: ev-winner-sym { m1 m2 rel -- sym }
  rel case
    1 of m1 ev-sym.type + @ endof
    2 of m2 ev-sym.type + @ endof
    3 of m1 ev-sym.type + @ endof
  endcase
  ev-sl-cmax @ 1+ dup ev-sl-cmax !
  m1 ev-sym.explicit + @ m2 ev-sym.explicit + @ or
  ev-sym-new ;

\ Composes two stack effects, unifying the touching boundary one symbol at a time.
: ev-spec-multiply { list s1 s2 ts -- spec|0 }
  s1 0= s2 0= or if 0 exit then
  s1 ev-spec-copy-left { rleft }
  s2 ev-spec-copy-right { rright }
  s1 ev-spec-right-count 0= if
    s2 ev-spec.left + @ rleft ev-vec-prepend-clones
    rright s2 ev-spec-from-sides exit
  then
  s2 ev-spec-left-count 0= if
    s1 ev-spec.right + @ rright ev-vec-prepend-clones
    s1 ev-spec-copy-left swap s2 ev-spec-from-sides exit
  then
  s1 ev-spec.right + @ ev-vec-last@ { m1 }
  s2 ev-spec.left + @ ev-vec-last@ { m2 }
  m1 ev-sym.type + @ m2 ev-sym.type + @ ts ev-ts-relation { rel }
  rel 0= if
    s1 s2 m1 m2 ev-sl-record-conflict
    0 exit
  then
  m1 m2 rel ev-winner-sym { fresh }
  s1 ev-spec.right + @ ev-sym-vec-clone { r1rs }
  s2 ev-spec.left + @ ev-sym-vec-clone { r2ls }
  m1 fresh r1rs ev-spec-substitute-vec drop
  m2 fresh r1rs ev-spec-substitute-vec drop
  m1 fresh r2ls ev-spec-substitute-vec drop
  m2 fresh r2ls ev-spec-substitute-vec drop
  m1 fresh rleft ev-spec-substitute-vec drop
  m2 fresh rleft ev-spec-substitute-vec drop
  m1 fresh rright ev-spec-substitute-vec drop
  m2 fresh rright ev-spec-substitute-vec drop
  m1 fresh list ev-spec-list-substitute
  m2 fresh list ev-spec-list-substitute
  r1rs ev-vec-remove-last
  r2ls ev-vec-remove-last
  rleft r1rs s1 ev-spec-from-sides { r1 }
  r2ls rright s2 ev-spec-from-sides { r2 }
  list r1 r2 ts recurse ;

: ev-spec-list-evaluate { list ts -- spec|0 }
  0 ev-sl-cmax !
  ev-sl-clear-conflict
  list ev-vec-count@ 0 ?do
    ev-sl-cmax @ i list ev-vec@ ev-spec-increment-wild
    i list ev-vec@ ev-spec-max-pos ev-sl-cmax !
  loop
  4 ev-vec-new 4 ev-vec-new ev-spec-new ev-eval-result !
  list ev-vec-count@ 0 ?do
    list ev-eval-result @ i list ev-vec@ ts ev-spec-multiply dup 0= if
      drop 0 unloop exit
    then
    ev-eval-result !
  loop
  list ev-eval-result @ ev-spec-list-normalize ;

: ev-new-merged-sym { m1 m2 rel max -- sym max' }
  rel case
    1 of m1 ev-sym.type + @ endof
    2 of m2 ev-sym.type + @ endof
    3 of m1 ev-sym.type + @ endof
  endcase
  max 1+
  m1 ev-sym.explicit + @ m2 ev-sym.explicit + @ or
  ev-sym-new
  max 1+ ;

: ev-spec-cprefix { spec len ts -- spec|0 }
  spec ev-spec-clone { result }
  len 0> if
    result ev-spec-left-count len < if 0 exit then
    result ev-spec-right-count len < if 0 exit then
    0 result ev-spec-increment-wild
    result ev-spec-max-pos { rmax }
    len 0 ?do
      i result ev-spec.left + @ ev-vec@ { m1 }
      i result ev-spec.right + @ ev-vec@ { m2 }
      m1 ev-sym.type + @ m2 ev-sym.type + @ ts ev-ts-relation { rel }
      rel 0= if 0 unloop exit then
      m1 m2 rel rmax ev-new-merged-sym { fresh newmax }
      newmax to rmax
      m1 fresh result ev-spec-substitute drop
      m2 fresh result ev-spec-substitute drop
    loop
  then
  4 ev-vec-new { tmp }
  result tmp ev-vec-push
  tmp result ev-spec-list-normalize ;

: ev-spec-unify { s1 s2 ts -- spec|0 }
  s2 0= if 0 exit then
  s1 ev-spec-left-count { p1 }
  s1 ev-spec-right-count { p2 }
  s2 ev-spec-left-count { q1 }
  s2 ev-spec-right-count { q2 }
  p1 q1 < if 0 exit then
  p2 q2 < if 0 exit then
  s1 ev-spec-clone { result }
  0 result ev-spec-increment-wild
  result ev-spec-max-pos { tcmax }
  s2 ev-spec-clone { tc }
  tcmax tc ev-spec-increment-wild
  tc ev-spec-max-pos to tcmax
  q1 0 ?do
    i result ev-spec.left + @ ev-vec@ { m1 }
    i tc ev-spec.left + @ ev-vec@ { m2 }
    m1 ev-sym.type + @ m2 ev-sym.type + @ ts ev-ts-relation { rel }
    rel 0= if 0 unloop exit then
    m1 m2 rel tcmax ev-new-merged-sym { fresh newmax }
    newmax to tcmax
    m1 fresh result ev-spec-substitute drop
    m2 fresh result ev-spec-substitute drop
    m1 fresh tc ev-spec-substitute drop
    m2 fresh tc ev-spec-substitute drop
  loop
  q2 0 ?do
    i result ev-spec.right + @ ev-vec@ { m1 }
    i tc ev-spec.right + @ ev-vec@ { m2 }
    m1 ev-sym.type + @ m2 ev-sym.type + @ ts ev-ts-relation { rel }
    rel 0= if 0 unloop exit then
    m1 m2 rel tcmax ev-new-merged-sym { fresh newmax }
    newmax to tcmax
    m1 fresh result ev-spec-substitute drop
    m2 fresh result ev-spec-substitute drop
    m1 fresh tc ev-spec-substitute drop
    m2 fresh tc ev-spec-substitute drop
  loop
  tcmax result ev-spec.max-pos + !
  4 ev-vec-new { tmp }
  result tmp ev-vec-push
  tmp result ev-spec-list-normalize ;

: ev-spec-glb { s1 s2 ts -- spec|0 }
  s2 0= if 0 exit then
  s1 ev-spec-left-count { n1 }
  s1 ev-spec-right-count { n2 }
  s2 ev-spec-left-count { m1 }
  s2 ev-spec-right-count { m2 }
  n1 m1 > if
    n1 m1 - { plen }
    n2 m2 - plen <> if 0 exit then
    s1 plen ts ev-spec-cprefix dup 0= if exit then
    s2 ts ev-spec-unify exit
  else
    m1 n1 - { plen }
    m2 n2 - plen <> if 0 exit then
    s2 plen ts ev-spec-cprefix dup 0= if exit then
    s1 ts ev-spec-unify exit
  then ;

: ev-spec-idemp { spec ts -- spec|0 }
  spec ev-spec-left-count spec ev-spec-right-count <> if 0 exit then
  spec spec ev-spec-left-count ts ev-spec-cprefix ;

: ev-spec-pistar { spec ts -- spec|0 }
  4 ev-vec-new { tmp }
  spec ev-spec-clone tmp ev-vec-push
  spec ev-spec-clone tmp ev-vec-push
  tmp ts ev-spec-list-evaluate { twice }
  twice 0= if 0 exit then
  spec twice ts ev-spec-glb ;

\ ----------------------------------------------------------------------
\ Spec dictionaries and declarative control structures

0 cells constant ev-entry.key
1 cells constant ev-entry.surface
2 cells constant ev-entry.value
3 cells constant /ev-entry

: ev-entry-new { key surface value -- entry }
  /ev-entry ev-xalloc { entry }
  key entry ev-entry.key + !
  surface entry ev-entry.surface + !
  value entry ev-entry.value + !
  entry ;

0 constant ev-expr.empty
1 constant ev-expr.segment
2 constant ev-expr.control
3 constant ev-expr.seq
4 constant ev-expr.glb
5 constant ev-expr.star

0 cells constant ev-expr.kind
1 cells constant ev-expr.a
2 cells constant ev-expr.b
3 cells constant /ev-expr

: ev-expr-new { kind a b -- expr }
  /ev-expr ev-xalloc { expr }
  kind expr ev-expr.kind + !
  a expr ev-expr.a + !
  b expr ev-expr.b + !
  expr ;

: ev-empty-expr ( -- expr )
  ev-expr.empty 0 0 ev-expr-new ;

: ev-segment-expr { name -- expr }
  ev-expr.segment name 0 ev-expr-new ;

: ev-control-expr { role -- expr }
  ev-expr.control role 0 ev-expr-new ;

: ev-seq-expr { parts -- expr }
  ev-expr.seq parts 0 ev-expr-new ;

: ev-glb-expr { left right -- expr }
  ev-expr.glb left right ev-expr-new ;

: ev-star-expr { inner -- expr }
  ev-expr.star inner 0 ev-expr-new ;

0 cells constant ev-struct.name
1 cells constant ev-struct.open
2 cells constant ev-struct.boundaries
3 cells constant ev-struct.optional
4 cells constant ev-struct.close
5 cells constant ev-struct.segments
6 cells constant ev-struct.meaning
7 cells constant /ev-struct

: ev-struct-new { name open boundaries optional close segments meaning -- st }
  /ev-struct ev-xalloc { st }
  name st ev-struct.name + !
  open st ev-struct.open + !
  boundaries st ev-struct.boundaries + !
  optional st ev-struct.optional + !
  close st ev-struct.close + !
  segments st ev-struct.segments + !
  meaning st ev-struct.meaning + !
  st ;

: ev-struct-boundary-count ( st -- n )
  ev-struct.boundaries + @ ev-vec-count@ ;

: ev-struct-segment-count ( st -- n )
  ev-struct.segments + @ ev-vec-count@ ;

: ev-struct-boundary@ { index st -- s }
  st ev-struct.boundaries + @ index swap ev-vec@ ;

: ev-struct-optional? { index st -- flag }
  st ev-struct.optional + @ index swap ev-vec@ 0<> ;

: ev-struct-segment@ { index st -- s }
  st ev-struct.segments + @ index swap ev-vec@ ;

: ev-struct-segment-index { name st -- idx|-1 }
  name ev-canon-sptr { key }
  st ev-struct.segments + @ { segs }
  segs ev-vec-count@ 0 ?do
    i segs ev-vec@ ev-canon-sptr key ev-s= if
      i unloop exit
    then
  loop
  -1 ;

: ev-struct-uses-role? { role st -- flag }
  role st ev-struct.open + @ ev-s= if true exit then
  role st ev-struct.close + @ ev-s= if true exit then
  st ev-struct.boundaries + @ { bounds }
  bounds ev-vec-count@ 0 ?do
    role i bounds ev-vec@ ev-s= if true unloop exit then
  loop
  false ;

: ev-struct-same-signature? { a b -- flag }
  a ev-struct.open + @ b ev-struct.open + @ ev-s= 0= if false exit then
  a ev-struct.close + @ b ev-struct.close + @ ev-s= 0= if false exit then
  a ev-struct-boundary-count b ev-struct-boundary-count <> if false exit then
  a ev-struct-boundary-count 0 ?do
    i a ev-struct-boundary@ i b ev-struct-boundary@ ev-s= 0= if
      false unloop exit
    then
    i a ev-struct-optional? i b ev-struct-optional? <> if
      false unloop exit
    then
  loop
  true ;

0 cells constant ev-ss.words
1 cells constant ev-ss.literals
2 cells constant ev-ss.structures
3 cells constant /ev-ss

: ev-ss-new ( -- ss )
  /ev-ss ev-xalloc { ss }
  64 ev-vec-new ss ev-ss.words + !
  8 ev-vec-new ss ev-ss.literals + !
  8 ev-vec-new ss ev-ss.structures + !
  ss ;

: ev-ss-find-entry { key vec -- entry|0 }
  key ev-canon-sptr { canon }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ { entry }
    canon entry ev-entry.key + @ ev-s= if
      entry unloop exit
    then
  loop
  0 ;

: ev-ss-find-word-entry { name ss -- entry|0 }
  name ss ev-ss.words + @ ev-ss-find-entry ;

: ev-ss-find-literal-entry { kind ss -- entry|0 }
  kind ss ev-ss.literals + @ ev-ss-find-entry ;

: ev-ss-word@ { name ss -- spec|0 }
  name ss ev-ss-find-word-entry dup if ev-entry.value + @ exit then ;

: ev-ss-literal@ { kind ss -- spec|0 }
  kind ss ev-ss-find-literal-entry dup if ev-entry.value + @ exit then ;

: ev-ss-add-entry { surface value vec span -- }
  surface ev-canon-sptr { key }
  key vec ev-ss-find-entry if
    s" Duplicate specification for " ev-scopy surface ev-scat2
    0 span ev-error-msg
  then
  key surface value ev-entry-new vec ev-vec-push ;

: ev-ss-add-word { surface spec span ss -- }
  surface spec ss ev-ss.words + @ span ev-ss-add-entry ;

: ev-ss-add-literal { kind spec span ss -- }
  kind spec ss ev-ss.literals + @ span ev-ss-add-entry ;

: ev-ss-set-word { surface spec ss -- }
  surface ev-canon-sptr { key }
  ss ev-ss.words + @ { vec }
  key vec ev-ss-find-entry { entry }
  entry if
    surface entry ev-entry.surface + !
    spec entry ev-entry.value + !
  else
    key surface spec ev-entry-new vec ev-vec-push
  then ;

: ev-ss-add-structure { st ss -- }
  ss ev-ss.structures + @ { vec }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ st ev-struct-same-signature? if
      drop unloop exit
    then
  loop
  st vec ev-vec-push ;

: ev-ss-open-structures { role ss -- vec }
  4 ev-vec-new { out }
  ss ev-ss.structures + @ { structs }
  structs ev-vec-count@ 0 ?do
    i structs ev-vec@ { st }
    role st ev-struct.open + @ ev-s= if st out ev-vec-push then
  loop
  out ;

: ev-ss-role-entry { role ss -- entry|0 }
  ss ev-ss.words + @ { vec }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ { entry }
    entry ev-entry.value + @ { spec }
    spec ev-spec.control-mode + @ dup if
      role ev-s= if entry unloop exit then
    else
      drop
    then
  loop
  0 ;

: ev-word-key= { word c-addr u -- flag }
  word ev-word-text@ ev-canon-sptr ev-s@ c-addr u compare 0= ;

: ev-word-text= { word c-addr u -- flag }
  word ev-word-text@ ev-s@ c-addr u compare 0= ;

: ev-key= { s c-addr u -- flag }
  s ev-canon-sptr ev-s@ c-addr u compare 0= ;

: ev-directive-sptr { text -- s }
  text ev-canon-sptr { key }
  key ev-s@ { addr u }
  u 0> if
    addr u 1- + c@ [char] : = if
      addr u 1- ev-scopy exit
    then
  then
  key ;

: ev-word-directive= { word c-addr u -- flag }
  word ev-word-text@ ev-directive-sptr ev-s@ c-addr u compare 0= ;

: ev-word-directive-text= { word c-addr u -- flag }
  word ev-word-text@ ev-s@ { addr wu }
  wu 0> if
    addr wu 1- + c@ [char] : = if
      addr wu 1- c-addr u compare 0= exit
    then
  then
  addr wu c-addr u compare 0= ;

: ev-canon-segment-name { text -- s }
  text ev-s@ { addr u }
  cell u + ev-xalloc { out }
  u out !
  u 0 ?do
    addr i + c@ { ch }
    ch [char] a >= ch [char] z <= and if
      ch 32 - out cell+ i + c!
    else
      ch [char] A >= ch [char] Z <= and
      ch [char] 0 >= ch [char] 9 <= and or if
        ch out cell+ i + c!
      else
        [char] _ out cell+ i + c!
      then
    then
  loop
  out ;

: ev-metasymbol-name { token -- s|0 }
  token ev-s@ { addr u }
  u 3 < if 0 exit then
  addr c@ [char] < <> if 0 exit then
  addr u 1- + c@ [char] > <> if 0 exit then
  addr 1+ u 2 - ev-scopy ev-canon-segment-name ;

: ev-line-range>sptr { start stop line -- s }
  0 0 ev-scopy { out }
  stop start ?do
    i line ev-vec@ ev-word-text@ { piece }
    out ev-slen@ 0= if
      piece ev-sdup to out
    else
      out ev-sspace ev-scat2 piece ev-scat2 to out
    then
  loop
  out ;

: ev-append-line { line$ buffer -- buffer' }
  line$ ev-slen@ 0= if line$ drop buffer exit then
  buffer ev-slen@ 0> if
    buffer 10 ev-sfrom-char ev-scat2
  else
    buffer
  then
  line$ ev-scat2 ;

: ev-ctl-tokenize { text -- vec }
  s" <control>" ev-scopy text ev-sc-new { sc }
  8 ev-vec-new { vec }
  begin
    sc ev-sc-skip-whitespace
    sc ev-sc-at-end? 0=
  while
    sc ev-sc-char@ { ch }
    ch [char] [ = ch [char] ] = or if
      ch ev-sfrom-char vec ev-vec-push
      sc ev-sc-advance
    else
      ch [char] < = if
        sc ev-sc-advance
        s" >" ev-scopy sc ev-sc-parse-until dup 0= if
          s" Unclosed metasymbol" ev-scopy 0 sc ev-sc-position-span ev-error-msg
        then
        ev-word-text@ { body }
        s" <" ev-scopy body ev-scat2 s" >" ev-scopy ev-scat2 vec ev-vec-push
      else
        s" []<" sc ev-sc-read-word dup if
          ev-word-text@ vec ev-vec-push
        else
          drop
        then
      then
    then
  repeat
  vec ;

: ev-seq-collapse { parts -- expr }
  parts ev-vec-count@ 0= if ev-empty-expr exit then
  parts ev-vec-count@ 1 = if 0 parts ev-vec@ exit then
  parts ev-seq-expr ;

: ev-effect-atom { token -- expr }
  token ev-metasymbol-name dup if
    ev-segment-expr exit
  then
  drop
  token ev-canon-sptr ev-control-expr ;

: ev-parse-effect-line { line$ -- expr }
  line$ ev-s@ ev-trim-range ev-scopy { trimmed }
  trimmed ev-slen@ 0= if ev-empty-expr exit then
  trimmed ev-ctl-tokenize { toks }
  toks ev-vec-count@ 0= if ev-empty-expr exit then
  0 toks ev-vec@ { head }
  head s" EITHER" ev-key= if
    toks ev-vec-count@ 3 < if
      s" EITHER requires two alternatives" ev-scopy 0 0 ev-error-msg
    then
    1 toks ev-vec@ ev-effect-atom { result }
    toks ev-vec-count@ 2 ?do
      result i toks ev-vec@ ev-effect-atom ev-glb-expr to result
    loop
    result exit
  then
  head s" REPEAT" ev-key= if
    toks ev-vec-count@ 2 < if
      s" REPEAT requires a repeated effect" ev-scopy 0 0 ev-error-msg
    then
    4 ev-vec-new { parts }
    toks ev-vec-count@ 1 ?do
      i toks ev-vec@ ev-effect-atom parts ev-vec-push
    loop
    parts ev-seq-collapse ev-star-expr exit
  then
  4 ev-vec-new { parts }
  toks ev-vec-count@ 0 ?do
    i toks ev-vec@ ev-effect-atom parts ev-vec-push
  loop
  parts ev-seq-collapse ;

: ev-lines>sptr { vec -- s }
  ev-sempty { out }
  vec ev-vec-count@ 0 ?do
    i vec ev-vec@ out ev-append-line to out
  loop
  out ;

: ev-parse-control-meaning { text -- expr }
  text ev-split-lines { lines }
  8 ev-vec-new { parts }
  lines ev-vec-count@ 0 ?do
    i lines ev-vec@ ev-parse-effect-line { expr }
    expr ev-expr.kind + @ ev-expr.empty <> if expr parts ev-vec-push then
  loop
  parts ev-seq-collapse ;

: ev-parse-control-syntax { text -- st }
  text ev-ctl-tokenize { toks }
  toks ev-vec-count@ 3 < if
    s" Malformed SYNTAX clause" ev-scopy 0 0 ev-error-msg
  then
  8 ev-vec-new { bounds }
  8 ev-vec-new { opt }
  8 ev-vec-new { segs }
  0 { idx }
  idx toks ev-vec@ ev-canon-sptr { open }
  idx 1+ to idx
  idx toks ev-vec@ ev-metasymbol-name dup 0= if
    s" Missing first segment in SYNTAX" ev-scopy 0 0 ev-error-msg
  then segs ev-vec-push
  idx 1+ to idx
  begin
    idx toks ev-vec-count@ 1- <
  while
    false { optional? }
    idx toks ev-vec@ s" [" ev-key= if
      true to optional?
      idx 1+ to idx
    then
    idx toks ev-vec-count@ 1- >= if
      s" Missing boundary word in SYNTAX" ev-scopy 0 0 ev-error-msg
    then
    idx toks ev-vec@ ev-canon-sptr { role }
    idx 1+ to idx
    idx toks ev-vec-count@ 1- >= if
      s" Missing segment metasymbol in SYNTAX" ev-scopy 0 0 ev-error-msg
    then
    idx toks ev-vec@ ev-metasymbol-name dup 0= if
      s" Missing segment metasymbol in SYNTAX" ev-scopy 0 0 ev-error-msg
    then { segname }
    idx 1+ to idx
    optional? if
      idx toks ev-vec-count@ 1- >= if
        s" Missing ] in SYNTAX" ev-scopy 0 0 ev-error-msg
      then
      idx toks ev-vec@ s" ]" ev-key= 0= if
        s" Missing ] in SYNTAX" ev-scopy 0 0 ev-error-msg
      then
      idx 1+ to idx
    then
    role bounds ev-vec-push
    optional? if 1 else 0 then opt ev-vec-push
    segname segs ev-vec-push
  repeat
  idx toks ev-vec-count@ >= if
    s" Missing closing control word in SYNTAX" ev-scopy 0 0 ev-error-msg
  then
  idx toks ev-vec@ ev-canon-sptr { close }
  ev-sempty open bounds opt close segs 0 ev-struct-new ;

: ev-install-builtin-structure { open close ss -- }
  close drop
  open drop
  ss drop ;

\ Seeds the legacy IF/BEGIN/DO families so old spec files still work without syntax blocks.
: ev-ss-install-builtins { ss -- }
  1 ev-vec-new { b1 } 1 ev-vec-new { o1 } 2 ev-vec-new { s1 } 2 ev-vec-new { p1 }
  s" ELSE" ev-scopy b1 ev-vec-push
  1 o1 ev-vec-push
  s" THEN_BRANCH" ev-scopy ev-canon-segment-name s1 ev-vec-push
  s" ELSE_BRANCH" ev-scopy ev-canon-segment-name s1 ev-vec-push
  s" IF" ev-scopy ev-control-expr p1 ev-vec-push
  s" THEN_BRANCH" ev-scopy ev-canon-segment-name ev-segment-expr
  s" ELSE_BRANCH" ev-scopy ev-canon-segment-name ev-segment-expr ev-glb-expr
  p1 ev-vec-push
  p1 ev-seq-expr { m1 }
  s" IF" ev-scopy s" IF" ev-scopy b1 o1 s" FI" ev-scopy s1 m1
  ev-struct-new ss ev-ss-add-structure

  1 ev-vec-new { b2 } 1 ev-vec-new { o2 } 2 ev-vec-new { s2 }
  2 ev-vec-new { p2 } 2 ev-vec-new { p2prefix }
  s" WHILE" ev-scopy b2 ev-vec-push
  0 o2 ev-vec-push
  s" LOOP_PREFIX" ev-scopy ev-canon-segment-name s2 ev-vec-push
  s" LOOP_BODY" ev-scopy ev-canon-segment-name s2 ev-vec-push
  s" LOOP_PREFIX" ev-scopy ev-canon-segment-name ev-segment-expr p2prefix ev-vec-push
  s" WHILE" ev-scopy ev-control-expr p2prefix ev-vec-push
  p2prefix ev-seq-expr ev-star-expr p2 ev-vec-push
  s" LOOP_BODY" ev-scopy ev-canon-segment-name ev-segment-expr ev-star-expr p2 ev-vec-push
  p2 ev-seq-expr { m2 }
  s" BUILTIN_WHILE" ev-scopy s" BEGIN" ev-scopy b2 o2 s" REPEAT" ev-scopy s2 m2
  ev-struct-new ss ev-ss-add-structure

  0 ev-vec-new { b3 } 0 ev-vec-new { o3 } 1 ev-vec-new { s3 }
  s" LOOP_BODY" ev-scopy ev-canon-segment-name s3 ev-vec-push
  s" LOOP_BODY" ev-scopy ev-canon-segment-name ev-segment-expr ev-star-expr { m3 }
  s" BUILTIN_AGAIN" ev-scopy s" BEGIN" ev-scopy b3 o3 s" AGAIN" ev-scopy s3 m3
  ev-struct-new ss ev-ss-add-structure

  0 ev-vec-new { b4 } 0 ev-vec-new { o4 } 1 ev-vec-new { s4 } 2 ev-vec-new { p4 }
  s" LOOP_BODY" ev-scopy ev-canon-segment-name s4 ev-vec-push
  s" LOOP_BODY" ev-scopy ev-canon-segment-name ev-segment-expr p4 ev-vec-push
  s" UNTIL" ev-scopy ev-control-expr p4 ev-vec-push
  p4 ev-seq-expr ev-star-expr { m4 }
  s" BUILTIN_UNTIL" ev-scopy s" BEGIN" ev-scopy b4 o4 s" UNTIL" ev-scopy s4 m4
  ev-struct-new ss ev-ss-add-structure

  0 ev-vec-new { b5 } 0 ev-vec-new { o5 } 1 ev-vec-new { s5 } 2 ev-vec-new { p5 }
  s" LOOP_BODY" ev-scopy ev-canon-segment-name s5 ev-vec-push
  s" DO" ev-scopy ev-control-expr p5 ev-vec-push
  s" LOOP_BODY" ev-scopy ev-canon-segment-name ev-segment-expr ev-star-expr p5 ev-vec-push
  p5 ev-seq-expr { m5 }
  s" BUILTIN_DO" ev-scopy s" DO" ev-scopy b5 o5 s" LOOP" ev-scopy s5 m5
  ev-struct-new ss ev-ss-add-structure ;

\ ----------------------------------------------------------------------
\ Native spec-set loader

: ev-parse-mode-from { tok -- mode }
  tok s" until" ev-word-text= if ev-parse.until exit then
  tok s" word" ev-word-text= if ev-parse.word exit then
  tok s" definition" ev-word-text= if ev-parse.definition exit then
  0 ;

: ev-define-mode-from { tok -- mode }
  tok s" colon" ev-word-text= if ev-define.colon exit then
  tok s" constant" ev-word-text= if ev-define.constant exit then
  tok s" variable" ev-word-text= if ev-define.variable exit then
  0 ;

: ev-state-mode-from { tok -- mode }
  tok s" interpret" ev-word-text= if ev-state.interpret exit then
  tok s" compile" ev-word-text= if ev-state.compile exit then
  tok s" outer" ev-word-text= if ev-state.interpret exit then
  tok s" definition" ev-word-text= if ev-state.compile exit then
  0 ;

: ev-parse-mode-needs-arg? { mode -- flag }
  mode ev-parse.until = mode ev-parse.definition = or ;

: ev-clause-starter? { tok -- flag }
  tok s" parse" ev-word-text= if true exit then
  tok s" define" ev-word-text= if true exit then
  tok s" control" ev-word-text= if true exit then
  tok s" state" ev-word-text= if true exit then
  tok s" context" ev-word-text= if true exit then
  tok s" immediate" ev-word-text= if true exit then
  tok s" scan" ev-word-text= if true exit then
  tok s" (" ev-token-unquoted= ;

: ev-resolve-parse-string { tok ts -- s }
  tok ev-word-quoted? if tok ev-word-text@ exit then
  tok ev-word-text@ ts ev-ts-scanner-delim dup if
    exit
  then
  drop
  s" Unknown scanner delimiter " ev-scopy tok ev-word-text@ ev-scat2
  0 tok ev-word-span@ ev-error-msg ;

: ev-line-find-close { start line -- idx|-1 }
  line ev-vec-count@ start ?do
    i line ev-vec@ s" )" ev-token-unquoted= if
      i unloop exit
    then
  loop
  -1 ;

: ev-infer-define-mode { spec span -- mode }
  spec ev-spec-left-count 1 = spec ev-spec-right-count 0= and if
    ev-define.constant exit
  then
  spec ev-spec-left-count 0= spec ev-spec-right-count 1 = and if
    ev-define.variable exit
  then
  s" DEFINE without mode requires ( x -- ) or ( -- y )" ev-scopy
  0 span ev-error-msg ;

: ev-validate-define-shape { mode spec word span -- }
  mode 0= if exit then
  mode ev-define.colon = if
    spec ev-spec-left-count 0<> spec ev-spec-right-count 0<> or if
      s" DEFINE COLON must have stack effect ( -- )" ev-scopy 0 span ev-error-msg
    then
    exit
  then
  mode ev-define.constant = if
    spec ev-spec-left-count 1 <> spec ev-spec-right-count 0<> or if
      s" DEFINE CONSTANT must have stack effect ( x -- )" ev-scopy 0 span ev-error-msg
    then
    exit
  then
  mode ev-define.variable = if
    spec ev-spec-left-count 0<> spec ev-spec-right-count 1 <> or if
      s" DEFINE VARIABLE must have stack effect ( -- y )" ev-scopy 0 span ev-error-msg
    then
  then ;

\ Parses one ordinary word specification line, including parser/define/control metadata.
: ev-parse-word-spec-line { line ts ss -- }
  0 line ev-vec@ { word }
  word ev-word-text@ ev-s@ { waddr wu }
  -1 { openi }
  line ev-vec-count@ 1 ?do
    i line ev-vec@ s" (" ev-token-unquoted= if
      i to openi
      leave
    then
  loop
  openi 0< if
    s" Missing ( in specification" ev-scopy 0 word ev-word-span@ ev-error-msg
  then
  openi line ev-line-find-close { closei }
  closei 0< if
    s" Missing ) in specification" ev-scopy 0 word ev-word-span@ ev-error-msg
  then
  openi 1+ closei line ev-line-range>sptr { body }
  body ts
  word ev-word-span@ closei line ev-vec@ ev-word-span@ ev-span-cover
  ev-parse-spec-body { bodyspec }
  ev-parse.none { parsemode }
  0 { parsestring }
  ev-define.none { definemode }
  false { defineseen }
  0 { controlmode }
  ev-state.any { statemode }
  false { immediate }
  1 { idx }
  begin
    idx openi <
  while
    idx line ev-vec@ { tok }
    tok s" parse" ev-word-text= if
      idx 1+ to idx
      idx openi >= if s" Missing parser mode" ev-scopy 0 tok ev-word-span@ ev-error-msg then
      idx line ev-vec@ { modetok }
      modetok ev-parse-mode-from { parsedmode }
      parsedmode dup 0= if
        s" Unknown parser mode" ev-scopy 0 idx line ev-vec@ ev-word-span@ ev-error-msg
      then to parsemode
      idx 1+ to idx
      parsemode ev-parse-mode-needs-arg? if
        idx openi >= if s" Missing parser delimiter" ev-scopy 0 tok ev-word-span@ ev-error-msg then
        idx line ev-vec@ ts ev-resolve-parse-string to parsestring
        idx 1+ to idx
      then
    else tok s" define" ev-word-text= if
      true to defineseen
      idx 1+ to idx
      idx openi < if
        idx line ev-vec@ ev-clause-starter? 0= if
          idx line ev-vec@ ev-define-mode-from dup 0= if
            s" Unknown defining mode" ev-scopy 0 idx line ev-vec@ ev-word-span@ ev-error-msg
          then to definemode
          idx 1+ to idx
        then
      then
    else tok s" control" ev-word-text= if
      idx 1+ to idx
      idx openi >= if s" Missing control mode" ev-scopy 0 tok ev-word-span@ ev-error-msg then
      idx line ev-vec@ ev-word-text@ ev-canon-sptr to controlmode
      idx 1+ to idx
    else tok s" state" ev-word-text= if
      idx 1+ to idx
      idx openi >= if s" Missing state mode" ev-scopy 0 tok ev-word-span@ ev-error-msg then
      idx line ev-vec@ ev-state-mode-from dup 0= if
        s" Unknown state mode" ev-scopy 0 idx line ev-vec@ ev-word-span@ ev-error-msg
      then to statemode
      idx 1+ to idx
    else tok s" context" ev-word-text= if
      idx 1+ to idx
      idx openi >= if s" Missing context mode" ev-scopy 0 tok ev-word-span@ ev-error-msg then
      idx line ev-vec@ ev-state-mode-from dup 0= if
        s" Unknown context mode" ev-scopy 0 idx line ev-vec@ ev-word-span@ ev-error-msg
      then to statemode
      idx 1+ to idx
    else tok s" immediate" ev-word-text= if
      true to immediate
      idx 1+ to idx
    else tok s" scan" ev-word-text= if
      idx 1+ to idx
      idx openi >= if s" Missing scanner delimiter" ev-scopy 0 tok ev-word-span@ ev-error-msg then
      ev-parse.until to parsemode
      idx line ev-vec@ ts ev-resolve-parse-string to parsestring
      idx 1+ to idx
    else
      parsemode ev-parse.none <> if
        s" Duplicate scanner/parser clause" ev-scopy 0 tok ev-word-span@ ev-error-msg
      then
      tok ts ev-resolve-parse-string to parsestring
      ev-parse.until to parsemode
      idx 1+ to idx
    then then then then then then then
  repeat
  defineseen definemode ev-define.none = and if
    bodyspec word ev-word-span@ ev-infer-define-mode to definemode
  then
  definemode bodyspec word ev-word-text@ word ev-word-span@ ev-validate-define-shape
  bodyspec parsemode parsestring ev-spec-with-parse { outspec }
  outspec definemode ev-spec-with-define to outspec
  outspec controlmode ev-spec-with-control to outspec
  outspec immediate ev-spec-with-immediate to outspec
  outspec statemode ev-spec-with-state to outspec
  outspec word ev-word-span@ 0 ev-spec-with-origin to outspec
  word ev-word-text@ outspec word ev-word-span@ ss ev-ss-add-word
  ;

: ev-parse-literal-line { line ts ss -- }
  line ev-vec-count@ 4 < if
    s" Malformed literal specification" ev-scopy 0 0 line ev-vec@ ev-word-span@ ev-error-msg
  then
  1 line ev-vec@ { kind }
  2 { openi }
  openi line ev-vec@ s" (" ev-token-unquoted= 0= if
    s" Missing ( in literal specification" ev-scopy 0 kind ev-word-span@ ev-error-msg
  then
  openi line ev-line-find-close { closei }
  closei 0< if
    s" Missing ) in literal specification" ev-scopy 0 kind ev-word-span@ ev-error-msg
  then
  openi 1+ closei line ev-line-range>sptr
  ts
  kind ev-word-span@ closei line ev-vec@ ev-word-span@ ev-span-cover
  ev-parse-spec-body { spec }
  spec ev-spec-left-count 0<> if
    s" LITERAL must not consume stack input" ev-scopy 0 kind ev-word-span@ ev-error-msg
  then
  kind ev-word-text@ spec kind ev-word-span@ ss ev-ss-add-literal ;

\ Collects one indented syntax/effect block and turns it into a declarative structure entry.
: ev-parse-syntax-block { sc head line ss -- pending|0 }
  head ev-word-span@ ev-span.scol + @ { basecol }
  8 ev-vec-new { syntaxlines }
  8 ev-vec-new { effectlines }
  line ev-vec-count@ 1 > if
    1 line ev-vec-count@ line ev-line-range>sptr syntaxlines ev-vec-push
  then
  0 { pending }
  false { have-effect }
  begin
    sc ev-sc-next-line-atoms dup
    dup 0= if
      drop true
    else
      { nextline }
      nextline ev-vec-count@ 0= if
        false
      else
        0 nextline ev-vec@ ev-word-span@ ev-span.scol + @ basecol <=
      then if
        nextline to pending
        true
      else
        nextline ev-vec-count@ 0= if
        else
          0 nextline ev-vec@ { first }
          have-effect 0= first s" effect" ev-word-directive-text= or if
            first s" effect" ev-word-directive-text= if
              true to have-effect
              nextline ev-vec-count@ 1 > if
                1 nextline ev-vec-count@ nextline ev-line-range>sptr effectlines ev-vec-push
              then
            else
              0 nextline ev-vec-count@ nextline ev-line-range>sptr syntaxlines ev-vec-push
            then
          else
            0 nextline ev-vec-count@ nextline ev-line-range>sptr effectlines ev-vec-push
          then
        then
        false
      then
    then
  until
  syntaxlines ev-lines>sptr ev-parse-control-syntax { st }
  effectlines ev-lines>sptr ev-parse-control-meaning st ev-struct.meaning + !
  st ss ev-ss-add-structure
  pending ;

\ Loads the spec file into the native dictionaries and declarative structure table.
: ev-ss-load { file ts -- ss }
  ev-ss-new { ss }
  file ev-sc-from-file { sc }
  sc ev-sc.lines + @ ev-current-source-lines !
  0 { pending }
  0 { line }
  begin
    pending if
      pending to line
      0 to pending
      true
    else
      sc ev-sc-next-line-atoms dup to line
      if true else false then
    then
  while
    line ev-vec-count@ 0= if
    else
      0 line ev-vec@ { head }
      head s" literal" ev-word-directive-text= if
        line ts ss ev-parse-literal-line
      else head s" syntax" ev-word-directive-text= if
        sc head line ss ev-parse-syntax-block to pending
      else
        line ts ss ev-parse-word-spec-line
      then then
    then
  repeat
  ss ev-ss-install-builtins
  ss ;

\ ----------------------------------------------------------------------
\ Native program parser and evaluator

0 cells constant ev-prog.name
1 cells constant ev-prog.text
2 cells constant ev-prog.lines
3 cells constant ev-prog.words
4 cells constant ev-prog.spans
5 cells constant ev-prog.specs
6 cells constant /ev-prog

: ev-prog-new { name text lines -- prog }
  /ev-prog ev-xalloc { prog }
  name prog ev-prog.name + !
  text prog ev-prog.text + !
  lines prog ev-prog.lines + !
  32 ev-vec-new prog ev-prog.words + !
  32 ev-vec-new prog ev-prog.spans + !
  32 ev-vec-new prog ev-prog.specs + !
  prog ;

: ev-prog-add-word { word span spec prog -- }
  word prog ev-prog.words + @ ev-vec-push
  span prog ev-prog.spans + @ ev-vec-push
  spec span word ev-spec-with-origin prog ev-prog.specs + @ ev-vec-push ;

: ev-spec-consumes-until? { spec -- flag }
  spec ev-spec.parse-mode + @ ev-parse.until =
  spec ev-spec.parse-string + @ 0<> and ;

: ev-spec-consumes-word? { spec -- flag }
  spec ev-spec.parse-mode + @ ev-parse.word = ;

: ev-spec-starts-definition? { spec -- flag }
  spec ev-spec.parse-mode + @ ev-parse.definition = ;

: ev-spec-defines-word? { spec -- flag }
  spec ev-spec.define-mode + @ ev-define.none <> ;

: ev-spec-is-control? { spec -- flag }
  spec ev-spec.control-mode + @ 0<> ;

: ev-spec-is-immediate? { spec -- flag }
  spec ev-spec.immediate + @ 0<>
  spec ev-spec.parse-mode + @ ev-parse.none <> or
  spec ev-spec.define-mode + @ ev-define.none <> or
  spec ev-spec.control-mode + @ dup if
    spec ev-spec.control-mode + @ s" INDEX" ev-key= 0=
  else
    drop false
  then or ;

: ev-spec-effective-state { spec -- mode }
  spec ev-spec.state-mode + @ dup ev-state.any <> if exit then
  spec ev-spec.define-mode + @ ev-define.none <> if ev-state.interpret exit then
  spec ev-spec.control-mode + @ 0<> if ev-state.compile exit then
  ev-state.any ;

: ev-spec-allowed-interpret? { spec -- flag }
  spec ev-spec-effective-state ev-state.compile <> ;

: ev-spec-allowed-compile? { spec -- flag }
  spec ev-spec-effective-state ev-state.interpret <> ;

: ev-runtime-clone { spec -- copy }
  spec ev-spec-copy-left
  spec ev-spec-copy-right
  ev-spec-new ;

: ev-next-prog-word { sc -- word|0 }
  0 0 sc ev-sc-next-program-word dup ev-current-program-token ! ;

: ev-int-literal? { text -- flag }
  text ev-s@ { addr u }
  u 0= if false exit then
  0 { idx }
  addr c@ dup [char] + = swap [char] - = or if
    u 1 = if false exit then
    1 to idx
  then
  idx u >= if false exit then
  u idx ?do
    addr i + c@ dup [char] 0 >= swap [char] 9 <= and 0= if
      false unloop exit
    then
  loop
  true ;

: ev-double-literal? { text -- flag }
  text ev-s@ { addr u }
  u 2 < if false exit then
  addr u 1- + c@ [char] . <> if false exit then
  addr u 1- ev-scopy ev-int-literal? ;

: ev-control-runtime-spec { role ts ss span -- spec }
  role ss ev-ss-role-entry dup if
    ev-entry.value + @ ev-runtime-clone exit
  then
  drop
  role s" DO" ev-key= if
    s" n[2] n[1] --" ts span ev-parse-spec-body exit
  then
  role s" INDEX" ev-key= if
    s" -- n" ts span ev-parse-spec-body exit
  then
  s" flag --" ts span ev-parse-spec-body ;

\ Resolves a program token to the runtime effect it contributes at the current nesting depth.
: ev-resolve-runtime-spec { token do-depth ts ss -- spec }
  token ev-word-text@ ss ev-ss-word@ { spec }
  spec if
    spec ev-spec-is-control? if
      spec ev-spec.control-mode + @ s" INDEX" ev-key= do-depth 0> and if
        spec ev-spec.control-mode + @ ts ss token ev-word-span@ ev-control-runtime-spec exit
      then
      s" Unexpected control word" ev-scopy 0 token ev-word-span@ ev-error-msg
    then
    spec ev-runtime-clone exit
  then
  token ev-word-text@ ev-double-literal? if
    s" DOUBLE" ev-scopy ss ev-ss-literal@ dup if ev-runtime-clone exit then
    drop
    s" No literal specification for double literal" ev-scopy 0 token ev-word-span@ ev-error-msg
  then
  token ev-word-text@ ev-int-literal? if
    s" INTEGER" ev-scopy ss ev-ss-literal@ dup if ev-runtime-clone exit then
    drop
    s" No literal specification for integer literal" ev-scopy 0 token ev-word-span@ ev-error-msg
  then
  s" No specification found for " ev-scopy token ev-word-text@ ev-scat2
  0 token ev-word-span@ ev-error-msg ;

: ev-consume-parser-input { token spec sc -- span }
  spec ev-spec-consumes-word? if
    sc ev-next-prog-word dup 0= if
      s" Missing word after parser word" ev-scopy 0 token ev-word-span@ ev-error-msg
    then
    ev-word-span@ token ev-word-span@ swap ev-span-cover exit
  then
  spec ev-spec-consumes-until? if
    sc ev-sc-skip-whitespace
    spec ev-spec.parse-string + @ sc ev-sc-parse-until dup if
      ev-word-span@ token ev-word-span@ swap ev-span-cover exit
    then
    drop
    s" Missing closing delimiter for parser word" ev-scopy 0 token ev-word-span@ ev-error-msg
  then
  token ev-word-span@ ;

: ev-definition-end-spec? { spec -- flag }
  spec 0= if false exit then
  spec ev-spec-is-control? 0= if false exit then
  spec ev-spec.control-mode + @ s" END" ev-key= ;

: ev-definition-starter-token? { tok ss -- flag }
  tok 0= if false exit then
  tok ev-word-text@ ss ev-ss-word@ dup 0= if drop false exit then { spec }
  spec ev-spec.define-mode + @ ev-define.colon = ;

: ev-ignore-parser-input-error { tok spec sc -- }
  ev-current-diagnostic @ { saved }
  tok spec sc ['] ev-consume-parser-input catch dup if
    { code }
    drop drop drop
  else
    drop drop
  then
  saved ev-current-diagnostic ! ;

: ev-skip-recovery-payload { tok spec sc -- }
  tok 0= spec 0= or if exit then
  spec ev-spec-defines-word? if
    sc ev-next-prog-word drop
    exit
  then
  spec ev-spec-is-immediate? if
    tok spec sc ev-ignore-parser-input-error
  then ;

: ev-recover-definition { sc tok spec ss -- }
  tok 0= if exit then
  spec ev-definition-end-spec? if exit then
  tok ss ev-definition-starter-token? if 1 else 0 then { nested }
  tok spec sc ev-skip-recovery-payload
  begin
    sc ev-next-prog-word dup
  while
    { skipped }
    skipped ev-word-text@ ss ev-ss-word@ { skippedspec }
    skipped ss ev-definition-starter-token? if
      nested 1+ to nested
      skipped skippedspec sc ev-skip-recovery-payload
    else
      skippedspec ev-definition-end-spec? if
        nested 0> if
          nested 1- to nested
        else
          exit
        then
      else
        skipped skippedspec sc ev-skip-recovery-payload
      then
    then
  repeat
  drop ;

: ev-recover-top-level { sc tok spec ss -- }
  spec 0= if exit then
  spec ev-spec-defines-word? if
    spec ev-spec.define-mode + @ ev-define.colon = if
      ev-current-program-token @ { badtok }
      badtok dup if badtok ev-word-text@ ss ev-ss-word@ else 0 then { badspec }
      sc badtok badspec ss ev-recover-definition
    then
    exit
  then
  spec ev-spec-is-immediate? if
    tok spec sc ev-skip-recovery-payload
  then ;

: ev-seq-add { word span spec seq -- }
  spec span word ev-spec-with-origin seq ev-vec-push ;

: ev-current-program-span ( -- span|0 )
  ev-current-program-token @ dup if
    ev-word-span@
  else
    drop
    0
  then ;

\ Evaluates a linear sequence of runtime effects and raises a contextual clash if composition fails.
: ev-seq-evaluate { seq context ts -- spec }
  seq ts ev-spec-list-evaluate dup if exit then
  drop
  s" Type clash in " ev-scopy context ev-scat2
  0
  ev-current-program-span
  ev-error-msg ;

: ev-control-close-match? { role stage st -- flag }
  role st ev-struct.close + @ ev-s= 0= if false exit then
  st ev-struct-boundary-count stage ?do
    i st ev-struct-optional? 0= if false unloop exit then
  loop
  true ;

: ev-filter-boundary-candidates { role stage candidates -- out }
  4 ev-vec-new { out }
  candidates ev-vec-count@ 0 ?do
    i candidates ev-vec@ { st }
    stage st ev-struct-boundary-count < if
      role stage st ev-struct-boundary@ ev-s= if st out ev-vec-push then
    then
  loop
  out ;

: ev-filter-close-candidates { role stage candidates -- out }
  4 ev-vec-new { out }
  candidates ev-vec-count@ 0 ?do
    i candidates ev-vec@ { st }
    role stage st ev-control-close-match? if st out ev-vec-push then
  loop
  out ;

: ev-structure-label { st -- s }
  st ev-struct.open + @ ev-sdup { out }
  st ev-struct-boundary-count 0 ?do
    out s" ..." ev-scopy ev-scat2
    i st ev-struct-boundary@ ev-scat2 to out
  loop
  out s" ..." ev-scopy ev-scat2 st ev-struct.close + @ ev-scat2 ;

\ Evaluates the control-effect algebra for one parsed structure instance.
: ev-eval-structure-expr { expr st segspecs ts ss span -- spec }
  expr ev-expr.kind + @ case
    ev-expr.empty of
      4 ev-vec-new 4 ev-vec-new ev-spec-new
    endof
    ev-expr.segment of
      expr ev-expr.a + @ st ev-struct-segment-index { idx }
      idx 0< if
        s" Unknown structure segment" ev-scopy 0 span ev-error-msg
      then
      idx segspecs ev-vec-count@ < if
        idx segspecs ev-vec@ ev-spec-clone
      else
        4 ev-vec-new 4 ev-vec-new ev-spec-new
      then
    endof
    ev-expr.control of
      expr ev-expr.a + @ ts ss span ev-control-runtime-spec
    endof
    ev-expr.seq of
      expr ev-expr.a + @ { parts }
      8 ev-vec-new { seq }
      parts ev-vec-count@ 0 ?do
        i parts ev-vec@ st segspecs ts ss span recurse
        seq ev-vec-push
      loop
      seq st ev-structure-label ts ev-seq-evaluate
    endof
    ev-expr.glb of
      expr ev-expr.a + @ st segspecs ts ss span recurse { left }
      expr ev-expr.b + @ st segspecs ts ss span recurse { right }
      left right ts ev-spec-glb dup 0= if
        drop s" Non-comparable control alternatives" ev-scopy 0 span ev-error-msg
      then
    endof
    ev-expr.star of
      expr ev-expr.a + @ st segspecs ts ss span recurse { inner }
      inner ts ev-spec-pistar dup 0= if
        drop s" Non-idempotent repeated effect" ev-scopy 0 span ev-error-msg
      then
    endof
  endcase ;

defer ev-parse-definition-structure

\ Parses a colon-definition body until its closing role, recursively handling nested structures.
: ev-parse-definition-seq { defname sc ts ss do-depth close-role -- spec }
  16 ev-vec-new { seq }
  begin
    sc ev-next-prog-word dup
  while
    { tok }
    tok ev-word-text@ ss ev-ss-word@ { spec }
    spec if
      spec ev-spec-is-control? if
        spec ev-spec.control-mode + @ close-role ev-s= if
          seq defname ts ev-seq-evaluate { final }
          final exit
        then
        spec ev-spec.control-mode + @ ss ev-ss-open-structures { opens }
        opens ev-vec-count@ 0> if
          tok spec defname sc ts ss do-depth ev-parse-definition-structure
          tok ev-word-text@ tok ev-word-span@ rot seq ev-seq-add
        else
          spec ev-spec.control-mode + @ s" INDEX" ev-key= do-depth 0> and if
            spec ev-spec.control-mode + @ ts ss tok ev-word-span@ ev-control-runtime-spec
            tok ev-word-text@ tok ev-word-span@ rot seq ev-seq-add
          else
            s" Unexpected control word in definition" ev-scopy 0 tok ev-word-span@ ev-error-msg
          then
        then
      else spec ev-spec-is-immediate? if
        spec ev-spec-defines-word? if
          s" Defining words are not supported inside definitions" ev-scopy 0 tok ev-word-span@ ev-error-msg
        then
        tok spec sc ev-consume-parser-input
        tok ev-word-text@ swap spec ev-runtime-clone seq ev-seq-add
      else
        tok do-depth ts ss ev-resolve-runtime-spec
        tok ev-word-text@ tok ev-word-span@ rot seq ev-seq-add
      then
      then
    else
      tok do-depth ts ss ev-resolve-runtime-spec
      tok ev-word-text@ tok ev-word-span@ rot seq ev-seq-add
    then
  repeat
  drop
  s" Missing end of definition" ev-scopy 0 0 ev-error-msg ;

:noname { opener spec defname sc ts ss do-depth -- spec }
  spec ev-spec.control-mode + @ { open-role }
  open-role ss ev-ss-open-structures { candidates }
  candidates ev-vec-count@ 0= if
    s" Unknown control structure" ev-scopy 0 opener ev-word-span@ ev-error-msg
  then
  8 ev-vec-new { segments }
  16 ev-vec-new { current }
  0 { stage }
  open-role s" DO" ev-key= if do-depth 1+ else do-depth then { inner-depth }
  begin
    sc ev-next-prog-word dup
  while
    { tok }
    tok ev-word-text@ ss ev-ss-word@ { tspec }
    tspec if
      tspec ev-spec-is-control? if
        tspec ev-spec.control-mode + @ { role }
        role stage candidates ev-filter-boundary-candidates { by-boundary }
        role stage candidates ev-filter-close-candidates { by-close }
        by-close ev-vec-count@ 0> by-boundary ev-vec-count@ 0= and if
          current segments ev-vec-push
          0 by-close ev-vec@ { st }
          segments ev-vec-count@ 4 ev-max ev-vec-new { segspecs }
          segments ev-vec-count@ 0 ?do
            i segments ev-vec@ defname ts ev-seq-evaluate segspecs ev-vec-push
          loop
          opener ev-word-span@ tok ev-word-span@ ev-span-cover { span }
          st ev-struct.meaning + @ st segspecs ts ss span ev-eval-structure-expr
          exit
        then
        by-boundary ev-vec-count@ 0> by-close ev-vec-count@ 0= and if
          current segments ev-vec-push
          16 ev-vec-new to current
          by-boundary to candidates
          stage 1+ to stage
        else
          role ss ev-ss-open-structures { opens }
          opens ev-vec-count@ 0> if
            tok tspec defname sc ts ss inner-depth recurse
            tok ev-word-text@ tok ev-word-span@ rot current ev-seq-add
          else
            role s" INDEX" ev-key= inner-depth 0> and if
              role ts ss tok ev-word-span@ ev-control-runtime-spec
              tok ev-word-text@ tok ev-word-span@ rot current ev-seq-add
            else
              s" Unexpected control word in definition" ev-scopy 0 tok ev-word-span@ ev-error-msg
            then
          then
        then
      else tspec ev-spec-is-immediate? if
        tspec ev-spec-defines-word? if
          s" Defining words are not supported inside definitions" ev-scopy 0 tok ev-word-span@ ev-error-msg
        then
        tok tspec sc ev-consume-parser-input
        tok ev-word-text@ swap tspec ev-runtime-clone current ev-seq-add
      else
        tok inner-depth ts ss ev-resolve-runtime-spec
        tok ev-word-text@ tok ev-word-span@ rot current ev-seq-add
      then
      then
    else
      tok inner-depth ts ss ev-resolve-runtime-spec
      tok ev-word-text@ tok ev-word-span@ rot current ev-seq-add
    then
  repeat
  drop
  s" Missing control terminator in definition" ev-scopy 0 opener ev-word-span@ ev-error-msg ;
is ev-parse-definition-structure

\ Treats actual definition opener/terminator surface words as reserved names.
: ev-definition-boundary-name? { name ss -- flag }
  name ss ev-ss-word@ dup 0= if drop false exit then { spec }
  spec ev-spec.define-mode + @ ev-define.colon = if true exit then
  spec ev-spec-is-control? if
    spec ev-spec.control-mode + @ s" END" ev-key= if true exit then
  then
  false ;

\ Reads the next user-defined word name after a defining word.
: ev-next-defined-name { sc defining-token ss -- name }
  sc ev-next-prog-word dup 0= if
    s" Missing word name after " ev-scopy defining-token ev-word-text@ ev-scat2
    0 defining-token ev-word-span@ ev-error-msg
  then { name }
  name ev-word-text@ ev-slen@ 0= if
    s" Empty word name after " ev-scopy defining-token ev-word-text@ ev-scat2
    0 name ev-word-span@ ev-error-msg
  then
  name ev-word-text@ ss ev-definition-boundary-name? if
    s" Illegal word name " ev-scopy name ev-word-text@ ev-scat2
    0 name ev-word-span@ ev-error-msg
  then
  name ;

\ Builds a one-input runtime effect for a concrete type name.
: ev-type-input-spec { type -- spec }
  4 ev-vec-new { left }
  4 ev-vec-new { right }
  type 0 false ev-sym-new left ev-vec-push
  left right ev-spec-new dup ev-spec-max-pos drop ;

\ Builds a zero-input runtime effect that produces one concrete type.
: ev-type-output-spec { type -- spec }
  4 ev-vec-new { left }
  4 ev-vec-new { right }
  type 0 false ev-sym-new right ev-vec-push
  left right ev-spec-new dup ev-spec-max-pos drop ;

\ Adds a hidden bookkeeping effect to the top-level program sequence.
: ev-prog-add-hidden { label span spec prog -- }
  ev-sempty prog ev-prog.words + @ ev-vec-push
  span prog ev-prog.spans + @ ev-vec-push
  spec span label ev-spec-with-origin prog ev-prog.specs + @ ev-vec-push ;

: ev-prog-discard-last { prog -- }
  prog ev-prog.words + @ ev-vec-remove-last
  prog ev-prog.spans + @ ev-vec-remove-last
  prog ev-prog.specs + @ ev-vec-remove-last ;

\ Handles ':' at top level: read the new word name, compile its body, then register the result.
: ev-parse-definition { token spec sc ts ss -- }
  spec ev-spec-left-count 0<> spec ev-spec-right-count 0<> or if
    s" Colon definition word must have stack effect ( -- )" ev-scopy 0 token ev-word-span@ ev-error-msg
  then
  sc token ss ev-next-defined-name { name }
  s" END" ev-scopy { end-role }
  token ev-word-text@ drop
  name ev-word-text@ sc ts ss 0 end-role ['] ev-parse-definition-seq catch dup if
    { code }
    drop drop drop drop drop drop
    code ev-error# = if
      ev-report-current-diagnostic
      ev-current-program-token @ { badtok }
      badtok dup if badtok ev-word-text@ ss ev-ss-word@ else 0 then { badspec }
      sc badtok badspec ss ev-recover-definition
      exit
    then
    code throw
  then
  drop { defspec }
  name ev-word-text@ defspec ss ev-ss-set-word
  name ev-word-text@ defspec ev-log-definition ;

\ Handles top-level CONSTANT-like words by consuming one runtime value and defining a zero-argument word.
: ev-parse-top-level-constant { token spec sc ts ss prog -- }
  sc token ss ev-next-defined-name { name }
  token ev-word-text@ ev-sspace ev-scat2 name ev-word-text@ ev-scat2 { opname }
  token ev-word-span@ name ev-word-span@ ev-span-cover { defspan }
  spec ev-spec-left-count 1 <> spec ev-spec-right-count 0<> or if
    token ev-word-text@ ev-sspace ev-scat2
    s" must have defining shape ( x -- )" ev-scopy ev-scat2
    0 defspan ev-error-msg
  then
  prog ev-prog.specs + @ s" top-level program" ev-scopy ts ev-seq-evaluate { prefix }
  prefix ev-spec.right + @ { right }
  right ev-vec-count@ 0= if
    opname ev-sspace ev-scat2
    s" requires one value on the stack" ev-scopy ev-scat2
    0 defspan ev-error-msg
  then
  right ev-vec-last@ { top }
  0 spec ev-spec.left + @ ev-vec@ { expected }
  top ev-sym.type + @ expected ev-sym.type + @ ts ev-ts-relation 0= if
    opname ev-sspace ev-scat2
    s" expects a value comparable with " ev-scopy ev-scat2
    expected ev-sym.type + @ ev-scat2
    s" but the current stack provides " ev-scopy ev-scat2
    top ev-sym.type + @ ev-scat2
    0 defspan ev-error-msg
  then
  top ev-sym.type + @ ev-type-output-spec { constspec }
  constspec name ev-word-span@ name ev-word-text@ ev-spec-with-origin drop
  name ev-word-text@ constspec ss ev-ss-set-word
  name ev-word-text@ constspec ev-log-definition
  top ev-sym.type + @ ev-type-input-spec
  opname defspan rot prog ev-prog-add-hidden ;

\ Handles top-level VARIABLE-like words by defining a zero-input runtime word.
: ev-parse-top-level-variable { token spec sc ts ss -- }
  sc token ss ev-next-defined-name { name }
  token ev-word-span@ name ev-word-span@ ev-span-cover { defspan }
  spec ev-spec-left-count 0<> spec ev-spec-right-count 1 <> or if
    token ev-word-text@ ev-sspace ev-scat2
    s" must have defining shape ( -- y )" ev-scopy ev-scat2
    0 defspan ev-error-msg
  then
  spec ev-runtime-clone { varspec }
  varspec name ev-word-span@ name ev-word-text@ ev-spec-with-origin drop
  name ev-word-text@ varspec ss ev-ss-set-word
  name ev-word-text@ varspec ev-log-definition ;

: ev-prog-current-effect { prog ts -- spec }
  prog ev-prog.specs + @ s" top-level program" ev-scopy ts ev-seq-evaluate ;

: ev-prog-add-checked-word { word span spec prog ts -- }
  word span spec prog ev-prog-add-word
  prog ts ['] ev-prog-current-effect catch dup if
    { code }
    prog ev-prog-discard-last
    code ev-error# = if
      ev-report-current-diagnostic
      exit
    then
    code throw
  then
  drop drop ;

: ev-prog-words>sptr { prog -- s }
  ev-sempty { out }
  prog ev-prog.words + @ { words }
  words ev-vec-count@ 0 ?do
    out i words ev-vec@ ev-scat2 ev-sspace ev-scat2 to out
  loop
  out ;

: ev-annotate. { prog final -- }
  ." > " final ev-spec.left + @ ev-sym-vec>sptr ev-s.
  cr
  prog ev-prog.words + @ { words }
  prog ev-prog.specs + @ { specs }
  words ev-vec-count@ 0 ?do
    ."     "
    i words ev-vec@ ev-s.
    ." 	"
    i specs ev-vec@ ev-spec>sptr ev-s.
    cr
  loop
  ." < " final ev-spec.right + @ ev-sym-vec>sptr ev-s.
  cr ;

: ev-parse-program-token { tok spec sc ts ss prog -- }
  spec if
    spec ev-spec-allowed-interpret? 0= if
      s" Word not supported in interpretation state" ev-scopy 0 tok ev-word-span@ ev-error-msg
    then
    spec ev-spec-is-immediate? if
      spec ev-spec-defines-word? if
        spec ev-spec.define-mode + @ { mode }
        mode ev-define.colon = if
          tok spec sc ts ss ev-parse-definition
        else mode ev-define.constant = if
          tok spec sc ts ss prog ev-parse-top-level-constant
        else mode ev-define.variable = if
          tok spec sc ts ss ev-parse-top-level-variable
        else
          s" Unsupported top-level defining word" ev-scopy 0 tok ev-word-span@ ev-error-msg
        then then then
      else spec ev-spec-is-control? if
        s" Unexpected control word in top-level program" ev-scopy 0 tok ev-word-span@ ev-error-msg
      else
        tok spec sc ev-consume-parser-input { span }
        tok ev-word-text@ span spec ev-runtime-clone prog ts ev-prog-add-checked-word
      then then
    else
      tok 0 ts ss ev-resolve-runtime-spec { rspec }
      tok ev-word-text@ tok ev-word-span@ rspec prog ts ev-prog-add-checked-word
    then
  else
    tok 0 ts ss ev-resolve-runtime-spec { rspec }
    tok ev-word-text@ tok ev-word-span@ rspec prog ts ev-prog-add-checked-word
  then ;

\ Outer interpreter for program text: execute top-level defining words immediately and collect runtime effects.
: ev-parse-program { name text ts ss -- prog }
  name text ev-sc-new { sc }
  sc ev-sc.lines + @ ev-current-source-lines !
  name text sc ev-sc.lines + @ ev-prog-new { prog }
  begin
    sc ev-next-prog-word dup
  while
    { tok }
    tok ev-word-text@ ss ev-ss-word@ { spec }
    tok spec sc ts ss prog ['] ev-parse-program-token catch dup if
      { code }
      drop drop drop drop drop drop
      code ev-error# = if
        ev-report-current-diagnostic
        sc tok spec ss ev-recover-top-level
      else
        code throw
      then
    else
      drop
    then
  repeat
  drop
  prog ;

\ ----------------------------------------------------------------------
\ Native CLI entrypoint

0 cells constant ev-cfg.types
1 cells constant ev-cfg.specs
2 cells constant ev-cfg.prog
3 cells constant ev-cfg.words
4 cells constant /ev-cfg

: ev-log-path { cfg -- path }
  cfg ev-cfg.prog + @ dup if
    s" .log" ev-scopy ev-scat2
  else
    drop
    s" command-line.log" ev-scopy
  then ;

: ev-log-open { cfg -- }
  cfg ev-log-path { path }
  path ev-s@ w/o create-file { fileid ior }
  ior if
    s" Unable to create log file " ev-scopy path ev-scat2
    0 0 ev-error-msg
  then
  fileid ev-log-fileid ! ;

: ev-cfg-new ( -- cfg )
  /ev-cfg ev-xalloc { cfg }
  0 cfg ev-cfg.types + !
  0 cfg ev-cfg.specs + !
  0 cfg ev-cfg.prog + !
  8 ev-vec-new cfg ev-cfg.words + !
  cfg ;

: ev-args-usage ( -- s )
  s" Usage: gforth gforth-evaluator.fs --types TYPES --specs SPECS [--prog PROGRAM] [word ...]" ev-scopy ;

: ev-args-words>sptr { vec -- s }
  ev-sempty { out }
  vec ev-vec-count@ 0 ?do
    out i vec ev-vec@ ev-scat2 ev-sspace ev-scat2 to out
  loop
  out ;

\ Parses the gforth command line into explicit types/specs/program inputs.
: ev-parse-args ( -- cfg )
  ev-cfg-new { cfg }
  1 { i }
  begin
    i argc @ <
  while
    i arg ev-scopy { a }
    a s" --HELP" ev-key= a s" -H" ev-key= or if
      ev-args-usage 0 0 ev-error-msg
    then
    a s" --TYPES" ev-key= if
      i 1+ argc @ >= if s" Missing file name after --types" ev-scopy 0 0 ev-error-msg then
      i 1+ arg ev-scopy cfg ev-cfg.types + !
      i 2 + to i
    else a s" --SPECS" ev-key= if
      i 1+ argc @ >= if s" Missing file name after --specs" ev-scopy 0 0 ev-error-msg then
      i 1+ arg ev-scopy cfg ev-cfg.specs + !
      i 2 + to i
    else a s" --PROG" ev-key= if
      i 1+ argc @ >= if s" Missing file name after --prog" ev-scopy 0 0 ev-error-msg then
      i 1+ arg ev-scopy cfg ev-cfg.prog + !
      i 2 + to i
    else
      a cfg ev-cfg.words + @ ev-vec-push
      i 1+ to i
    then then then
  repeat
  cfg ev-cfg.types + @ 0= if
    s" Missing required --types file. " ev-scopy ev-args-usage ev-scat2 0 0 ev-error-msg
  then
  cfg ev-cfg.specs + @ 0= if
    s" Missing required --specs file. " ev-scopy ev-args-usage ev-scat2 0 0 ev-error-msg
  then
  cfg ev-cfg.prog + @ 0= cfg ev-cfg.words + @ ev-vec-count@ 0= and if
    s" Missing program source. " ev-scopy ev-args-usage ev-scat2 0 0 ev-error-msg
  then
  cfg ;

\ Native CLI entrypoint: load the files, parse the program, evaluate it, and print the annotation.
: ev-run-native ( -- )
  0 ev-current-diagnostic !
  0 ev-diagnostic-count !
  0 ev-current-program-token !
  ev-no-fileid ev-log-fileid !
  ev-parse-args { cfg }
  cfg ev-log-open
  ." Types file: " cfg ev-cfg.types + @ ev-s. cr
  ." Specs file: " cfg ev-cfg.specs + @ ev-s. cr
  cfg ev-cfg.words + @ ev-vec-count@ 0> if
    ." Program source: command line" cr
  else
    ." Program file: " cfg ev-cfg.prog + @ ev-s. cr
  then
  cfg ev-cfg.types + @ ev-ts-load { ts }
  cfg ev-cfg.specs + @ ts ev-ss-load { ss }
  cfg ev-cfg.words + @ ev-vec-count@ 0> if
    s" <command line>" ev-scopy
    cfg ev-cfg.words + @ ev-args-words>sptr
  else
    cfg ev-cfg.prog + @ dup ev-s@ ev-file>sptr
  then
  ts ss ev-parse-program { prog }
  ev-diagnostic-count @ 0> if
    ev-reported-error# throw
  then
  prog ts ev-prog-current-effect { final }
  ." Program text:" cr
  prog ev-prog.text + @ ev-s. cr
  ." Program: " prog ev-prog-words>sptr ev-s. cr
  prog final ev-annotate.
  ev-log-close ;

: ev-main ( -- code )
  ['] ev-run-native catch dup if
    { code }
    ev-log-close
    code ev-reported-error# = if
      1
      exit
    then
    ev-current-diagnostic @ dup if
      drop
      ev-report-current-diagnostic
    else
      code throw
    then
    1
  else
    0
  then ;

ev-main (bye)
