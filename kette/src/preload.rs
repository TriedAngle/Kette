pub const PRELOAD: &str = r#"
@: \ @vm-next-token @vm-link-word >box ;

@: \\ @vm-next-token @vm-link-word t ;

@: !/ \ !/ @vm-skip-until drop t ;

: set-word-body ( word body -- ) swap 1 set-slot ;

: define-push-word ( word value -- )  1 swap <array> array>quotation set-word-body ;

@: ?: @vm-next-token @vm-define-empty-global-word dup >box define-push-word t ;

?: }
?: )
?: ;
?: ]

@: { \ } @vm-parse-until ;

@: $[ \ ] @vm-parse-until array>quotation (call) ;

: @stack. ( -- ) @vm-stack array. ;


: . ( a -- ) fixnum. ;
: neg ( a -- ) fixnum-neg ;
: + ( a b -- c ) fixnum+ ;
: - ( a b -- c ) fixnum- ;
: * ( a b -- c ) fixnum* ;
: / ( a -- ) fixnum/ ;
: = ( a b -- ? ) fixnum= ;
: % ( a b -- c ) fixnum% ;
: > ( a b -- ? ) fixnum> ;
: >= ( a b -- ? ) fixnum>= ;
: < ( a b -- ? ) fixnum< ;
: <= ( a b -- ? ) fixnum<= ;

: +1 ( a -- n+1 ) 1 + ;
: -1 ( a -- n-1 ) 1 - ;
: n| ( a n -- ? ) % 0 = ;
: !n| ( a n -- ? ) n| not ;


: when ( ? q -- ) swap [ (call) ] [ drop ] if ;
: unless ( ? q -- ) swap [ drop ] [ (call) ] if ;


: 2dup ( x y -- x y x y ) dup [ dupd swap ] dip ;
: 2dip ( x y q -- x y ) swap [ dip ] dip ;
: 2keep ( x y q -- x y ) [ 2dup ] dip 2dip ;

: rotd ( x y z w -- y z a w ) [ rot ] dip ;
: -rotd ( x y z w -- z x y w ) [ -rot ] dip ;

: 2drop ( x y -- ) drop drop ;
: 3drop ( x y z -- ) 2drop drop ;
: 4drop ( x y z w -- ) 3drop drop ;

: 2dropd ( x y z -- z ) dropd dropd ;
: 3dropd ( x y z -- z ) 2dropd dropd ;

: 2swap ( x y z w -- z w x y ) -rotd -rot ;
: over ( x b -- x y z ) dupd swap ;
: pick ( x y z -- x y z x ) [ dup ] 2dip rot ;
: pickd ( x y z w -- x y z x w ) [ pick ] dip ;

: 3dup ( x y z --  x y z x y z ) 2dup [ pick ] 2dip ;
: 3dip ( x y z q -- y y z ) swap [ 2dip ] dip ;
: 3keep ( x y z q -- x y z ) [ 3dup ] dip 3dip ;

: 4dup ( x y z w -- x y z w x y z w ) 3dup [ pickd swap ] 3dip ;
: 4dip ( w x y z q -- w x y z ) swap [ 3dip ] dip ;
: 4keep ( x y z w q -- x y z w ) [ 4dup ] dip 4dip ;

: spin ( x y z -- z y x ) -rot swap ;

: bi ( x p q -- ) [ keep ] dip (call) ;
: bi* ( x y p q -- ) [ dip ] dip (call) ;
: bi@ ( x y p -- ) dup bi* ;

: loop ( ..a q -- ..a ) [ (call) ] keep swap [ loop ] [ drop ] if ;

: while ( ..a cond body -- ..a ) 
    [ [ (call) ] keep ] dip rot 
    [ [ dropd (call) ] 2keep while ] [ 2drop ] if ;

: bi-curry ( x y a b p q  -- ) -rotd [ (call) ] 3dip (call) ; 
: bi*-curry ( x y w p q -- ) [ dup swapd ] 2dip -rotd [ (call) ] 3dip (call) ;
: bi@-curry ( x y w p -- ) dup bi*-curry ;

: 2bi ( x y p q -- ) [ 2keep ] dip (call) ;
: 3bi ( x y z p q -- ) [ 3keep ] dip (call) ;

: 2dupd ( x y z w -- x y x y z w ) [ 2dup ] 2dip ;

: tri ( x p q r -- ) [ [ keep ] dip keep ] dip (call) ;
: tri* ( x y z p q r -- ) [ [ 2dip ] dip dip ] dip (call) ;
: tri@ ( x y z p -- ) dup dup tri* ;

: while* ( ..a cond do-after body -- ..a )
    [ [ (call) ] keep swap ] 2dip rot
    [ [ -rot [ [ (call) ] keep ] 2dip ] [ ] if rot ] keep
    [ swapd [ [ (call) ] keep ] 2dip swapd while* ] [ 3drop ] if ;

: array-size ( arr -- n ) 0 slot ;
: array-nth ( n array -- val ) swap 1 + slot ;
: set-array-nth ( val n array -- ) swap 1 + set-slot ;

: (1array) ( x arr -- arr ) [ 0 swap set-array-nth ] keep ;
: (2array) ( x y arr -- arr ) [ 1 swap set-array-nth ] keep (1array)  ;
: (3array) ( x y z arr -- arr ) [ 2 swap set-array-nth ] keep (2array)  ;
: (4array) ( x y z w arr -- arr ) [ 3 swap set-array-nth ] keep (3array) ;
: (5array) ( x y z w v arr -- arr ) [ 4 swap set-array-nth ] keep (4array) ;
: 1array ( x -- arr ) 1 f <array> (1array) ;
: 2array ( x y -- arr ) 2 f <array> (2array) ;
: 3array ( x y z -- arr ) 3 f <array> (3array) ;
: 4array ( x y z w -- arr ) 4 f <array> (4array)  ;
: 5array ( x y z w v -- arr ) 5 f <array> (5array)  ;

: 1th ( seq -- val ) 0 swap array-nth ;
: 2th ( seq -- val ) 1 swap array-nth ;
: 3th ( seq -- val ) 2 swap array-nth ;

: array-copy ( src dst start-src start-dst count -- ) 
    0 swap [ 2dup fixnum< ] [ [ 1 fixnum+ ] dip ] [ [ [
        [ fixnum+ ] bi@-curry 2dupd swapd 
        [ swap array-nth ] [ swap set-array-nth ] bi-curry
    ] 3keep ] dip ] while* 4drop drop drop ;

!/ this is very inefficient, use vectors if this is your normal usecase !/
: array-push ( obj arr -- arr ) 
    dup array-size dup 1 fixnum+ f <array> 
    [ swap [ 0 0 ] dip array-copy ] keep [ [ array-size 1 - ] [ set-array-nth ] bi ] keep ;

!/ this is very inefficient, use vectors if this is your normal usecase !/
: array-push-front ( obj arr -- arr ) 
    dup array-size dup 1 + f <array> [ swap [ 0 1 ] dip array-copy ] keep [ 0 swap set-array-nth ] keep ;

: ref-eq? ( x y -- ? ) [ object^ ] bi@ fixnum= ;

: special-object ( id -- object ) 8 fixnum* let-me-cook 1 slot swap fixnum+ get^ ^object ;

: primitive? ( word -- ? ) 4 slot 1 fixnum= ;
: syntax? ( word -- ? ) 3 slot 1 fixnum= ;

: execute-if-syntax ( word -- res ) 
    dup syntax? 
    [ dup primitive? [
        [ (call-primitive) ] keep
        \ [ unbox ref-eq? [ 1 swap <array> array>quotation ] unless 
    ] [ 1 slot (call) ] if ] 
    [ drop f ] if ;

@: !: 
    @vm-next-token @vm-define-empty-global-word @vm-next-token 
    dup @vm-?number dup [ dropd 1 swap <array> array>quotation set-word-body ] [ 
        drop @vm-link-word dup [ execute-if-syntax  set-word-body ] [ drop f ] if 
    ] if t ;


!: SLOT-CONSTANT 0
!: SLOT_PARENT 1
!: SLOT_DATA 2
!: SLOT_ASSIGNMENT 3
!: SLOT_METHOD 4
!: SLOT_VARIABLE_DATA: 5
!: SLOT_EMBEDDED_DATA: 6

: map>> ( obj -- map ) 1 neg slot ;
: slots>> ( map -- slots ) 3 slot ;

: find-slot ( name slots count -- slot/f ) 
    1 - dup 0 > [ 
        [ swap array-nth dup 0 slot pick bytearray= ] 2keep
        2swap [ 3dropd ] [ drop find-slot ] if
    ] [ 3drop f ] if ;

: find-slot-in-map-by-name ( name map -- slot/f ) [ slots>> ] [ 2 slot ] bi find-slot ;

: find-slot-in-map ( word map -- slot/f ) [ 0 slot ] dip find-slot-in-map-by-name ;

: find-self ( word obj -- slot/f ) map>> find-slot-in-map ;


: send-self ( ..a obj boxed-word -- ..b ) unbox dupd swap find-self 2 slot 1 slot (call) ;

: push-map-slot ( slot map -- ) 
    [ 3 slot array-push ] [ 3 set-slot ] [ [ 2 slot 1 fixnum+ ] [ 2 set-slot ] bi ] tri  ;


: create-method-slot ( name word -- slot ) 
    [ SLOT_METHOD ] dip 0 0 1 special-object @vm-new-object ;

: create-slot-slot ( name index -- slot )
    [ SLOT_DATA f ] dip 0 1 special-object @vm-new-object ;

: push-map-method ( word map -- ) 
    [ [ 0 slot ] keep create-method-slot ] dip push-map-slot ;



: define-word ( name body -- word ) 
    swap @vm-define-empty-word [ 1 set-slot ] keep ;

: create-getter-method ( name index -- word ) 
    [ s" >>" bytearray-concat ] dip \ slot unbox 2array array>quotation define-word ;

: create-setter-method ( name index -- word )
    [ s" <<" bytearray-concat ] dip \ set-slot unbox 2array array>quotation define-word ;

: create-accessor-methods ( name index -- getter setter ) 
    [ create-getter-method ] [ create-setter-method ] 2bi ;

: define-getter-word ( name -- )
    s" >>" bytearray-concat @vm-define-empty-global-word dup >box \ send-self unbox 2array array>quotation set-word-body ;

: define-setter-word ( name -- )
    s" <<" bytearray-concat @vm-define-empty-global-word dup >box \ send-self unbox 2array array>quotation set-word-body ;


!/ TODO !/
: define-change-word ( name -- ) 
    drop
;

: define-keep-set-word ( name -- ) 
    [ s" >>" swap bytearray-concat @vm-define-empty-global-word ] keep s" <<" bytearray-concat @vm-link-word
    \ over unbox swap 2array array>quotation set-word-body ;

: define-extra-accessor-words ( name -- ) 
    [ define-keep-set-word ] [ define-change-word ] bi ;

: define-accessor-words ( name -- )
    [ define-getter-word ] [ define-setter-word ] [ define-extra-accessor-words ] tri ;

: object-slot-for ( map name index ) 
    [ drop define-accessor-words ] [ create-accessor-methods ] 2bi
    rot [ push-map-method ] bi@-curry ;

: define-object-accessors ( map array count -- ) 
    1 fixnum- dup 0 fixnum>= [
        [ 2dup swap array-nth pickd rot object-slot-for 2drop ] 3keep
        define-object-accessors
    ] [ 3drop ] if ;

: define-map-word ( map -- word ) 
    [ 0 slot @vm-define-empty-global-word dup ] keep define-push-word ;

: scan-new-map ( -- map ) @vm-next-token @vm-define-map ;

: increase-map-object-slot-count ( map -- ) 
    [ [ 1 slot 1 fixnum+ ] [ 1 set-slot ] bi ] 
    [ [ 2 slot 1 fixnum+ ] [ 2 set-slot ] bi ] bi ;

: prepend-object-slot ( map name index -- ) 
    [ dup increase-map-object-slot-count ] 2dip 
    create-slot-slot swap [ 3 slot array-push-front ] keep 3 set-slot ;

: define-slots ( map array count -- ) 
    1 fixnum- dup 0 fixnum>= [
        [ [ swap array-nth dupd ] keep prepend-object-slot ] 2keep
        define-slots
    ] [ 3drop ] if ;

@: type: 
    scan-new-map [ define-map-word drop ] keep \ ; @vm-skip-until  
    dup array-size [ define-slots ] [ define-object-accessors ] 3bi t ;

@: method: 
    @vm-next-token \ ) @vm-skip-until drop @vm-define-empty-global-word dup
    >box \ unbox unbox \ over \ find-self \ dup [ unbox ] tri@ [ 2 slot 1 slot (call) ] [ drop f ] \ if unbox 5array
    array-push-front array-push-front array-push-front array>quotation set-word-body t ;

@: m: 
    @vm-next-token @vm-link-map @vm-next-token @vm-link-word \ ; @vm-parse-until array>quotation 
    [ 0 slot ] dip define-word swap push-map-method t ;

: boa ( ..slots map -- tuple ) @vm-new-object ;

@: builtin:
    @vm-next-token [ @vm-define-empty-global-word ] [ @vm-link-map ] bi
    define-push-word \ ; @vm-skip-until drop t ;

@: primitive: @vm-next-token drop \ ) @vm-skip-until drop t ;

builtin: object ... ;
builtin: fixnum < number { value i64 } ;
builtin: fixfloat < number { value f64 } ;
builtin: array { size i64 } { data ... } ;
builtin: bytearray { capacity i64 } { data ... } ;
builtin: box boxed ;

builtin: map 
    { name bytearray } 
    { object-size i64 } 
    { slot-count i64 } 
    { slots array } 
    { default-instance object } ;

!/ TODO: use t & f for boolean !/
builtin: map-slot 
    { name bytearray } 
    { kind i64 } 
    { type map }
    { index i64 } 
    { read-only? i64 } ;

builtin: quotation
    { body array }
    effect
    entry ;

!/ TODO: use t & f for boolean !/
builtin: word
    { name bytearray }
    { body quotation }
    { properties array }
    { primitive? i64 }
    { syntax? i64 } ;


!/ primitive macros: `@:` `]` `:` but they get !/ 
primitive: @vm-next-token ( -- token )
primitive: @vm-peek-next-token ( -- token )
primitive: @vm-parse-until ( wrapped-word -- array )
primitive: @vm-skip-until ( wrapped-word -- array )
primitive: @vm-link-word ( name -- word )
primitive: @vm-?number ( token -- number/? )
primitive: @vm-define-empty-global-word ( name -- word )
primitive: @vm-stack ( -- stack )
primitive: @vm-define-map ( name -- map )
primitive: @vm-clone ( obj -- clone )
primitive: @vm-new-object ( ..obj map -- obj )
primitive: >box ( value -- box )
primitive: unbox ( box -- value )

primitive: dup ( x -- x x )
primitive: dupd ( x y -- x x y )
primitive: drop ( x -- )
primitive: dropd ( x y -- y )
primitive: swap ( x y -- y x )
primitive: swapd ( x y z -- y x z )
primitive: rot ( x y z -- y z x )
primitive: -rot ( x y z -- z x y )
primitive: dip ( x q -- x )
primitive: keep ( x q -- x )
primitive: t ( -- t )
primitive: f ( -- f )
primitive: let-me-cook ( -- context )
primitive: slot ( n obj -- obj )
primitive: set-slot ( value n obj -- )
primitive: get^ ( ptr -- fixnum )
primitive: object^ ( obj -- ptr )
primitive: ^object ( fixnum -- obj ) !/ reinterpret a fixnum as an object !/
primitive: set^ ( fixnum ptr -- )
primitive: if ( ... ? true false -- ... )
primitive: and ( x y -- ? )
primitive: or ( x y -- ? )
primitive: not ( x -- ? )
primitive: array>quotation ( array -- quotation )
primitive: (call) ( ... quotation -- ... )
primitive: (call-primitive) ( ... word -- ... ) !/ TODO: make call generic over "callables" !/
primitive: <array> ( n default -- array )
primitive: <bytearray> ( n -- bytearray )
primitive: utf8. ( bytearray -- )
primitive: quotation. ( quotation --  )
primitive: array. ( array --  )
primitive: fixnum. ( a -- )

primitive: fixnum-neg ( a -- -a )
primitive: fixnum+ ( a b -- c )
primitive: fixnum- ( a b -- c )
primitive: fixnum* ( a b -- c )
primitive: fixnum/ ( a b -- c )
primitive: fixnum% ( a b -- c )
primitive: fixnum= ( a b -- ? )
primitive: fixnum< ( a b -- ? )
primitive: fixnum> ( a b -- ? )
primitive: fixnum<= ( a b -- ? )
primitive: fixnum>= ( a b -- ? )
primitive: fixnum-bitand ( a b -- c )
primitive: fixnum-bitor ( a b -- c )
primitive: fixnum-bitxor ( a b -- c )
primitive: fixnum-bitnot ( a -- b )
primitive: fixnum-bitshift-left ( a b -- c )
primitive: fixnum-bitshift-rigt ( a b -- c )

method: call ( callable -- ) 

m: quotation call (call) ;
m: word call 1 slot call ; 

type: curried obj quot ;
: curry ( obj quot -- curried ) curried boa ; 
m: curried call [ obj>> ] [ quot>> ] bi call ;

type: composed first second ;
: compose ( p q -- composed ) composed boa ;
m: composed call [ first>> call ] [ second>> call ] bi  ;


method: size ( sequence -- size )
method: length ( sequence -- size )
method: nth! ( n seuqence -- obj )
method: set-nth! ( obj n sequence -- )

method: in-bounds? ( n sequence -- ? )
method: check-bounds ( n sequence -- n sequence )
method: nth ( n sequence -- obj )
method: set-nth ( obj n sequence -- )
method: find ( q sequence -- obj/f )

m: array size array-size ;
m: array length array-size ;
m: array nth! array-nth ;
m: array set-nth! set-array-nth ;
m: array in-bounds? [ drop 0 >= ] [ size < ] 2bi and ;
m: array nth 2dup in-bounds? [ nth! ] [ 2drop f ] if ;
m: array set-nth 2dup in-bounds? [ set-nth! ] [ 3drop f ] if ;


method: push ( value sequence -- )
method: pop ( value sequence -- )

type: vector length underlying ;
: <vector> ( size -- vector ) f <array> 0 swap vector boa ;

m: vector size underlying>> size ;
m: vector length length>> ;
m: vector nth! underlying>> nth! ;
m: vector set-nth! underlying>> nth! ;
m: vector in-bounds? [ drop 0 >= ] [ length 1 < ] 2bi and ;
m: vector nth 2dup in-bounds? [ nth! ] [ 2drop f ] if ;
m: vector set-nth 2dup in-bounds? [ set-nth! ] [ 2drop f ] if ;


: vector-grow ( vector -- )
    dup [ underlying>> ] [ size dup 2 * f <array> ] bi
    [ swap [ 0 0 ] dip array-copy ] keep swap underlying<< ; 

: vector-shrink-minimum ( vector -- ) 
    dup [ underlying>> ] [ length dup ] bi f <array>
    [ swap [ 0 0 ] dip array-copy ] keep swap underlying<< ;

: vector-shrink ( vector -- ) 
    dup [ underlying>> ] [ length ] [ size 2 / f <array> ] bi
    [ swap [ 0 0 ] dip array-copy ] keep swap underlying<< ;

m: vector push
    dup [ length ] [ size ] bi < [ dup vector-grow ] unless
    [ length ] [ underlying>> set-nth! ] [ [ length 1 + ] [ length<< ] bi ] tri ;

m: vector pop
    dup [ length ] [ size 3 / ] < [ dup vector-shrink ] when
    [ length 1 - ] [ underlying>> set-nth! ] [ [ length 1 - ] [ length<< ] bi ] tri ;


: filter-apply ( element q -- ? ) call ;

: filter-step ( output element q -- ) dupd filter-apply [ swap push ] [ 2drop ] if ;

: filter-sequence ( output q sequence counter -- output ) 
    1 - dup 0 >= [
        [ filter-sequence ] 4keep  
        swap nth! swap filter-step 
    ] [ 3drop ] if ;

: filter ( sequence q -- filtered ) 
    10 <vector> spin dup length filter-sequence dup vector-shrink-minimum ;


: map-apply ( element q -- element ) call ;

: map-step ( output element q -- ) map-apply swap push ;

: map-sequence ( output q sequence counter -- output )
    1 - dup 0 >= [
        [ map-sequence ] 4keep
        swap nth! swap map-step
    ] [ 3drop ] if ;

: map ( sequence q -- mapped ) 
    10 <vector> spin dup length map-sequence dup vector-shrink-minimum ;


!/
: inherit-from-map ( map-child map-parent -- ) 
    slots>>
;

@: type: 
    scan-new-map [ define-map-word drop ] keep 
    @vm-peek-next-token s" <" bytearray= [ @vm-next-token drop 
    @vm-next-token @vm-link-map dupd inherit-from-map ] when 
    \ ; @vm-skip-until  
    dup array-size [ define-slots ] [ define-object-accessors ] 3bi t ;

!/ 



!/
type: array-iter array start stop ;

: <array-iter> ( array -- self ) dup array-size 0 swap array-iter @vm-new-object ;

: array-iter-next ( self -- next/? ) 
    dup [ 1 slot ] [ 2 slot ] bi < [ 
            [ 1 slot ] 
            [ 0 slot array-nth ] 
            [ [ 1 slot 1 + ] [ 1 set-slot ] bi ] tri 
        ] [ drop f ] if ;

: ?next ( self next/? ) array-iter-next ;

: match-step ( ..a ? array -- ..b c? ? ) 
    [ 1th ] [ 2th ] bi [ swap [ swap call ] keep ] dip swap [
        swap [ [ call ] [ drop ] if ] keep
    ] dip ;

: match-many ( ? array -- ) 
    <array-iter> [ dup array-iter-next dup ] [
        swap [ match-step dropd ] dip
    ] while 3drop ;

: match ( ? array -- )
    <array-iter> [
        dup array-iter-next dup [
            swap [ match-step ] dip rot not
        ] [ f ] if
    ] loop 2drop ;
!/





"#;

const _TEST: &str = r#"

"#;
