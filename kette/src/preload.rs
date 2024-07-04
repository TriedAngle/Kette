pub const PRELOAD: &str = r#"
@: \ @vm-next-token @vm-link-token >box ;

@: !/ \ !/ @vm-skip-until drop t ;

: set-word-body ( word body -- ) swap 1 set-slot ;

: define-push-word ( word value -- )  1 swap <array> array>quotation set-word-body ;

@: ?: @vm-next-token @vm-define-empty-global-word dup >box define-push-word t ;

?: }

@: { \ } @vm-parse-until ;

@: $[ \ ] @vm-parse-until array>quotation call ;



: . ( a -- ) fixnum. ;
: neg ( a -- ) fixnum-neg ;
: + ( a b -- c ) fixnum+ ;
: - ( a b -- c ) fixnum- ;
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


: when ( ? q -- ) swap [ call ] [ drop ] if ;
: unless ( ? q -- ) swap [ drop ] [ call ] if ;


: 2dup ( x y -- x y x y ) dup [ dupd swap ] dip ;
: 2dip ( x y q -- x y ) swap [ dip ] dip ;
: 2keep ( x y q -- x y ) [ 2dup ] dip 2dip ;

: rotd ( x y z w -- y z a w ) [ rot ] dip ;
: -rotd ( x y z w -- z x y w ) [ -rot ] dip ;

: 2drop ( x y -- ) drop drop ;
: 3drop ( x y z -- ) drop drop drop ;
: 4drop ( x y z w -- ) drop drop drop drop ;

: 2dropd ( x y z -- z ) dropd dropd ;

: 2swap ( x y z w -- z w x y ) -rotd -rot ;
: over ( x b -- x y z ) dupd swap ;
: pick ( x y z -- x y z x ) [ dup ] 2dip rot ;
: pickd ( x y z w -- x y z x w ) [ pick ] dip ;

: 3dup ( x y z --  x y z x y z ) 2dup [ pick ] 2dip ;
: 3dip ( x y z q -- y y z ) swap [ 2dip ] dip ;
: 3keep ( x y z q -- x y z ) [ 3dup ] dip 3dip ;


: bi ( x p q -- ) [ keep ] dip call ;
: bi* ( x y p q -- ) [ dip ] dip call ;
: bi@ ( x y p -- ) dup bi* ;

: loop ( ..a q -- ..a ) [ call ] keep swap [ loop ] [ drop ] if ;

: while ( ..a cond body -- ..a ) 
    [ [ call ] keep ] dip rot 
    [ [ dropd call ] 2keep while ] [ 2drop ] if ;

: bi-curry ( x y a b p q  -- ) -rotd [ call ] 3dip call ; 
: bi*-curry ( x y w p q -- ) [ dup swapd ] 2dip -rotd [ call ] 3dip call ;
: bi@-curry ( x y w p -- ) dup bi*-curry ;

: 2dupd ( x y z w -- x y x y z w ) [ 2dup ] 2dip ;

: tri ( x p q r -- ) [ [ keep ] dip keep ] dip call ;
: tri* ( x y z p q r -- ) [ [ 2dip ] dip dip ] dip call ;
: tri@ ( x y z p -- ) dup dup tri* ;

: while* ( ..a cond do-after body -- ..a )
    [ [ call ] keep swap ] 2dip rot
    [ [ -rot [ [ call ] keep ] 2dip ] [ ] if rot ] keep
    [ swapd [ [ call ] keep ] 2dip swapd while* ] [ 3drop ] if ;

: array-size ( arr -- n ) 0 slot ;
: array-nth ( n array -- val ) swap 1 + slot ;
: set-array-nth ( val n array -- ) swap 1 + set-slot ;

: (1array) ( x arr -- arr ) [ 0 swap set-array-nth ] keep ;
: (2array) ( x y arr -- arr ) [ 1 swap set-array-nth ] keep (1array)  ;
: (3array) ( x y z arr -- arr ) [ 2 swap set-array-nth ] keep (2array)  ;
: (4array) ( x y z w arr -- arr ) [ 3 swap set-array-nth ] keep (3array) ;
: 1array ( x -- arr ) 1 f <array> (1array) ;
: 2array ( x y -- arr ) 2 f <array> (2array) ;
: 3array ( x y z -- arr ) 3 f <array> (3array) ;
: 4array ( x y z w -- arr ) 4 f <array> (4array)  ;

: 1th ( seq -- val ) 0 swap array-nth ;
: 2th ( seq -- val ) 1 swap array-nth ;
: 3th ( seq -- val ) 2 swap array-nth ;

@: tuple: @vm-next-token [ @vm-define-empty-global-word ] keep \ ; @vm-skip-until @vm-define-tuple 1 swap <array> array>quotation set-word-body t ;


: eq? ( x y -- ? ) [ object^ ] bi@ fixnum= ;

: special-object ( id -- object ) 8 fixnum* let-me-cook 1 slot swap fixnum+ get^ ^object ;


: primitive? ( word -- ? ) 4 slot 1 fixnum= ;
: syntax? ( word -- ? ) 3 slot 1 fixnum= ;


: execute-if-syntax ( word -- res ) 
    dup syntax? 
    [ dup primitive? [
        [ call-primitive ] keep
        \ [ unbox eq? [ 1 swap <array> array>quotation ] unless 
    ] [ 1 slot call ] if ] 
    [ drop f ] if ;

@: const: 
    @vm-next-token @vm-define-empty-global-word @vm-next-token 
    dup @vm-try-parse-num dup [ dropd 1 swap <array> array>quotation set-word-body ] [ 
        drop @vm-link-token dup [ execute-if-syntax  set-word-body ] [ drop f ] if 
    ] if
    t ;


: array-copy ( src dst start-src start-dst count -- ) 
    0 swap [ 2dup < ] [ [ 1 + ] dip ] [ [ [
        [ + ] bi@-curry 2dupd swapd 
        [ swap array-nth ] [ swap set-array-nth ] bi-curry
    ] 3keep ] dip ] while* 4drop drop drop ;

!/ this is very inefficient, use vectors if this is your normal usecase !/
: array-push ( obj arr -- arr ) 
    dup array-size dup 1 + f <array> [ swap [ 0 0 ] dip array-copy ] keep [ [ array-size 1 - ] [ set-array-nth ] bi ] keep ;

!/ this is very inefficient, use vectors if this is your normal usecase !/
: array-push-front ( obj arr -- arr ) 
    dup array-size dup 1 + f <array> [ swap [ 0 1 ] dip array-copy ] keep [ 0 swap set-array-nth ] keep ;


: curry ( obj quot -- curried ) [ 0 slot array-push-front ] keep [ 0 set-slot ] keep ;


tuple: array-iter array start stop ;

: <array-iter> ( array -- self ) dup array-size 0 swap array-iter tuple-boa ;

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



tuple: vector len underlying ;

: <vector> ( size -- vector ) f <array> 0 swap vector tuple-boa ;

: set-at ( obj n vector -- ) 1 slot set-array-nth ;

: vector-grow ( vector -- ) s" resize" utf8.
    dup 1 slot dup array-size dup 2 fixnum* 
    f <array> [ swap [ 0 0 ] dip array-copy ] keep swap 1 set-slot ; 

: vector-push ( obj vector -- ) 
    dup [ 0 slot ] [ 1 slot 0 slot ] bi < [ dup vector-grow ] unless 
    dup [ 0 slot ] [ [ 0 slot 1 + ] keep 0 set-slot ] bi swap set-at ;

"#;

const _TEST: &str = r#"

"#;
