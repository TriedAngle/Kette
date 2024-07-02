pub const PRELOAD: &str = r#"
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

: when ( ? q -- ) swap [ call ] [ drop ] if ;
: unless ( ? q -- ) swap [ drop ] [ call ] if ;


@: \ @vm-next-token @vm-link-token >box ;

: set-word-body ( word body -- ) swap 1 set-slot ;

: define-push-word ( push word -- )  1 swap <array> array>quotation set-word-body ;

@: ?: @vm-next-token @vm-define-empty-global-word dup >box define-push-word t ;


@: !/ \ !/ @vm-skip-until drop t ;

?: }

@: { \ } @vm-parse-until ;

@: $[ \ ] @vm-parse-until array>quotation call ;


: 2dup ( x y -- x y x y ) dup [ dupd swap ] dip ;
: 2dip ( x y q -- x y ) swap [ dip ] dip ;
: 2keep ( x y q -- x y ) [ 2dup ] dip 2dip ;

: rotd ( x y z w -- y z a w ) [ rot ] dip ;
: -rotd ( x y z w -- z x y w ) [ -rot ] dip ;

: 2drop ( x y -- ) drop drop ;
: 3drop ( x y z -- ) drop drop drop ;
: 4drop ( x y z w -- ) drop drop drop drop ;

: 2swap ( x y z w -- z w x y ) -rotd -rot ;
: over ( x b -- x y z ) dupd swap ;
: pick ( x y z -- x y z x ) [ dup ] 2dip rot ;

: 3dup ( x y z --  x y z x y z ) 2dup [ pick ] 2dip ;
: 3dip ( x y z q -- y y z ) swap [ 2dip ] dip ;
: 3keep ( x y z q -- x y z ) [ 3dup ] dip 3dip ;


: bi ( x p q -- ) [ keep ] dip call ;
: bi* ( x y p q -- ) [ dip ] dip call ;
: bi@ ( x y p -- ) dup bi* ;

: loop ( ..a q -- ..a ) [ call ] keep swap [ loop ] when ;

: while ( ..a cond body -- ..a ) 
    [ [ call ] keep ] dip rot 
    [ [ dropd call ] 2keep while ] [ 2drop ] if ;

: ^object ( ptr -- obj ) 0 slot ;

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
: 1array ( x -- arr ) 1 f <array> [ (1array) ] keep ;
: 2array ( x y -- arr ) 2 f <array> [ (2array) ] keep ;
: 3array ( x y z -- arr ) 3 f <array> [ (3array) ] keep ;
: 4array ( x y z w -- arr ) 4 f <array> [ (4array) ] keep ;

!/ word | token !/
@: ():  @vm-next-token [ @vm-define-empty-global-word ] keep \ ; @vm-skip-until @vm-define-tuple 1 swap <array> array>quotation set-word-body t ;



!/ src dst ss sd l c - src dst ss sd l - src dst ss+ sd+ - src dst !/
: array-copy ( src dst start-src start-dst count -- ) 
    0 swap [ 2dup < ] [ [ 1 + ] dip ] [ [ [
        [ + ] bi@-curry 2dupd swapd 
        [ swap array-nth ] [ swap set-array-nth ] bi-curry
    ] 3keep ] dip ] while* 4drop drop drop ;

!/ this is very inefficient, use vectors if this is your normal usecase !/
: array-push ( obj arr -- arr ) 
    dup array-size dup 1 + f <array> [ swap [ 0 0 ] dip array-copy ] keep [ [ array-size 1 - ] [ set-array-nth ] bi ] keep ;

: curry-inplace ( obj quot -- ) ;


"#;

const _TEST: &str = r#"

"#;
