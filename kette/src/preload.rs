pub const PRELOAD: &str = r#"

@: \ @vm-next-token @vm-link-token >box ;


: set-word-body ( word body -- ) swap 1 set-slot ;

@: ?: @vm-next-token @vm-define-empty-global-word dup >box 1 swap <array> array>quotation set-word-body t ;

@: !/ \ !/ @vm-parse-until drop t ;

!/  Hello this is a comment looool   !/
: + ( a b -- c ) fixnum+ ;
: - ( a b -- c ) fixnum- ;
: . ( a -- ) fixnum. ;
: / ( a -- ) fixnum/ ;
: = ( a b -- ? ) fixnum= ;
: % ( a b -- c ) fixnum% ;
: > ( a b -- ? ) fixnum> ;
: >= ( a b -- ? ) fixnum>= ;
: < ( a b -- ? ) fixnum> ;
: <= ( a b -- ? ) fixnum<= ;

: 2dup ( x y -- x y x y ) dup [ dupd swap ] dip ;
: 2dip ( x y q -- x y ) swap [ dip ] dip ;
: 2keep ( x y q -- x y ) [ 2dup ] dip 2dip ;

: rotd ( x y z w -- y z a w ) [ rot ] dip ;
: -rotd ( x y z w -- z x y w ) [ -rot ] dip ;

: 2drop ( x y -- ) drop drop ;

: 2swap ( x y z w -- z w x y ) -rotd -rot ;
: over ( x b -- x y z ) dupd swap ;
: pick ( x y z -- x y z x ) [ dup ] 2dip rot ;

: 3dup ( x y z --  x y z x y z ) 2dup [ pick ] 2dip ;
: 3dip ( x y z q -- y y z ) swap [ 2dip ] dip ;
: 3keep ( x y z q -- x y z ) [ 3dup ] dip 3dip ;

: bi ( x p q -- ) [ keep ] dip call ;
: bi* ( x y p q -- ) [ dip ] dip call ;
: bi@ ( x y p -- ) dup bi* ;

: array-size ( arr -- n ) 0 slot ;
: array-nth ( n array -- val ) swap 1 + slot ;
: set-array-nth ( val n array -- ) swap 1 + set-slot ;
: 1array ( x -- arr ) 1 swap <array> ;
: 2array ( x y -- arr ) 2 f <array> [ [ ] dip array-set-nth ] [ 2 ] bi* ;


: array-copy ( src dst start-src start-dst count -- ) 
    [ 0 ] dip [ <= ] [
        
        [ 1 - ] dip
    ] while ;

: array-push-front ( obj arr -- arr ) dup array-size 1 + swap @vm-array-resize  ;

: array-push-end ( obj arr -- arr ) ;

: curry-inplace ( obj quot -- ) ;






: ^object ( ptr -- obj ) 0 slot ;

: when ( ? q -- ) swap [ call ] [ drop ] if ;
: unless ( ? q -- ) swap [ drop ] [ call ] if ;

: loop ( ..a q -- ..a ) [ call ] keep swap [ loop ] when ;

: while ( ... cond body -- ... ) [ [ call ] keep ] dip rot 
    [ [ dropd call ] 2keep while ] [ 2drop ] if ;





"#;
