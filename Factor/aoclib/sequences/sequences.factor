USING: assocs kernel math sequences ;

IN: aoclib.sequences

: window2 ( seq -- seq ) dup [ but-last ] [ rest ] bi* zip ;

! { { { 1 2 } { 2 3 } { 3 4 } } } [ { 1 2 3 4 } window2 ]

! `( x -- ? )`を満たさない要素のix sequenceを返す
: !satisfies ( seq quot: ( x -- ? ) -- sequence )
   swap
   dup length <iota> ! ( quot seq iota )
   spin              ! ( iota seq quot )
   map [ [ drop -1 ] when ] 2map
   [ 0 >= ] filter
;

! { { 0 2 } } [ { 1 2 3 2 2 } [ 2 = ] !satisfies ] unit-test
! { { 0 2 4 } } [ { 1 0 3 0 2 } [ zero? ] !satisfies ] unit-test
