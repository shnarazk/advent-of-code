USING: arrays kernel math math.matrices sequences splitting
;
IN: aoclib.matrices

: matrix-indices ( matrix -- sequence )
  dimension first2 [ 2array ] <matrix-by-indices> { } join
;

! { { { 0 0 }  { 0 1 } } } [ 1 2 0 <matrix> indices ] unit-test

<PRIVATE

! : 4neighbors/expander ( loc -- sequence-of-locs )
!   { { -1 0 } { 0 -1 } { 0 1 } { 1 0 } }
!   [ over [ + ] 2map ]
!   nip
! ;
!

: 8neighbors/expander ( loc -- sequence-of-locs )
  { { -1 -1 } { -1  0 } { -1  1 }
    {  0 -1 } {  0  0 } {  0  1 }
    {  1 -1 } {  1  0 } {  1  1 } }
  [ over [ + ] 2map ] map
  nip
;

: range-check ( pos limit -- ? )
  [ over 0 >= [ < ] [ drop drop f ] if ] 2map first2 and
;

PRIVATE>

! : 4neighbors ( matrix -- matrix )
!   dup
!   matrix-indices
! ;

: 8neighbors ( matrix -- matrix )
  dimension dup first2 [ 2array 8neighbors/expander ] <matrix-by-indices>
  [ [ over range-check ] filter ] matrix-map
  nip
;
