"
I am visualizer for AoC 2023 problems.

"
Class {
	#name : 'AoC2023',
	#superclass : 'AoCView',
	#classTraits : '{} + TraitedClass',
	#category : 'AoCVisualize',
	#package : 'AoCVisualize'
}

{ #category : 'public' }
AoC2023 class >> day20 [

   self new day20 open
]

{ #category : 'public' }
AoC2023 class >> day25 [

   self new day25 open
]

{ #category : 'initialization' }
AoC2023 >> day20 [
   "(AoC2023 day20 isNil) >>> false"

   title := 'y2023 day20'.
   update := [ self day20 ].
   graph := self day20graph: self day20load
]

{ #category : 'private - building' }
AoC2023 >> day20graph: aCollection [

   | canvas elements flipflipLineBuilder conjunctionLineBuilder |
   canvas := RSCanvas new.
   elements := aCollection keys collect: [ :name | RSEllipse new size: 5; model: name ] as: RSGroup.
   elements @ RSDraggable.
   canvas addAll: elements.
   flipflipLineBuilder := RSLineBuilder line.
   flipflipLineBuilder canvas: canvas; color: Color red; connectFromAll: [ :each |
         ((aCollection at: each) at: #type) = 'FlipFlop' ifTrue: [
               (aCollection at: each) at: #inputs ]
            ifFalse: [ {  } ] ].
   conjunctionLineBuilder := RSLineBuilder line.
   conjunctionLineBuilder canvas: canvas; color: Color blue; connectFromAll: [ :each |
         ((aCollection at: each) at: #type) = 'Conjunction' ifTrue: [
               (aCollection at: each) at: #inputs ]
            ifFalse: [ {  } ] ].
   RSTreeLayout new on: elements.
   canvas @ RSCanvasController.
   ^ SpRoassalPresenter new canvas: canvas; yourself 
]

{ #category : 'private - loading' }
AoC2023 >> day20load [

   | data nodes |
   data := (baseDirectory / 'tmp/2023/day20.json') asFileReference readStreamDo: [ :stream |
              STON fromStream: stream ].
   nodes := data inject: Dictionary new into: [ :pool :each |
               | dic name props |
               dic := IdentityDictionary new.
               name := each at: 1.
               props := each at: 2.
               dic at: #name put: (each at: 1); at: #inputs put: (props at: 'hash') keys; at:
                     #output
                  put: (props at: 'dests'); at: #type put: (props at: 'module_type').
               pool at: name put: dic; yourself ].
   ^ nodes
]

{ #category : 'initialization' }
AoC2023 >> day25 [
   "(AoC2023 day25 isNil) >>> false"

   title := 'y2023 day25'.
   update := [ self day25 ].
   graph := self day25graph: self day25load
]

{ #category : 'private - building' }
AoC2023 >> day25graph: aCollection [

   | canvas lb elements |
   canvas := RSCanvas new.
   elements := aCollection keys collect: [ :c | RSEllipse new size: 5; model: c ] as: RSGroup.
   elements @ RSDraggable.
   canvas addAll: elements.
   lb := RSLineBuilder line.
   lb canvas: canvas; color: Color red; connectFromAll: [ :each | aCollection at: each ].
   RSForceBasedLayout new on: elements.
   canvas @ RSCanvasController.
   ^ SpRoassalPresenter new canvas: canvas; yourself 
]

{ #category : 'private - loading' }
AoC2023 >> day25load [

   | data nodes |
   data := (baseDirectory / 'tmp/2023/day25.json') asFileReference readStreamDo: [ :stream |
              STON fromStream: stream ].
   nodes := data inject: Dictionary new into: [ :dic :element |
               | to |
               to := element at: 2.
               dic at: (element at: 1)
                  update: [ :set | set add: to; yourself ]
                  initial: [ Set new add: to; yourself ].
               (dic keys includes: to) ifFalse: [ dic at: to put: Set new ].
               dic ].
   ^ nodes
]
