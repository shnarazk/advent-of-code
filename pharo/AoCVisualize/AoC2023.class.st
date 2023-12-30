"
I am visualizer for AoC 2023 problems.

"
Class {
	#name : 'AoC2023',
	#superclass : 'AoCView',
	#category : 'AoCVisualize',
	#package : 'AoCVisualize'
}

{ #category : 'public' }
AoC2023 class >> day20 [

  SpRoassalPresenter new canvas: self new day20; openModal
]

{ #category : 'public' }
AoC2023 class >> day25 [

  | presenter |
  presenter := SpRoassalPresenter new.
  presenter canvas: self new day25.
  presenter openModal
]

{ #category : 'public' }
AoC2023 >> day20 [
   "Visualize node connectivity"

   ^ self day20view: self day20load
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

{ #category : 'private - building' }
AoC2023 >> day20view: aCollection [

   | canvas elements flipflipLineBuilder conjunctionLineBuilder |
   canvas := RSCanvas new.
   elements := aCollection keys collect: [ :name | RSEllipse new size: 5; model: name ] as: RSGroup.
   elements @ RSDraggable.
   canvas addAll: elements.
   flipflipLineBuilder := RSLineBuilder line.
   flipflipLineBuilder canvas: canvas; color: Color red; connectFromAll: [ :each |
         ((aCollection at: each) at: #type) = 'FlipFlop' ifTrue: [ (aCollection at: each) at: #inputs ]
            ifFalse: [ {  } ] ].
   conjunctionLineBuilder := RSLineBuilder line.
   conjunctionLineBuilder canvas: canvas; color: Color blue; connectFromAll: [ :each |
         ((aCollection at: each) at: #type) = 'Conjunction' ifTrue: [ (aCollection at: each) at: #inputs ]
            ifFalse: [ {  } ] ].
   RSTreeLayout new on: elements.
   canvas @ RSCanvasController.
   ^ canvas
]

{ #category : 'public' }
AoC2023 >> day25 [
  "Visualize node connectivity"

  ^ self day25view: self day25load
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

{ #category : 'private - building' }
AoC2023 >> day25view: aCollection [

    | canvas lb elements |
    canvas := RSCanvas new.
    elements := aCollection keys collect: [ :c | RSEllipse new size: 5; model: c ] as: RSGroup.
    elements @ RSDraggable.
    canvas addAll: elements.
    lb := RSLineBuilder line.
    lb canvas: canvas; color: Color red; connectFromAll: [ :each | aCollection at: each ].
    RSForceBasedLayout new on: elements.
    canvas @ RSCanvasController.
    ^ canvas
]
