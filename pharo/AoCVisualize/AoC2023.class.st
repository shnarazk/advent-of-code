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
AoC2023 >> day25 [
"Visualize node connectivity"

	^ self day25view: self day25load
]

{ #category : 'private - loading' }
AoC2023 >> day25load [

   | data nodes |
   data := (baseDirectory / 'tmp/day25.json') asFileReference readStreamDo: [ :stream | STON fromStream: stream ].

   nodes := data inject: Dictionary new into: [ :dic :element |
               | to |
               to := element at: 2.
               dic at: (element at: 1) update: [ :set | set add: to; yourself ] initial: [ Set new add: to; yourself ].
               (dic keys includes: to) ifFalse: [ dic at: to put: Set new ].
               dic ].
   ^ nodes
]

{ #category : 'private - building' }
AoC2023 >> day25view: nodes [

	| canvas lb elements |
	canvas := RSCanvas new.
	elements := nodes keys collect: [ :c | RSEllipse new  size: 5;  model: c ] as: RSGroup.
	elements @ RSDraggable.
	canvas addAll: elements.
	lb := RSLineBuilder line.
	lb canvas: canvas; color: Color red; connectFromAll: [ :each | nodes at: each ].
	RSForceBasedLayout new on: elements.
	canvas @ RSCanvasController.
	^ canvas
]
