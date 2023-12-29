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
	| data nodes|
	data := (baseDirectory / 'day25.json') asFileReference readStreamDo: [ :stream | STON fromStream: stream ].
	
	nodes := data inject: Dictionary new 
	  into: [ :dic :element |dic at: (element at: 1)
	  update: [ :set | set  add: (element at: 2); yourself ]
        initial: [ Set new add: (element at: 2); yourself ]; yourself ].

	data do: [ :each || to |
         to := each at: 2.
         (nodes keys includes: to) ifFalse: [ nodes at: to put: {  } ] ].
    ^nodes

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
