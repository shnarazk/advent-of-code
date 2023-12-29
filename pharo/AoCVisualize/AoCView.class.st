"
I am a class for AoC visualizers.
"
Class {
	#name : 'AoCView',
	#superclass : 'Object',
	#instVars : [
		'baseDirectory'
	],
	#category : 'AoCVisualize',
	#package : 'AoCVisualize'
}

{ #category : 'initialization' }
AoCView >> initialize [ 
super initialize .
baseDirectory := (Smalltalk os environment at: 'HOME') asPath / 'Repositories/advent-of-code'.
]
