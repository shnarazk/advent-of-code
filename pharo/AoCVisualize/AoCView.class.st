"
I am a class for AoC visualizers.
"
Class {
	#name : 'AoCView',
	#superclass : 'SpPresenter',
	#classTraits : '{} + TraitedClass',
	#instVars : [
		'baseDirectory',
		'updateButton',
		'update',
		'title',
		'graph'
	],
	#category : 'AoCVisualize',
	#package : 'AoCVisualize'
}

{ #category : 'initialization' }
AoCView >> connectPresenters [

   updateButton action: [ update ifNotNil: [ update value ]]
]

{ #category : 'layout' }
AoCView >> defaultLayout [

   ^ SpBoxLayout newVertical add: graph; add: updateButton expand: false; yourself
]

{ #category : 'initialization' }
AoCView >> initialize [

   super initialize.
   title := 'AoC visualizer'.
   baseDirectory := (Smalltalk os environment at: 'HOME') asPath / 'Repositories/advent-of-code'
]

{ #category : 'initialization' }
AoCView >> initializePresenters [

   graph := self newRoassal.
   updateButton := self newButton.
   "Get all iconnames by Smalltalk ui icons"
   updateButton label: 'Update'; icon: (self iconNamed: #smallUpdate)
]

{ #category : 'initialization' }
AoCView >> initializeWindow: aWindowPresenter [
aWindowPresenter title: title; initialExtent: 600@660
]
