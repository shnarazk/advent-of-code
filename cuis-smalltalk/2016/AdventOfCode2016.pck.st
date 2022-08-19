'From Cuis 6.0 [latest update: #5213] on 4 June 2022 at 3:06:50 pm'!
'Description '!
!provides: 'AdventOfCode2016' 1 29!
!requires: 'RustBridge' 1 13 nil!
SystemOrganization addCategory: 'AdventOfCode2016-Day11'!
SystemOrganization addCategory: 'AdventOfCode2016-Day12'!
SystemOrganization addCategory: 'AdventOfCode2016-Day13'!
SystemOrganization addCategory: 'AdventOfCode2016'!


!classDefinition: #Day11State category: 'AdventOfCode2016-Day11'!
TestCase subclass: #Day11State
	instanceVariableNames: 'code currentCost estimatedCost aStart aGoal example'
	classVariableNames: 'Goal Kinds NumberOfObjects Width'
	poolDictionaries: ''
	category: 'AdventOfCode2016-Day11'!
!classDefinition: 'Day11State class' category: 'AdventOfCode2016-Day11'!
Day11State class
	instanceVariableNames: ''!

!classDefinition: #Day12Test category: 'AdventOfCode2016-Day12'!
TestCase subclass: #Day12Test
	instanceVariableNames: 'myComputer'
	classVariableNames: ''
	poolDictionaries: ''
	category: 'AdventOfCode2016-Day12'!
!classDefinition: 'Day12Test class' category: 'AdventOfCode2016-Day12'!
Day12Test class
	instanceVariableNames: ''!

!classDefinition: #Day13 category: 'AdventOfCode2016-Day13'!
TestCase subclass: #Day13
	instanceVariableNames: 'cost goal toEvaluate favorite'
	classVariableNames: ''
	poolDictionaries: ''
	category: 'AdventOfCode2016-Day13'!
!classDefinition: 'Day13 class' category: 'AdventOfCode2016-Day13'!
Day13 class
	instanceVariableNames: ''!

!classDefinition: #Day16 category: 'AdventOfCode2016'!
TestCase subclass: #Day16
	instanceVariableNames: 'length notShrink'
	classVariableNames: ''
	poolDictionaries: ''
	category: 'AdventOfCode2016'!
!classDefinition: 'Day16 class' category: 'AdventOfCode2016'!
Day16 class
	instanceVariableNames: ''!

!classDefinition: #Day17 category: 'AdventOfCode2016'!
TestCase subclass: #Day17
	instanceVariableNames: 'location key path'
	classVariableNames: 'FoundGoal Hasher Input ToVisit Visit'
	poolDictionaries: ''
	category: 'AdventOfCode2016'!
!classDefinition: 'Day17 class' category: 'AdventOfCode2016'!
Day17 class
	instanceVariableNames: ''!

!classDefinition: #Day12 category: 'AdventOfCode2016-Day12'!
Object subclass: #Day12
	instanceVariableNames: 'register code pc'
	classVariableNames: 'Input'
	poolDictionaries: ''
	category: 'AdventOfCode2016-Day12'!
!classDefinition: 'Day12 class' category: 'AdventOfCode2016-Day12'!
Day12 class
	instanceVariableNames: ''!


!Day11State commentStamp: 'shnarazk 5/28/2022 09:31:19' prior: 0!
Compressed state description. And it is a sub-class of TestCase for itself. So we don't need another class.!

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 12:09:33'!
code
^code! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/28/2022 14:40:50'!
currentCost
^currentCost! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/28/2022 14:40:15'!
currentCost: aCost
	| g c |
	currentCost := aCost.
	"And update the estimated cost"
	g := 0.
	c := 0.
	1
		to: self class kinds
		do: [ :kind |
			g := g + 3 - (self floorOfGenerator: kind).
			c := c + 3 - (self floorOfChip: kind) ].
	estimatedCost := currentCost + g + (c * 2).! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 09:07:37'!
estimatedCost
^estimatedCost ! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 02:03:32'!
floorOfChip: kind
	| index |
	index := self objectIndexOfChip: kind.
	^ self floorOfObject: index.! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 01:37:18'!
floorOfElevator
"I mean Elevator."
	^ self floorOfObject: 1.! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 01:38:19'!
floorOfElevator: aFloor
	^ self
		floorOfObject: 1
		to: aFloor.! !

!Day11State methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 02:03:05'!
floorOfGenerator: kind
| index |
	index := self objectIndexOfGenerator: kind.
	^ self floorOfObject: index! !

!Day11State methodsFor: 'initialization' stamp: 'shnarazk 5/28/2022 14:39:05'!
initialize
	"every instance is initialized as being a start."
	super initialize.
	code := 0.
	currentCost := 0.
	estimatedCost := 0.! !

!Day11State methodsFor: 'initialization' stamp: 'shnarazk 5/25/2022 20:07:00'!
initializeAs: anIndex
	self initialize.
	code := anIndex.! !

!Day11State methodsFor: 'evaluating' stamp: 'shnarazk 5/28/2022 14:41:41'!
cost
	| visit toCheck depth |
	depth := 0.
	visit := Set new.
	toCheck := Heap new.
	toCheck add: self.
	[ toCheck isEmpty ] whileFalse: [ | state |
		state := toCheck removeFirst.
		state isGoal ifTrue: [ ^ state currentCost ].
		(visit includes: state code) ifFalse: [
			visit add: state code.
			depth := depth max: state currentCost.
			state neighborStates do: [ :each |
				toCheck add: each ]]].
	Transcript
		show: 'visit: ' , visit size asString;
		cr.
	Transcript
		show: 'depth: ' , depth asString;
		cr.
	self error: 'wrong calculation'.! !

!Day11State methodsFor: 'evaluating' stamp: 'shnarazk 5/28/2022 14:32:39'!
ifSafe: aBlock
	self isSafe
		ifTrue: [ aBlock value: self ].! !

!Day11State methodsFor: 'evaluating' stamp: 'shnarazk 5/25/2022 20:53:05'!
isGoal
	^ code = self class goal ! !

!Day11State methodsFor: 'evaluating' stamp: 'shnarazk 5/28/2022 09:38:51'!
isSafe
	self forAllKinds: [ :k | | floor |
		floor := self floorOfChip: k.
		(self floorOfGenerator: k) = floor ifFalse: [
			self forAllKinds: [ :i |
					(self floorOfGenerator: i) = floor ifTrue: [ ^ false ]]]].
	^ true.! !

!Day11State methodsFor: 'evaluating' stamp: 'shnarazk 5/28/2022 14:31:22'!
neighborStates
	"the main logic"
	| floor result |
	result := Set new.
	floor := self floorOfElevator.
	self
		allObjectPairsOn: floor
		do: [ :i :j |
			self adjacentFloors do: [ :f | | newState |
				newState := self
					moveTo: f
					with: i
					and: j.
				newState ifSafe: [ :s |
					result add: s ]]].
	^ result.! !

!Day11State methodsFor: 'comparing' stamp: 'shnarazk 5/27/2022 09:07:54'!
<= other
	^ estimatedCost <= other estimatedCost ! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 13:56:55'!
adjacentFloors
	| floor |
	floor := self floorOfElevator.
	floor = 0 ifTrue: [ ^ {1} ].
	floor = 3 ifTrue: [ ^ {2} ].
	^ {floor - 1 . floor + 1}.! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 13:01:57'!
allObjectPairsOn: floor do: aBlock
	"all but elevator"
	| objects |
	objects := self class numberOfObjects .
	2
		to: objects
		do: [ :i |
			(self floorOfObject: i) = floor ifTrue: [
				i
					to: objects
					do: [ :j |
						(self floorOfObject: j) = floor ifTrue: [
							aBlock
								value: i
								value: j ]]]].! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 13:49:25'!
allObjectsOn: floor do: aBlock
	"not in use"
	"all but elevator"
	2
		to: self class numberOfObjects
		do: [ :i |
	
			i = floor ifTrue: [ aBlock value: i ]].! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 11:38:53'!
floorOfObject: anObject
	| mask result |
	mask := (self class numberOfObjects - anObject) * 2.
	mask := 2 << mask.
	result := (code bitAnd: mask) > 0
		ifTrue: [ 2 ]
		ifFalse: [ 0 ].
	mask := mask >> 1.
	(code bitAnd: mask) > 0
		ifTrue: [ ^ result + 1 ]
		ifFalse: [ ^ result ].! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 11:39:03'!
floorOfObject: anObject to: floor
	| mask |
	mask := self class numberOfObjects - anObject * 2.
	mask := 2 << mask.
	code := code bitClear: mask.
	floor > 1 ifTrue: [ code := code bitOr: mask ].
	mask := mask >> 1.
	code := code bitClear: mask.
	floor odd ifTrue: [ code := code bitOr: mask ].! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/28/2022 14:40:50'!
moveTo: floor with: anObjest and: anotherObject
	| state |
	state := self class new initializeAs: code.
	state floorOfElevator: floor.
	state
		floorOfObject: anObjest
		to: floor.
	state
		floorOfObject: anotherObject
		to: floor.
	state currentCost: self currentCost + 1.
	^ state.! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 01:34:43'!
objectIndexOfChip: k
	"index starts from 1 in Smalltalk. And 1 is used for Elevator."
	^ k * 2 + 1.! !

!Day11State methodsFor: 'private' stamp: 'shnarazk 5/27/2022 01:34:11'!
objectIndexOfGenerator: k
"index starts from 1 in Smalltalk. And 1 is used for Elevator."
^ k * 2! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 09:24:10'!
setUp
	self class setKinds: 2.
	aStart := self class new.
	aGoal := self class new initializeAs: 1023.
	example := self class represents:
		{1. 0. 2. 0}.! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 09:28:07'!
testAdjacentFloors
	self
		assert:
			{1}
		equals: aStart adjacentFloors.
	self
		assert:
			{2}
		equals: aGoal adjacentFloors.
	example floorOfElevator: 1.
	self
		assert:
			{0. 2}
		equals: example adjacentFloors.! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 14:41:41'!
testCostToGoal
self assert: 11 equals: example cost .! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 09:27:56'!
testFloorOfElevator
	example floorOfElevator: 3.
	self
		assert: 3
		equals: example floorOfElevator.
	example floorOfElevator: 1.
	self
		assert: 1
		equals: example floorOfElevator.
	example floorOfElevator: 2.
	self
		assert: 2
		equals: example floorOfElevator.! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 09:27:44'!
testFloorOfObject
	self
		assert: 0
		equals: (example floorOfObject: 1).
	self
		assert: 1
		equals: (example floorOfObject: 2).
	self
		assert: 0
		equals: (example floorOfObject: 3).
	self
		assert: 2
		equals: (example floorOfObject: 4).
	self
		assert: 0
		equals: (example floorOfObject: 5).
	self
		assert: 1
		equals: (example floorOfObject: (example objectIndexOfGenerator: 1)).
	self
		assert: 0
		equals: (example floorOfObject: (example objectIndexOfChip: 1)).
	self
		assert: 2
		equals: (example floorOfObject: (example objectIndexOfGenerator: 2)).
	self
		assert: 0
		equals: (example floorOfObject: (example objectIndexOfChip: 2)).
	self assert: 3 equals: (aGoal floorOfObject: 1).! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 09:27:31'!
testFloorOfObjectTo
	example
		floorOfObject: 2
		to: 3.
	self assert: 3 equals: (example floorOfObject: 2).
	example
		floorOfObject: 3
		to: 2.
	self assert: 2 equals: (example floorOfObject: 3).
	example
		floorOfObject: 4
		to: 1.
	self assert: 1 equals: (example floorOfObject: 4).
	example
		floorOfObject: 5
		to: 0.
	self assert: 0 equals: (example floorOfObject: 5).! !

!Day11State methodsFor: 'testing' stamp: 'shnarazk 5/28/2022 09:27:15'!
testIsSafe
	self
		assert: true
		equals: aStart isSafe.
	self
		assert: true
		equals: aGoal isSafe.
	self
		assert: true
		equals: example isSafe.! !

!Day11State methodsFor: 'running' stamp: 'shnarazk 5/28/2022 09:37:00'!
forAllKinds: aBlock
1 to: self class kinds do: aBlock ! !

!Day11State class methodsFor: 'accessing' stamp: 'shnarazk 5/25/2022 20:51:58'!
goal
^Goal ! !

!Day11State class methodsFor: 'accessing' stamp: 'shnarazk 5/26/2022 22:03:41'!
kinds
^Kinds ! !

!Day11State class methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 11:21:20'!
numberOfObjects
^NumberOfObjects ! !

!Day11State class methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 11:52:23'!
setKinds: k
	Kinds := k.
	"Generator and Microchip, plus elevator"
	Width := k * 2 + 1.
	NumberOfObjects := k * 2 + 1.
	Goal := 4 ^ NumberOfObjects - 1.! !

!Day11State class methodsFor: 'instance creation' stamp: 'shnarazk 5/27/2022 09:28:21'!
newAs: aCode
	| instance |
	instance := self new.
	instance initializeAs: aCode.
	^ instance.! !

!Day11State class methodsFor: 'instance creation' stamp: 'shnarazk 5/27/2022 09:41:59'!
represents: vec
	| code |
	code := vec inject: 0 into: [ :total :val | (total * 4) + val].
	^self newAs: code! !

!Day11State class methodsFor: 'evaluating' stamp: 'shnarazk 5/28/2022 14:43:06'!
part1
	| start |
	Day11State setKinds: 5.
	start := Day11State represents:
		{0. 0. 0. 0. 1. 2. 1. 1. 1. 1}.
	Transcript show: start cost.! !

!Day11State class methodsFor: 'evaluating' stamp: 'shnarazk 5/28/2022 14:41:41'!
part2
	| start |
	Day11State setKinds: 7.
	start := Day11State represents:
		{0. 0. 0. 0. 1. 2. 1. 1. 1. 1. 0. 0. 0. 0. }.
	Transcript show: start cost.! !

!Day12Test methodsFor: 'testing' stamp: 'shnarazk 5/27/2022 22:36:17'!
demoStart
 myComputer := Day12 new.
myComputer load: self example .
myComputer start.! !

!Day12Test methodsFor: 'testing' stamp: 'shnarazk 5/27/2022 22:34:32'!
setUp
	myComputer := Day12 new.
	myComputer load: self  example.! !

!Day12Test methodsFor: 'accessing' stamp: 'shnarazk 5/27/2022 22:33:24'!
example
	^ {
		{#cpy. 41. #a}. 
		{#inc. #a}. 
		{#inc. #a}. 
		{#dec. #a}. 
		{#jnz. #a. 2}. 
		{#dec. #a}
	}.! !

!Day12Test class methodsFor: 'associating' stamp: 'shnarazk 5/27/2022 22:37:19'!
demoStart
| myComputer |
	myComputer := Day12 new.
	myComputer load: self example.
	myComputer start.! !

!Day13 methodsFor: 'running' stamp: 'shnarazk 5/28/2022 21:18:40'!
setUp
	super setUp.
	favorite := 10.! !

!Day13 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 05:28:20'!
isGoal: aTuple
	^ (aTuple at: 3) = goal! !

!Day13 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 05:29:17'!
isOpenSpace: aTuple
	| x y val ones |
	x := (aTuple at: 3) x.
	y := (aTuple at: 3) y.
	val := x * x + (x * 3) + (x * y * 2) + y + (y * y).
	val := val + favorite.
	ones := 0.
	[ val > 0 ] whileTrue: [
		(val bitAnd: 1) > 0 ifTrue: [ ones := ones + 1 ].
		val := val // 2 ].
	^ ones even.! !

!Day13 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 05:44:35'!
rechableSitesBy: aLimit
	goal := 1 @ 1.
	cost := Dictionary new.
	cost
		at: goal
		put: 0.
	toEvaluate := Heap sortBlock: [ :a :b |
		(a at: 1) <= (b at: 1) ].
	toEvaluate add:
		{goal x + goal y. 0. 1@1}.
	[ toEvaluate isEmpty ] whileFalse: [ | state |
		state := toEvaluate removeFirst.
		aLimit < (state at: 2) ifTrue: [ ^ (cost select: [ :val |
				val isNil not and: [ val <= aLimit ]]) size ].
		self registerNextStatesOf: state ].! !

!Day13 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 05:37:14'!
registerNextStatesOf: aState
	| c x y xrange yrange |
	c := aState at: 2.
	x := (aState at: 3) x.
	y := (aState at: 3) y.
	xrange := x = 0
		ifTrue:
			{0. 1}
		ifFalse:
			{x - 1. x. x + 1}.
	yrange := y = 0
		ifTrue:
			{0. 1}
		ifFalse:
			{y - 1. y. y + 1}.
	self
		rangeX: xrange
		andY: yrange
		require: [ :p |
			p x = x or: p y = y ]
		on: [ :p | | newState xdist ydist |
			xdist := (goal x - p x) abs.
			ydist := (goal y - p y) abs.
			newState := {c + 1 + xdist + ydist. c + 1. p}.
			(cost includesKey: p) ifFalse: [
				(self isOpenSpace: newState)
					ifTrue: [
						cost
							at: p
							put: c + 1.
						toEvaluate add: newState ]
					ifFalse: [
						cost
							at: p
							put: nil ]]].! !

!Day13 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 05:41:16'!
stepsTo: aGoal
	goal := aGoal.
	cost := Dictionary new.
	cost
		at: 1 @ 1
		put: 0.
	toEvaluate := Heap sortBlock: [ :a :b |
		(a at: 1) <= (b at: 1) ].
	toEvaluate add:
		{goal x + goal y. 0. 1@1}.
	[ toEvaluate isEmpty ] whileFalse: [ | state |
		state := toEvaluate removeFirst.
		(self isGoal: state) ifTrue: [ "Transcript show: cost size."
			^ state at: 2 ].
		self registerNextStatesOf: state ].! !

!Day13 methodsFor: 'accessing' stamp: 'shnarazk 5/28/2022 21:17:53'!
favorite
^favorite ! !

!Day13 methodsFor: 'accessing' stamp: 'shnarazk 5/28/2022 21:18:06'!
favorite: aNumber
	 favorite := aNumber ! !

!Day13 methodsFor: 'accessing' stamp: 'shnarazk 5/31/2022 05:30:08'!
rangeX: aRange andY: anotherRange require: filterBlock on: aBlock
	aRange do: [ :x |
		anotherRange do: [ :y |
			(filterBlock
				value: x@y) ifTrue: [
				aBlock
					value: x@y ]]].! !

!Day13 methodsFor: 'testing' stamp: 'shnarazk 5/31/2022 05:38:59'!
testIsOpenSpace
	self
		assert: true
		equals:
			(self isOpenSpace:
				{0. 0. 1@1}).
	self
		assert: true
		equals:
			(self isOpenSpace:
				{0. 0. 1@2}).
	self
		assert: false
		equals:
			(self isOpenSpace:
				{0. 0. 0@2}).
	self
		assert: false
		equals:
			(self isOpenSpace:
				{0. 0. 5@1}).! !

!Day13 methodsFor: 'testing' stamp: 'shnarazk 5/31/2022 05:39:31'!
testStepsTo
	self
		assert: 11
		equals: (self stepsTo: 7 @4 ).! !

!Day13 class methodsFor: 'instance creation' stamp: 'shnarazk 5/31/2022 05:26:38'!
part1
	| solver |
	solver := self new.
	solver favorite: 1364.
	^ solver stepsTo: 31@39.! !

!Day13 class methodsFor: 'instance creation' stamp: 'shnarazk 5/28/2022 23:36:36'!
part2
	| solver |
	solver := self new.
	solver favorite: 1364.
	^ solver rechableSitesBy: 50.! !

!Day16 methodsFor: 'testing' stamp: 'shnarazk 5/31/2022 12:20:45'!
testExpand
	notShrink := true.
	length := 2.
	self
		assert:
			(self expand:
				{true})
		equals:
			{true. false. false}.
	self
		assert:
			(self expand:
				{false})
		equals:
			{false. false. true}.
	length := 6.
	self
		assert:
			(self expand:
				{true. true. true. true. true})
		equals:
			{true. true. true. true. true. false. false. false. false. false. false}.! !

!Day16 methodsFor: 'testing' stamp: 'shnarazk 5/31/2022 09:27:42'!
testShrink
	self
		assert:
			(self shrink:
				{true. true. true. true})
		equals:
			{true}.
	self
		assert:
			(self shrink:
				{true. true. false. true})
		equals:
			{false}.
	self
		assert:
			(self shrink:
				{true. false. true})
		equals:
			{true. false. true}.! !

!Day16 methodsFor: 'initialization' stamp: 'shnarazk 5/31/2022 12:14:12'!
initialize
	super initialize.
	notShrink := false.! !

!Day16 methodsFor: 'converting' stamp: 'shnarazk 5/31/2022 12:27:22'!
fromString: aString
	^ (aString collect:
		[ :char |
		char = $1 ] ) asArray.! !

!Day16 methodsFor: 'converting' stamp: 'shnarazk 5/31/2022 12:42:47'!
toString: aVec
	^ aVec
		inject: ''
		into:
			[ :str :bool |
			bool
				ifTrue: [ str , '1' ]
				ifFalse: [ str , '0' ]].! !

!Day16 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 13:04:31'!
expand: aVec
	aVec size < length ifTrue: [ ^ self expand:
			aVec ,
				{false} ,
				(aVec reverse collect: [ :v |
					v not ]) ].
	notShrink ifTrue: [ ^ aVec ].
	"Transcript show: 'Fullfilled: ' , (self toString: aVec)."
	^ self shrink:
		(aVec
			copyFrom: 1
			count: length).! !

!Day16 methodsFor: 'evaluating' stamp: 'shnarazk 5/31/2022 13:04:39'!
shrink: aVec
	"Transcript show: 'Reducing: ' , (self toString: aVec)."
	aVec size odd
		ifTrue: [ ^ self toString: aVec ]
		ifFalse: [ | tmp |
			tmp := ((1 to: aVec size) select: [ :i |
				i odd ]) collect: [ :i |
				(aVec at: i) = (aVec at: i + 1) ].
			^ self shrink: tmp ].! !

!Day16 methodsFor: 'as yet unclassified' stamp: 'shnarazk 5/31/2022 12:25:25'!
length: aNumber
length := aNumber ! !

!Day16 class methodsFor: 'as yet unclassified' stamp: 'shnarazk 5/31/2022 12:28:02'!
example
	| solver data |
	solver := self new.
	solver length: 20.
	data := solver fromString: '10000'.
	^ solver  expand: data.! !

!Day16 class methodsFor: 'as yet unclassified' stamp: 'shnarazk 5/31/2022 12:53:19'!
part1
	| solver data |
	solver := self new.
	solver length: 272.
	data := solver fromString: '10001110011110000'.
	Transcript show: 'Given: ', (solver toString: data).
	^ solver expand: data.! !

!Day16 class methodsFor: 'as yet unclassified' stamp: 'shnarazk 5/31/2022 13:04:12'!
part2
	| solver data |
	solver := self new.
	solver length: 35651584.
	data := solver fromString: '10001110011110000'.
	Transcript show: 'Given: ' , (solver toString: data).
	^ solver expand: data.! !

!Day17 methodsFor: 'accessing' stamp: 'shnarazk 6/3/2022 01:19:55'!
cost
^key size! !

!Day17 methodsFor: 'accessing' stamp: 'shnarazk 6/3/2022 01:21:12'!
location
	^ location ! !

!Day17 methodsFor: 'accessing' stamp: 'shnarazk 6/3/2022 01:21:32'!
location: aPoint
	location := aPoint ! !

!Day17 methodsFor: 'accessing' stamp: 'shnarazk 6/4/2022 13:09:52'!
path
^path! !

!Day17 methodsFor: 'accessing' stamp: 'shnarazk 6/4/2022 13:10:09'!
path: aPath
	path := aPath! !

!Day17 methodsFor: 'associating' stamp: 'shnarazk 6/4/2022 13:23:21'!
neighbars: aBlock
	| next masks locations |
	4 @ 4 = location ifTrue: [
		aBlock value: path.
		^ {} ].
	next := self nextKey.
	masks := #(1 2 3 4 ) collect: [ :each |
		(next at: each) > $a ].
	locations := {0 @ -1. 0 @ 1. -1 @ 0. 1 @ 0} collect: [ :each |
		location + each ].
	^ (1 to: 4)
		select: [ :each |
			(masks at: each) and: [
				(locations at: each)
					between: 1 @ 1
					and: 4 @ 4 ]]
		thenCollect: [ :each |
			self class
				newAt: (locations at: each)
				from:
					path ,
						({'U'. 'D'. 'L'. 'R'} at: each) ].! !

!Day17 methodsFor: 'associating' stamp: 'shnarazk 6/4/2022 13:12:33'!
nextKey
	^ self class hasher hash: (self class input, path)! !

!Day17 methodsFor: 'initialization' stamp: 'shnarazk 6/4/2022 13:27:34'!
initialize
	location := 1@1.
	path := ''! !

!Day17 class methodsFor: 'instance creation' stamp: 'shnarazk 6/4/2022 13:17:46'!
newAt: aPoint from: aPath
	| instance |
	instance := self new.
	instance
		location: aPoint;
		path: aPath.
	^ instance.! !

!Day17 class methodsFor: 'initialization' stamp: 'shnarazk 6/2/2022 20:46:12'!
initialize
	super initialize.
	self setHasher.
	Visit := Dictionary new.
	ToVisit := Heap new.! !

!Day17 class methodsFor: 'initialization' stamp: 'shnarazk 6/2/2022 20:06:26'!
setHasher
Hasher := RustCaller1 new.! !

!Day17 class methodsFor: 'accessing' stamp: 'shnarazk 6/3/2022 16:59:17'!
foundGoal
^FoundGoal ! !

!Day17 class methodsFor: 'accessing' stamp: 'shnarazk 6/3/2022 17:00:02'!
foundGoal: aNumber
	FoundGoal := aNumber .! !

!Day17 class methodsFor: 'accessing' stamp: 'shnarazk 6/2/2022 20:05:23'!
hasher
^Hasher! !

!Day17 class methodsFor: 'accessing' stamp: 'shnarazk 6/2/2022 20:05:44'!
hasher: aHasher
	Hasher := aHasher ! !

!Day17 class methodsFor: 'accessing' stamp: 'shnarazk 6/4/2022 13:11:51'!
input
	^Input ! !

!Day17 class methodsFor: 'methods' stamp: 'shnarazk 6/3/2022 20:02:55'!
example
	self initialize.
	"Input := 'hijkl'."
	"Input := 'ihgpwlah'."
	Input := 'kglvqrro'.
	^ self solve.! !

!Day17 class methodsFor: 'methods' stamp: 'shnarazk 6/3/2022 20:07:44'!
part1
	self initialize.
	Input := 'gdjjyniy'.
	^ self solve.! !

!Day17 class methodsFor: 'methods' stamp: 'shnarazk 6/4/2022 15:06:24'!
part2
	self initialize.
	Input := 'gdjjyniy' "'ihgpwlah'".
	^ self solve2.! !

!Day17 class methodsFor: 'methods' stamp: 'shnarazk 6/4/2022 13:24:37'!
solve
	| start stage |
	FoundGoal := nil.
	start := self new.
	start location: 1 @ 1.
	stage := Set new.
	stage add: start.
	[ FoundGoal isNil & stage isEmpty not ] whileTrue: [
		Transcript show: stage.
		stage := stage
			inject: Set new
			into: [ :aSet :each |
				Transcript show: each path.
				(each neighbars: [ :path |
					FoundGoal := path ]) do: [ :next |
					aSet add: next ].
				aSet ]].
	^ FoundGoal.! !

!Day17 class methodsFor: 'methods' stamp: 'shnarazk 6/4/2022 15:01:27'!
solve2
	| start stage |
	FoundGoal := 0.
	start := self new.
	start location: 1 @ 1.
	stage := Set new.
	stage add: start.
	[ stage isEmpty not ] whileTrue: [
		"Transcript show: FoundGoal asString."
		stage := stage
			inject: Set new
			into: [ :aSet :each |
				"Transcript show: each key."
				(each neighbars: [ :path |
					FoundGoal := FoundGoal max: path size ]) do: [ :next |
					aSet add: next ].
				aSet ]].
	^ FoundGoal.! !

!Day12 methodsFor: 'evaluating' stamp: 'shnarazk 5/27/2022 23:20:17'!
execute: anInstruction
	| opCode |
	opCode := anInstruction at: 1.
	"Transcript show: opCode."
	opCode = #cpy ifTrue: [ | from to val |
		from := anInstruction at: 2.
		to := anInstruction at: 3.
		val := from isNumber
			ifTrue: [ from ]
			ifFalse: [ register at: from ].
		register
			at: to
			put: val.
		pc := pc + 1.
		^ self ].
	opCode = #inc ifTrue: [ | name val |
		name := anInstruction at: 2.
		val := register at: name.
		register
			at: name
			put: val + 1.
		pc := pc + 1.
		^ self ].
	opCode = #dec ifTrue: [ | name val |
		name := anInstruction at: 2.
		val := register at: name.
		register
			at: name
			put: val - 1.
		pc := pc + 1.
		^ self ].
	opCode = #jnz ifTrue: [ | op1 cond op2 offset |
		op1 := anInstruction at: 2.
		cond := op1 isNumber
			ifTrue: [ op1 ]
			ifFalse: [ register at: op1 ].
		op2 := anInstruction at: 3.
		offset := op2 isNumber
			ifTrue: [ op2 ]
			ifFalse: [ register at: op2 ].
		pc := pc +
			(cond = 0
				ifTrue: [ 1 ]
				ifFalse: [ offset ]).
		^ self ].! !

!Day12 methodsFor: 'evaluating' stamp: 'shnarazk 5/27/2022 23:02:07'!
start
	| end |
	pc := 1.
	end := code size.
	[ end < pc ] whileFalse: [ | instruction oldPc |
		oldPc := pc.
		instruction := code at: pc.
		"Transcript show: instruction asString."
		self execute: instruction.
		oldPc = pc ifTrue: [ self error: 'Not updated PC' ]].
	Transcript show: (register at: #a).! !

!Day12 methodsFor: 'initialization' stamp: 'shnarazk 5/27/2022 22:41:19'!
initialize
pc := 1.
register := Dictionary new.
register at: #a put: 0; at: #b put: 0; at: #c put: 0; at: #d put: 0.! !

!Day12 methodsFor: 'initialization' stamp: 'shnarazk 5/27/2022 22:18:30'!
load: aProgram
	code := aProgram.
	pc := 1.! !

!Day12 methodsFor: 'as yet unclassified' stamp: 'shnarazk 5/27/2022 23:22:55'!
at: reg put: val
register at: reg put: val! !

!Day12 class methodsFor: 'initialization' stamp: 'shnarazk 5/27/2022 23:18:53'!
part1
	| code myComputer |
	code := {
	{#cpy . 1 . #a} .
      {#cpy . 1 . #b} .
      {#cpy . 26 . #d} .
      {#jnz . #c . 2} .
      {#jnz . 1 . 5} .
      {#cpy . 7 . #c} .
      {#inc . #d}. 
      {#dec . #c}.  
      {#jnz . #c . -2} .
     {#cpy . #a . #c} .
    {#inc . #a}.  
     {#dec . #b}.  
    {#jnz . #b . -2} .
     {#cpy . #c . #b} .
     {#dec . #d}.  
    {#jnz . #d . -6} .
     {#cpy . 16 . #c} .
     {#cpy . 12 . #d} .
     {#inc . #a}.  
    {#dec . #d}.  
  {#jnz . #d . -2} .
     {#dec . #c}.  
  {#jnz . #c . -5} 
	
	}.
	myComputer := self new.
	myComputer load: code.
	myComputer start.! !

!Day12 class methodsFor: 'initialization' stamp: 'shnarazk 5/27/2022 23:23:22'!
part2
	| code myComputer |
	code := {
		{#cpy. 1. #a}. 
		{#cpy. 1. #b}. 
		{#cpy. 26. #d}. 
		{#jnz. #c. 2}. 
		{#jnz. 1. 5}. 
		{#cpy. 7. #c}. 
		{#inc. #d}. 
		{#dec. #c}. 
		{#jnz. #c. -2}. 
		{#cpy. #a. #c}. 
		{#inc. #a}. 
		{#dec. #b}. 
		{#jnz. #b. -2}. 
		{#cpy. #c. #b}. 
		{#dec. #d}. 
		{#jnz. #d. -6}. 
		{#cpy. 16. #c}. 
		{#cpy. 12. #d}. 
		{#inc. #a}. 
		{#dec. #d}. 
		{#jnz. #d. -2}. 
		{#dec. #c}. 
		{#jnz. #c. -5}
	}.
	myComputer := self new.
	myComputer load: code.
	myComputer at: #c put: 1.
	myComputer start.! !
Day17 initialize!
