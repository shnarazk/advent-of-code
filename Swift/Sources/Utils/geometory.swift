/// implementation of 2D point as struct
///
@DebugDescription
public struct Pos: Comparable, Hashable, Sendable {
    public func negate() -> Pos {
        Pos(y: -y, x: -x)
    }
    public func abs() -> Pos {
        Pos(y: Swift.abs(y), x: Swift.abs(x))
    }

    public let y: Int
    public let x: Int
    private static let _zero: Pos = Pos(y: 0, x: 0)
    public init(y: Int, x: Int) {
        self.y = y
        self.x = x
    }
    public init() {
        self.y = 0
        self.x = 0
    }
    var debugDescription: String {
        "(y:\(y), x:\(x))"
    }
    public static var zero: Pos {
        ._zero
    }
    public static var unit: Pos {
        Pos(y: 1, x: 1)
    }
    public static var north: Pos {
        Pos(y: -1, x: 0)
    }
    public static var east: Pos {
        Pos(y: 0, x: 1)
    }
    public static var south: Pos {
        Pos(y: 1, x: 0)
    }
    public static var west: Pos {
        Pos(y: 0, x: -1)
    }
    public func turnRight() -> Pos {
        switch self {
        case .north: .east
        case .east: .south
        case .south: .west
        case .west: .north
        default: .zero
        }
    }
    public func turnLeft() -> Pos {
        switch self {
        case .west: .south
        case .south: .east
        case .east: .north
        case .north: .west
        default: .zero
        }
    }
    /// Return the last valid Pos(y - 1, x - 1)  corresponding to range (0, 0) to (y, x)
    public static func asBoundary(y: Int, x: Int) -> Pos {
        Pos(y: y - 1, x: x - 1)
    }
    /// Return the last valid Pos(y - 1, x - 1)  corresponding to range (0, 0) to `p`
    public static func asBoundary(_ p: (Int, Int)) -> Pos {
        Pos(y: p.0 - 1, x: p.1 - 1)
    }
    /// Pos.zero <= self <= size
    public func within(_ size: Pos) -> Pos? {
        if 0 <= self.y && self.y <= size.y && 0 <= self.x && self.x <= size.x {
            self
        } else {
            nil
        }
    }
    /// (0, 0) <= self < (y,x)
    public func within(y: Int, x: Int) -> Pos? {
        if 0 <= self.y && self.y < y && 0 <= self.x && self.x < x {
            self
        } else {
            nil
        }
    }
    public static func + (lhs: Pos, rhs: Pos) -> Pos {
        Pos(y: lhs.y + rhs.y, x: lhs.x + rhs.x)
    }
    public static func + (lhs: Pos, rhs: Int) -> Pos {
        Pos(y: lhs.y + rhs, x: lhs.x + rhs)
    }
    public static func - (lhs: Pos, rhs: Pos) -> Pos {
        Pos(y: lhs.y - rhs.y, x: lhs.x - rhs.x)
    }
    public static func - (lhs: Pos, rhs: Int) -> Pos {
        Pos(y: lhs.y - rhs, x: lhs.x - rhs)
    }
    public static func * (lhs: Pos, rhs: Pos) -> Pos {
        Pos(y: lhs.y * rhs.y, x: lhs.x * rhs.x)
    }
    public static func * (lhs: Pos, rhs: Int) -> Pos {
        Pos(y: lhs.y * rhs, x: lhs.x * rhs)
    }
    public static func / (lhs: Pos, rhs: Pos) -> Pos {
        Pos(y: lhs.y / rhs.y, x: lhs.x / rhs.x)
    }
    public static func / (lhs: Pos, rhs: Int) -> Pos {
        Pos(y: lhs.y / rhs, x: lhs.x / rhs)
    }
    public static func % (lhs: Pos, rhs: Pos) -> Pos {
        Pos(y: lhs.y % rhs.y, x: lhs.x % rhs.x)
    }
    public static func % (lhs: Pos, rhs: Int) -> Pos {
        Pos(y: lhs.y % rhs, x: lhs.x % rhs)
    }
    public static func < (lhs: Pos, rhs: Pos) -> Bool {
        lhs.y < rhs.y && lhs.x < rhs.x
    }
    public static func <= (lhs: Pos, rhs: Pos) -> Bool {
        lhs.y <= rhs.y && lhs.x <= rhs.x
    }
    /// L1 norm or Manhattan distance
    public func l1Norm() -> Int {
        Swift.abs(self.y) + Swift.abs(self.x)
    }
    public func next(upto bound: Pos) -> Pos? {
        if self.x < bound.x {
            return Pos(y: self.y, x: self.x + 1)
        }
        if self.y < bound.y {
            return Pos(y: self.y + 1, x: 0)
        }
        return nil
    }
    /// `bound` is the closed end.
    public func neighbors4(bound: Pos) -> [Pos] {
        [self + .north, self + .east, self + .south, self + .west].compactMap { $0.within(bound) }
    }
    /// Returns up to 8 orthogonal and diagonal neighbors of `self` within `(0,0)` and `bound` (closed).
    public func neighbors8(bound: Pos) -> [Pos] {
        [
            self + .north, self + .north + .east, self + .east, self + .south + .east,
            self + .south, self + .south + .west, self + .west, self + .north + .west,
        ]
        .compactMap { $0.within(bound) }
    }
    // return Pos(y: 2, x:2) from [[1,2,3], [4,5,6], [7,8,9]]
    public static func boundary<T>(of m: [[T]]) -> Pos {
        Pos(y: m.count - 1, x: m[0].count - 1)
    }
}

extension Array where Element: Collection, Element.Index == Int {
    /// allow `my2D[pos]`
    public subscript(_ pos: Pos) -> Element.Element {
        get {
            return self[pos.y][pos.x]
        }
    }
}
// Use Pos as index for [[T]]
// only on Arrays whose Element is a MutableCollection (e.g. another Array)
// whose indices are Ints
extension Array where Element: MutableCollection, Element.Index == Int {
    /// allow `my2D[pos]`
    public subscript(_ pos: Pos) -> Element.Element {
        get {
            return self[pos.y][pos.x]
        }
        set {
            self[pos.y][pos.x] = newValue
        }
    }
}

public func within(_ me: (Int, Int), in size: (Int, Int)) -> (Int, Int)? {
    if 0 <= me.0 && me.0 < size.0 && 0 <= me.1 && me.1 < size.1 {
        me
    } else {
        nil
    }
}

@DebugDescription
public struct Pos3: Comparable, Hashable, Sendable {
    public func negate() -> Pos3 {
        Pos3(z: -z, y: -y, x: -x)
    }
    public func abs() -> Pos3 {
        Pos3(z: Swift.abs(z), y: Swift.abs(y), x: Swift.abs(x))
    }

    public let z: Int
    public let y: Int
    public let x: Int
    public static let zero: Pos3 = Pos3(z: 0, y: 0, x: 0)
    public init(z: Int, y: Int, x: Int) {
        self.z = z
        self.y = y
        self.x = x
    }
    public init() {
        self.z = 0
        self.y = 0
        self.x = 0
    }
    var debugDescription: String {
        "(z:\(z), y:\(y), x:\(x))"
    }
    public static func < (lhs: Pos3, rhs: Pos3) -> Bool {
        lhs.z < rhs.z && lhs.y < rhs.y && lhs.x < rhs.x
    }
    public static func <= (lhs: Pos3, rhs: Pos3) -> Bool {
        lhs.z <= rhs.z && lhs.y <= rhs.y && lhs.x <= rhs.x
    }
    public static func + (lhs: Pos3, rhs: Pos3) -> Pos3 {
        Pos3(z: lhs.z + rhs.z, y: lhs.y + rhs.y, x: lhs.x + rhs.x)
    }
    public static func + (lhs: Pos3, rhs: Int) -> Pos3 {
        Pos3(z: lhs.z + rhs, y: lhs.y + rhs, x: lhs.x + rhs)
    }
    public static func - (lhs: Pos3, rhs: Pos3) -> Pos3 {
        Pos3(z: lhs.z - rhs.z, y: lhs.y - rhs.y, x: lhs.x - rhs.x)
    }
    public static func - (lhs: Pos3, rhs: Int) -> Pos3 {
        Pos3(z: lhs.z - rhs, y: lhs.y - rhs, x: lhs.x - rhs)
    }
    public static func * (lhs: Pos3, rhs: Pos3) -> Pos3 {
        Pos3(z: lhs.z * rhs.z, y: lhs.y * rhs.y, x: lhs.x * rhs.x)
    }
    public static func * (lhs: Pos3, rhs: Int) -> Pos3 {
        Pos3(z: lhs.z * rhs, y: lhs.y * rhs, x: lhs.x * rhs)
    }
    public static func / (lhs: Pos3, rhs: Pos3) -> Pos3 {
        Pos3(z: lhs.z / rhs.z, y: lhs.y / rhs.y, x: lhs.x / rhs.x)
    }
    public static func / (lhs: Pos3, rhs: Int) -> Pos3 {
        Pos3(z: lhs.z / rhs, y: lhs.y / rhs, x: lhs.x / rhs)
    }
    public static func % (lhs: Pos3, rhs: Pos3) -> Pos3 {
        Pos3(z: lhs.z % rhs.z, y: lhs.y % rhs.y, x: lhs.x % rhs.x)
    }
    public static func % (lhs: Pos3, rhs: Int) -> Pos3 {
        Pos3(z: lhs.z % rhs, y: lhs.y % rhs, x: lhs.x % rhs)
    }
}

extension Array
where
    Element: Collection, Element.Index == Int, Element.Element: Collection,
    Element.Element.Index == Int
{
    /// allow `my3D[pos]`
    public subscript(_ pos: Pos3) -> Element.Element.Element {
        get {
            return self[pos.z][pos.y][pos.x]
        }
    }
}
// Use Pos as index for [[T]]
// only on Arrays whose Element is a MutableCollection (e.g. another Array)
// whose indices are Ints
extension Array
where
    Element: MutableCollection, Element.Index == Int, Element.Element: MutableCollection,
    Element.Element.Index == Int
{
    /// allow `my3D[pos] = value`
    public subscript(_ pos: Pos3) -> Element.Element.Element {
        get {
            return self[pos.z][pos.y][pos.x]
        }
        set {
            self[pos.z][pos.y][pos.x] = newValue
        }
    }
}
