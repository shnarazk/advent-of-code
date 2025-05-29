/// implementation of 2D point as struct
public struct Pos: Comparable, Hashable, Sendable {
    public let y: Int
    public let x: Int
    private static let _zero: Pos = Pos(y: 0, x: 0)
    public init(y: Int, x: Int) {
        self.y = y
        self.x = x
    }
    public static var zero: Pos {
        get {
            ._zero
        }
    }
    /// Return the last valid Pos(y - 1, x - 1)  corresponding to range (0, 0) to (y, x)
    public static func asBound(y: Int, x: Int) -> Pos {
        Pos(y: y - 1, x: x - 1)
    }
    /// Return the last valid Pos(y - 1, x - 1)  corresponding to range (0, 0) to `p`
    public static func asBound(_ p: (Int, Int)) -> Pos {
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
    public static func - (lhs: Pos, rhs: Pos) -> Pos {
        Pos(y: lhs.y - rhs.y, x: lhs.x - rhs.x)
    }
    public static func < (lhs: Pos, rhs: Pos) -> Bool {
        lhs.y < rhs.y && lhs.x < rhs.x
    }
    public static func <= (lhs: Pos, rhs: Pos) -> Bool {
        lhs.y <= rhs.y && lhs.x <= rhs.x
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
    public func neighbors4(bound: Pos) -> [Pos] {
        [
            self + Pos(y: -1, x: 0),
            self + Pos(y: 0, x: 1),
            self + Pos(y: 1, x: 0),
            self + Pos(y: 0, x: -1),
        ].compactMap { $0.within(bound) }
    }
}

public func within(_ me: (Int, Int), in size: (Int, Int)) -> (Int, Int)? {
    if 0 <= me.0 && me.0 < size.0 && 0 <= me.1 && me.1 < size.1 {
        me
    } else {
        nil
    }
}
