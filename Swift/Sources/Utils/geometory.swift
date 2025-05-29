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
    public func within(_ size: Pos) -> Pos? {
        if 0 <= self.y && self.y < size.y && 0 <= self.x && self.x < size.x {
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
}

public func within(_ me: (Int, Int), in size: (Int, Int)) -> (Int, Int)? {
    if 0 <= me.0 && me.0 < size.0 && 0 <= me.1 && me.1 < size.1 {
        me
    } else {
        nil
    }
}
