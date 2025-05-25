import Parsing
// import ArgumentParser

struct User {
    var id: Int
    var name: String
    var isAdmin: Bool
}

@main
struct Parser1 {

    public static func main() throws {
        let input = """
        	1,Blob,true
        	2,Blob,Jr.,false
        	3,Blob Sr.,true
        	"""
        let user = Parse(input: Substring.self) {
            Int.parser()
            ","
            Prefix { $0 != "," }.map(String.init)
            ","
            Bool.parser()
        }
            .map { User(id: $0, name: $1, isAdmin: $2) }
        
        var inp = input[...]
        
        
        let u = try user.parse(&inp)
        print("done.\(inp) \(u)")
    }
}
