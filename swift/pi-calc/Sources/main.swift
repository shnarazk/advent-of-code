public func main() {
  let limit: Int = 1_000_000_000
  let sum: Float = (0...limit).reduce(0) { (result, index) in
    let k = Float(index) * 4.0
    return result + 8.0 / ((k + 1) * (k + 3))
  }
  print(sum)
}

// var sum: Float = 0.0
// var index: Int = 1

// for i in 0...limit {
//     let k = Float(i) * 4.0
//     sum += 8.0 / ((k+1)*(k+3))
// }
