module Math

export append_digits

"""
  Append two Ints like this:
  ```julia
  append_digits(102, 4050) => 1024050
  ```
"""
function append_digits(a::Int, b::Int)::Int
    n = b
    while 0 < n
        a *= 10
        n = div(n, 10)
    end
    a + b
end

end
