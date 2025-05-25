using Test

include(joinpath(@__DIR__, "../y2024day08.jl"))

@testset "(y2024day08) within function tests" begin
    # standard size
    s = (5, 5)
    @test within(s, (1, 1)) == (1, 1)
    @test within(s, (5, 5)) == (5, 5)
    @test within(s, (3, 4)) == (3, 4)
    @test within(s, (0, 3)) === nothing
    @test within(s, (6, 2)) === nothing
    @test within(s, (3, 0)) === nothing

    # different dimensions
    s2 = (3, 4)
    @test within(s2, (3, 4)) == (3, 4)
    @test within(s2, (1, 4)) == (1, 4)
    @test within(s2, (4, 1)) === nothing
    @test within(s2, (3, 0)) === nothing
end
