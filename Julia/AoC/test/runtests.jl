using Test
using AoC, AoC.Geometry, AoC.Math

@testset "within function tests" begin
    # standard size
    s = Dim2(5, 5)
    @test within(Dim2(2, 2), Dim2(2, 2)) == Dim2(2, 2)
    @test within(Dim2(2, 2), Dim2(3, 3)) == Dim2(2, 2)
    @test within(Dim2(2, 2), Dim2(3, 1)) === nothing
    @test within(Dim2(2, 2), Dim2(1, 3)) === nothing
    # different dimensions
    s2 = (3, 4)
end

@testset "append_digits function tests" begin
    @test append_digits(1, 2) == 12
    @test append_digits(123, 45) == 12345
    @test append_digits(120, 4050) == 1204050
end
