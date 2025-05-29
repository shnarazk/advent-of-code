
function datafile(year, day)::String
    days = lpad(string(day), 2, '0')
    seg = ENV["AOC_DIR"] * "/data/$(year)/input-day$(days)"
    if 0 < length(ARGS)
        seg *= "-$(ARGS[1])"
    end
    seg * ".txt"
end
