#!/usr/bin/env julia
# Build a Julia sysimage with PackageCompiler.
#
# Usage examples:
#   julia scripts/build_sysimage.jl --project=.                         # infer packages from Project.toml
#   julia scripts/build_sysimage.jl --packages=AoC_Julia,ParserCombinator
#   julia scripts/build_sysimage.jl --project=. --warmup=scripts/warmup.jl
#   julia scripts/build_sysimage.jl --project=. --cpu-target=native
#   julia scripts/build_sysimage.jl --project=. --name=AoC_JuliaSys
#
# Options:
#   --project=PATH          Project to activate and infer packages (default: none)
#   --packages=A,B,C        Comma-separated package names to include (default: inferred or empty)
#   --sysimage-path=PATH    Output path (default: build/sysimages/<NAME>.{so|dylib|dll})
#   --name=NAME             Basename for sysimage if --sysimage-path is not given (default: inferred from project or "AppSysimage")
#   --warmup=PATH           Julia file to execute to record precompile statements (relative to project if --project is set)
#   --cpu-target=STRING     CPU target (e.g., native, haswell; see `julia --cpu-target=help`)
#   --force                 Overwrite an existing sysimage file
#   --help                  Show help
#
# Notes:
# - If you pass --project, this script activates that environment to infer direct dependencies and to resolve local packages.
# - The sysimage does not create a standalone executable. Use it at runtime:
#       julia --sysimage=path/to/sysimage.dylib your_script.jl
# - To capture more method specializations for your workload, provide a warmup script with --warmup.

using Pkg
import InteractiveUtils # for versioninfo if needed
import TOML

# ────────────────────────────────────────────────────────────────────────────────
# Utilities
# ────────────────────────────────────────────────────────────────────────────────

const STDERR = stderr

println_stderr(msg) = println(STDERR, msg)

function parse_args()
    opts = Dict{String,Union{Nothing,String,Bool}}(
        "project" => nothing,
        "packages" => nothing,
        "sysimage-path" => nothing,
        "name" => nothing,
        "warmup" => nothing,
        "cpu-target" => nothing,
        "force" => false,
    )
    for arg in ARGS
        if arg in ("-h", "--help")
            opts["help"] = ""
        elseif arg == "--force"
            opts["force"] = true
        elseif startswith(arg, "--project=")
            opts["project"] = split(arg, "=", limit=2)[2]
        elseif startswith(arg, "--packages=")
            opts["packages"] = split(arg, "=", limit=2)[2]
        elseif startswith(arg, "--sysimage-path=")
            opts["sysimage-path"] = split(arg, "=", limit=2)[2]
        elseif startswith(arg, "--name=")
            opts["name"] = split(arg, "=", limit=2)[2]
        elseif startswith(arg, "--warmup=")
            opts["warmup"] = split(arg, "=", limit=2)[2]
        elseif startswith(arg, "--cpu-target=")
            opts["cpu-target"] = split(arg, "=", limit=2)[2]
        else
            println_stderr("Unknown option: $arg")
            opts["help"] = ""
        end
    end
    return opts
end

function show_help()
    println("""
Build a Julia sysimage with PackageCompiler.

Options:
  --project=PATH          Project to activate and infer packages (default: none)
  --packages=A,B,C        Comma-separated package names to include (default: inferred or empty)
  --sysimage-path=PATH    Output path (default: build/sysimages/<NAME>.{so|dylib|dll})
  --name=NAME             Basename for sysimage if --sysimage-path is not given (default: inferred from project or "AppSysimage")
  --warmup=PATH           Julia file to execute to record precompile statements (relative to project if --project is set)
  --cpu-target=STRING     CPU target (e.g., native, haswell; see `julia --cpu-target=help`)
  --force                 Overwrite an existing sysimage file
  --help                  Show this help

Examples:
  julia scripts/build_sysimage.jl --project=.
  julia scripts/build_sysimage.jl --packages=AoC_Julia,ParserCombinator
  julia scripts/build_sysimage.jl --project=. --warmup=scripts/warmup.jl
  julia scripts/build_sysimage.jl --project=. --cpu-target=native
  julia scripts/build_sysimage.jl --project=. --name=AoC_JuliaSys
""")
end

function ensure_packagecompiler_loaded()
    try
        @eval using PackageCompiler
        return
    catch
        # Load PackageCompiler in an ephemeral environment so we don't mutate the project's dependencies
        println("Loading PackageCompiler in a temporary environment...")
        Pkg.activate(; temp=true, io=devnull)
        Pkg.add(name="PackageCompiler")
        @eval using PackageCompiler
    end
end

function read_project_toml(project_path::String)
    toml_path = isdir(project_path) ? joinpath(project_path, "Project.toml") : project_path
    if !isfile(toml_path)
        error("Project file not found at: $toml_path")
    end
    return TOML.parsefile(toml_path)
end

function project_name_from_toml(project_path::String)
    try
        t = read_project_toml(project_path)
        return get(t, "name", nothing)
    catch
        return nothing
    end
end

function sysimage_ext()
    if Sys.isapple()
        return "dylib"
    elseif Sys.iswindows()
        return "dll"
    else
        return "so"
    end
end

function default_output_path(name::String)
    outdir = joinpath(pwd(), "build", "sysimages")
    isdir(outdir) || mkpath(outdir)
    return joinpath(outdir, string(name, ".", sysimage_ext()))
end

function normalize_warmup_path(warmup::String, project_path::Union{Nothing,String})
    if project_path !== nothing && !isabspath(warmup)
        return abspath(joinpath(project_path, warmup))
    else
        return abspath(warmup)
    end
end

function infer_packages_from_project(project_path::String; include_project::Bool=true)
    # Activate the project to resolve path deps and registry entries
    Pkg.activate(project_path)
    deps = Pkg.dependencies()
    pkgs = String[]
    for (_, info) in deps
        # Only include direct deps; avoid stdlibs and internal tools
        if hasproperty(info, :is_direct_dep) && getproperty(info, :is_direct_dep) === true
            name = getproperty(info, :name)
            if name != "PackageCompiler"
                push!(pkgs, name)
            end
        end
    end
    # Optionally include the top-level project module if it has a name
    if include_project
        pname = project_name_from_toml(project_path)
        if pname !== nothing && !isempty(pname)
            push!(pkgs, String(pname))
        end
    end
    return unique(pkgs)
end

# ────────────────────────────────────────────────────────────────────────────────
# Main
# ────────────────────────────────────────────────────────────────────────────────

function main()
    opts = parse_args()
    if haskey(opts, "help")
        show_help()
        return
    end

    # Determine packages to include
    packages = String[]
    project_path = nothing
    if (p = opts["packages"]) !== nothing && !isempty(p)
        packages = [strip(s) for s in split(p, ",") if !isempty(strip(s))]
        println("Using explicitly specified packages: ", packages)
    elseif (proj = opts["project"]) !== nothing && !isempty(proj)
        project_path = proj
        println("Inferring packages from project: $project_path")
        packages = infer_packages_from_project(project_path; include_project=true)
        println("Inferred packages: ", packages)
    else
        println("No packages specified or project provided; building a base sysimage.")
    end

    # Determine output path
    default_name = let pn = (project_path === nothing ? nothing : project_name_from_toml(project_path))
        pn === nothing || isempty(pn) ? "AppSysimage" : string(pn, "Sysimage")
    end
    name = begin
        n = opts["name"]
        (n === nothing || isempty(String(n))) ? default_name : String(n)
    end

    sysimage_path = begin
        sp = opts["sysimage-path"]
        if sp === nothing || isempty(String(sp))
            default_output_path(name)
        else
            # Ensure parent directory exists
            outdir = dirname(String(sp))
            isdir(outdir) || mkpath(outdir)
            String(sp)
        end
    end

    warmup = begin
        w = opts["warmup"]
        if w === nothing || isempty(String(w))
            nothing
        else
            normalize_warmup_path(String(w), project_path)
        end
    end

    cpu_target = begin
        ct = opts["cpu-target"]
        (ct === nothing || isempty(String(ct))) ? nothing : String(ct)
    end

    force = opts["force"] === true

    # Resolve and load PackageCompiler (temporary environment to avoid mutating the project)
    ensure_packagecompiler_loaded()

    # Build create_sysimage kwargs
    kwargs = Dict{Symbol,Any}(:sysimage_path => sysimage_path)
    if warmup !== nothing
        kwargs[:precompile_execution_file] = warmup
    end
    if cpu_target !== nothing
        kwargs[:cpu_target] = cpu_target
    end

    # Handle existing file
    if isfile(sysimage_path)
        if force
            println("Removing existing sysimage: $sysimage_path")
            rm(sysimage_path; force=true)
        else
            println_stderr("Sysimage already exists at: $sysimage_path")
            println_stderr("Use --force to overwrite.")
            return
        end
    end

    # If a project is provided, activate it before building to ensure packages resolve correctly
    if project_path !== nothing
        println("Activating project: $(abspath(project_path))")
        Pkg.activate(project_path)
    end

    # Build
    println("Building sysimage at: $sysimage_path")
    try
        if isempty(packages)
            # Base/Stdlib-only sysimage
            PackageCompiler.create_sysimage(; kwargs...)
        else
            PackageCompiler.create_sysimage(Symbol.(packages); kwargs...)
        end
        println("Done.")
        println("Use it with:")
        println("  julia --sysimage=$(sysimage_path) your_script.jl")
    catch err
        println_stderr("Sysimage build failed: $(typeof(err)) - $(err)")
        rethrow()
    end
end

main()
