# This file is a part of Julia. License is MIT: https://julialang.org/license

struct PkgId
    uuid::Union{UUID,Nothing}
    name::String
    weak::Bool
    PkgId(u::UUID, name::AbstractString, weak::Bool=false) = new(UInt128(u) == 0 ? nothing : u, name, weak)
    PkgId(::Nothing, name::AbstractString, weak::Bool=false) = new(nothing, name, weak)
end
PkgId(name::AbstractString, weak::Bool=false) = PkgId(nothing, name, weak)

function PkgId(m::Module, name::String = String(nameof(moduleroot(m))))
    uuid = UUID(ccall(:jl_module_uuid, NTuple{2, UInt64}, (Any,), m))
    UInt128(uuid) == 0 ? PkgId(name) : PkgId(uuid, name)
end

==(a::PkgId, b::PkgId) = a.uuid == b.uuid && a.name == b.name && a.weak == b.weak

function hash(pkg::PkgId, h::UInt)
    h += 0xc9f248583a0ca36c % UInt
    h = hash(pkg.uuid, h)
    h = hash(pkg.name, h)
    h = hash(pkg.weak, h)
    return h
end

show(io::IO, pkg::PkgId) =
    print(io, pkg.name, " [", pkg.uuid === nothing ? "top-level" : pkg.uuid, "]", pkg.weak ? " (weak)" : "")

function binpack(pkg::PkgId)
    io = IOBuffer()
    write(io, UInt8(0))
    uuid = pkg.uuid
    write(io, uuid === nothing ? UInt128(0) : UInt128(uuid))
    write(io, pkg.weak)
    write(io, pkg.name)
    return String(take!(io))
end

function binunpack(s::String)
    io = IOBuffer(s)
    @assert read(io, UInt8) === 0x00
    uuid = read(io, UInt128)
    weak = read(io, Bool)
    name = read(io, String)
    return PkgId(UUID(uuid), name, weak)
end
