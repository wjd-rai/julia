using Test
include("irutils.jl")

# control flow backedge should taint `terminates`
@test Base.infer_effects((Int,)) do n
    for i = 1:n; end
end |> !Core.Compiler.is_terminates

# interprocedural-recursion should taint `terminates` **appropriately**
function sumrecur(a, x)
    isempty(a) && return x
    return sumrecur(Base.tail(a), x + first(a))
end
@test Base.infer_effects(sumrecur, (Tuple{Int,Int,Int},Int)) |> Core.Compiler.is_terminates
@test Base.infer_effects(sumrecur, (Tuple{Int,Int,Int,Vararg{Int}},Int)) |> !Core.Compiler.is_terminates

# https://github.com/JuliaLang/julia/issues/45781
@test Base.infer_effects((Float32,)) do a
    out1 = promote_type(Irrational{:π}, Bool)
    out2 = sin(a)
    out1, out2
end |> Core.Compiler.is_terminates

# refine :consistent-cy effect inference using the return type information
@test Base.infer_effects((Any,)) do x
    taint = Ref{Any}(x) # taints :consistent-cy, but will be adjusted
    throw(taint)
end |> Core.Compiler.is_consistent
@test Base.infer_effects((Int,)) do x
    if x < 0
        taint = Ref(x) # taints :consistent-cy, but will be adjusted
        throw(DomainError(x, taint))
    end
    return nothing
end |> Core.Compiler.is_consistent
@test Base.infer_effects((Int,)) do x
    if x < 0
        taint = Ref(x) # taints :consistent-cy, but will be adjusted
        throw(DomainError(x, taint))
    end
    return x == 0 ? nothing : x # should `Union` of isbitstype objects nicely
end |> Core.Compiler.is_consistent
@test Base.infer_effects((Symbol,Any)) do s, x
    if s === :throw
        taint = Ref{Any}(":throw option given") # taints :consistent-cy, but will be adjusted
        throw(taint)
    end
    return s # should handle `Symbol` nicely
end |> Core.Compiler.is_consistent
@test Base.infer_effects((Int,)) do x
    return Ref(x)
end |> !Core.Compiler.is_consistent
@test Base.infer_effects((Int,)) do x
    return x < 0 ? Ref(x) : nothing
end |> !Core.Compiler.is_consistent
@test Base.infer_effects((Int,)) do x
    if x < 0
        throw(DomainError(x, lazy"$x is negative"))
    end
    return nothing
end |> Core.Compiler.is_foldable

# effects propagation for `Core.invoke` calls
# https://github.com/JuliaLang/julia/issues/44763
global x44763::Int = 0
increase_x44763!(n) = (global x44763; x44763 += n)
invoke44763(x) = @invoke increase_x44763!(x)
@test Base.return_types() do
    invoke44763(42)
end |> only === Int
@test x44763 == 0

# Test that purity doesn't try to accidentally run unreachable code due to
# boundscheck elimination
function f_boundscheck_elim(n)
    # Inbounds here assumes that this is only ever called with n==0, but of
    # course the compiler has no way of knowing that, so it must not attempt
    # to run the @inbounds `getfield(sin, 1)`` that ntuple generates.
    ntuple(x->(@inbounds getfield(sin, x)), n)
end
@test Tuple{} <: code_typed(f_boundscheck_elim, Tuple{Int})[1][2]

# Test that purity modeling doesn't accidentally introduce new world age issues
f_redefine_me(x) = x+1
f_call_redefine() = f_redefine_me(0)
f_mk_opaque() = Base.Experimental.@opaque ()->Base.inferencebarrier(f_call_redefine)()
const op_capture_world = f_mk_opaque()
f_redefine_me(x) = x+2
@test op_capture_world() == 1
@test f_mk_opaque()() == 2

# backedge insertion for Any-typed, effect-free frame
const CONST_DICT = let d = Dict()
    for c in 'A':'z'
        push!(d, c => Int(c))
    end
    d
end
Base.@assume_effects :foldable getcharid(c) = CONST_DICT[c]
@noinline callf(f, args...) = f(args...)
function entry_to_be_invalidated(c)
    return callf(getcharid, c)
end
@test Base.infer_effects((Char,)) do x
    entry_to_be_invalidated(x)
end |> Core.Compiler.is_foldable
@test fully_eliminated(; retval=97) do
    entry_to_be_invalidated('a')
end
getcharid(c) = CONST_DICT[c] # now this is not eligible for concrete evaluation
@test Base.infer_effects((Char,)) do x
    entry_to_be_invalidated(x)
end |> !Core.Compiler.is_foldable
@test !fully_eliminated() do
    entry_to_be_invalidated('a')
end

@test !Core.Compiler.builtin_nothrow(Core.get_binding_type, Any[Rational{Int}, Core.Const(:foo)], Any)

# Nothrow for assignment to globals
global glob_assign_int::Int = 0
f_glob_assign_int() = global glob_assign_int += 1
let effects = Base.infer_effects(f_glob_assign_int, ())
    @test !Core.Compiler.is_effect_free(effects)
    @test Core.Compiler.is_nothrow(effects)
end
# Nothrow for setglobal!
global SETGLOBAL!_NOTHROW::Int = 0
let effects = Base.infer_effects() do
        setglobal!(@__MODULE__, :SETGLOBAL!_NOTHROW, 42)
    end
    @test Core.Compiler.is_nothrow(effects)
end

# we should taint `nothrow` if the binding doesn't exist and isn't fixed yet,
# as the cached effects can be easily wrong otherwise
# since the inference curently doesn't track "world-age" of global variables
@eval global_assignment_undefinedyet() = $(GlobalRef(@__MODULE__, :UNDEFINEDYET)) = 42
setglobal!_nothrow_undefinedyet() = setglobal!(@__MODULE__, :UNDEFINEDYET, 42)
let effects = Base.infer_effects() do
        global_assignment_undefinedyet()
    end
    @test !Core.Compiler.is_nothrow(effects)
end
let effects = Base.infer_effects() do
        setglobal!_nothrow_undefinedyet()
    end
    @test !Core.Compiler.is_nothrow(effects)
end
global UNDEFINEDYET::String = "0"
let effects = Base.infer_effects() do
        global_assignment_undefinedyet()
    end
    @test !Core.Compiler.is_nothrow(effects)
end
let effects = Base.infer_effects() do
        setglobal!_nothrow_undefinedyet()
    end
    @test !Core.Compiler.is_nothrow(effects)
end
@test_throws ErrorException setglobal!_nothrow_undefinedyet()

# Nothrow for setfield!
mutable struct SetfieldNothrow
    x::Int
end
f_setfield_nothrow() = SetfieldNothrow(0).x = 1
let effects = Base.infer_effects(f_setfield_nothrow, ())
    # Technically effect free even though we use the heap, since the
    # object doesn't escape, but the compiler doesn't know that.
    #@test Core.Compiler.is_effect_free(effects)
    @test Core.Compiler.is_nothrow(effects)
end

# :the_exception expression should taint :consistent-cy
global inconsistent_var::Int = 42
function throw_inconsistent() # this is still :consistent
    throw(inconsistent_var)
end
function catch_inconsistent()
    try
        throw_inconsistent()
    catch err
        err
    end
end
@test !Core.Compiler.is_consistent(Base.infer_effects(catch_inconsistent))
cache_inconsistent() = catch_inconsistent()
function compare_inconsistent()
    a = cache_inconsistent()
    global inconsistent_var = 0
    b = cache_inconsistent()
    return a === b
end
@test !compare_inconsistent()
# still we should be able to refine the tainted :consistent-cy using the return type info
function catch_inconsistent(x)
    try
        throw_inconsistent()
    catch err
        err
    end
    return x
end
@test Core.Compiler.is_consistent(Base.infer_effects(catch_inconsistent, (Symbol,)))
cache_inconsistent(x) = catch_inconsistent(x)
function compare_inconsistent(x)
    a = cache_inconsistent(x)
    b = cache_inconsistent(x)
    return a === b
end
@test compare_inconsistent(:foo)

# allocation with uninitialized fields should taint the :consistent-cy
struct UnsafeSome{T}
    value::T
    UnsafeSome{T}() where T = new{T}()
    UnsafeSome{T}(x) where T = new{T}(x)
    UnsafeSome(x::T) where T = new{T}(x)
end
@test Base.infer_effects() do
    UnsafeSome{Int}().value
end |> !Core.Compiler.is_consistent
let src = code_typed1() do
        UnsafeSome{Int}().value
    end
    @test any(isnew, src.code)
end

throw_undefined() = throw(UnsafeSome{Int}())
catch_undefined() = try
    throw_undefined()
catch err
    (err::UnsafeSome{Int}).value
end
@test !Core.Compiler.is_consistent(Base.infer_effects(catch_undefined))
