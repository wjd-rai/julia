struct TriState; state::UInt8; end
const ALWAYS_FALSE = TriState(0x00)
const ALWAYS_TRUE  = TriState(0x01)
const CONSISTENT_IF_NOT_RETURNED = TriState(0x01 << 1)
const CONSISTENT_IF_NOGLOBAL = TriState(0x01 << 2)
const EFFECT_FREE_IF_NOGLOBAL = TriState(0x01 << 1)

function tristate_merge(old::TriState, new::TriState)
    if old === ALWAYS_FALSE || new === ALWAYS_FALSE
        return ALWAYS_FALSE
    end
    return TriState(old.state | new.state)
end

"""
    effects::Effects

Represents computational effects of a method call.

The effects are composed of the following set of different properties:
- `effects.consistent::TriState`: this method is guaranteed to return or terminate consistently
- `effect_free::TriState`: this method is free from externally semantically visible side effects
- `nothrow::TriState`: this method is guaranteed to not throw an exception
- `terminates::TriState`: this method is guaranteed to terminate
- `nonoverlayed::Bool`: indicates that any methods that may be called within this method
  are not defined in an [overlayed method table](@ref OverlayMethodTable)
- `notaskstate::TriState`: this method does not access any state bound to the current
  task and may thus be moved to a different task without changing observable
  behavior. Note that this currently implies that `noyield` as well, since
  yielding modifies the state of the current task, though this may be split
  in the future.
- `noglobal::TriState`: this method does not access or modify any mutable global state,
  e.g. this method does not access to mutable global object nor include assignment
  to a non-constant global variable.
See [`Base.@assume_effects`](@ref) for more detailed explanation on the definitions of these properties.

Along the abstract interpretation, `Effects` at each statement are analyzed locally and
they are merged into the single global `Effects` that represents the entire effects of
the analyzed method (see `tristate_merge!`).
Each effect property is represented as tri-state and managed separately.
The tri-state consists of `ALWAYS_TRUE`, `TRISTATE_UNKNOWN` and `ALWAYS_FALSE`, where they
have the following meanings:
- `ALWAYS_TRUE`: this method is guaranteed to not have this effect.
- `ALWAYS_FALSE`: this method may have this effect, and there is no need to do any further
  analysis w.r.t. this effect property as this conclusion will not be refined anyway.
- `TRISTATE_UNKNOWN`: this effect property may still be refined to `ALWAYS_TRUE` or
  `ALWAYS_FALSE`, e.g. using return type information.

An effect property is initialized with `ALWAYS_TRUE` and then transitioned towards
`ALWAYS_FALSE`. When we find a statement that has some effect, either of `TRISTATE_UNKNOWN`
or `ALWAYS_FALSE` is propagated. Note that however, within the current flow-insensitive
analysis design, it is usually difficult to derive a global conclusion accurately from local
analysis on each statement, and therefore, the effect analysis usually propagates the
`ALWAYS_FALSE` state conservatively.
"""
struct Effects
    consistent::TriState
    effect_free::TriState
    nothrow::TriState
    terminates::TriState
    nonoverlayed::Bool
    notaskstate::TriState
    noglobal::TriState
    # This effect is currently only tracked in inference and modified
    # :consistent before caching. We may want to track it in the future.
    inbounds_taints_consistency::Bool
    function Effects(
        consistent::TriState,
        effect_free::TriState,
        nothrow::TriState,
        terminates::TriState,
        nonoverlayed::Bool,
        notaskstate::TriState,
        noglobal::TriState,
        inbounds_taints_consistency::Bool = false)
        return new(
            consistent,
            effect_free,
            nothrow,
            terminates,
            nonoverlayed,
            notaskstate,
            noglobal,
            inbounds_taints_consistency)
    end
end

const EFFECTS_TOTAL    = Effects(ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_TRUE,  true,  ALWAYS_TRUE,  ALWAYS_TRUE)
const EFFECTS_THROWS   = Effects(ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_FALSE, ALWAYS_TRUE,  true,  ALWAYS_TRUE,  ALWAYS_TRUE)
const EFFECTS_UNKNOWN  = Effects(ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, true,  ALWAYS_FALSE, ALWAYS_FALSE) # mostly unknown, but it's not overlayed at least (e.g. it's not a call)
const EFFECTS_UNKNOWN′ = Effects(ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, false, ALWAYS_FALSE, ALWAYS_FALSE) # unknown, really

function Effects(e::Effects = EFFECTS_UNKNOWN′;
    consistent::TriState = e.consistent,
    effect_free::TriState = e.effect_free,
    nothrow::TriState = e.nothrow,
    terminates::TriState = e.terminates,
    nonoverlayed::Bool = e.nonoverlayed,
    notaskstate::TriState = e.notaskstate,
    noglobal::TriState = e.noglobal,
    inbounds_taints_consistency::Bool = e.inbounds_taints_consistency)
    return Effects(
        consistent,
        effect_free,
        nothrow,
        terminates,
        nonoverlayed,
        notaskstate,
        noglobal,
        inbounds_taints_consistency)
end

is_consistent(effects::Effects)   = effects.consistent === ALWAYS_TRUE
is_effect_free(effects::Effects)  = effects.effect_free === ALWAYS_TRUE
is_nothrow(effects::Effects)      = effects.nothrow === ALWAYS_TRUE
is_terminates(effects::Effects)   = effects.terminates === ALWAYS_TRUE
is_notaskstate(effects::Effects)  = effects.notaskstate === ALWAYS_TRUE
is_noglobal(effects::Effects)     = effects.noglobal === ALWAYS_TRUE
is_nonoverlayed(effects::Effects) = effects.nonoverlayed

# implies `is_notaskstate` & `is_noglobal`, but not explicitly checked here
is_foldable(effects::Effects) =
    is_consistent(effects) &&
    is_effect_free(effects) &&
    is_terminates(effects)
is_foldable(effects::Effects, argtypes::Vector{Any}) =
    is_consistent(effects, argtypes) &&
    is_effect_free(effects) &&
    is_terminates(effects)

is_total(effects::Effects) =
    is_foldable(effects) &&
    is_nothrow(effects)

is_removable_if_unused(effects::Effects) =
    is_effect_free(effects) &&
    is_terminates(effects) &&
    is_nothrow(effects)

is_consistent_if_not_returned(consistent::TriState) =
    !iszero(consistent.state & CONSISTENT_IF_NOT_RETURNED.state)
is_consistent_if_not_returned(effects::Effects) =
    is_consistent_if_not_returned(effects.consistent)

function is_consistent(effects::Effects, argtypes::Vector{Any})
    is_consistent(effects) && return true
    if is_consistent_if_noglobal(effects, argtypes)
        return is_noglobal(effects)
    end
    return false
end

is_effect_free_if_noglobal(effect_free::TriState) =
    !iszero(effect_free.state & EFFECT_FREE_IF_NOGLOBAL.state)

is_consistent_if_noglobal(consistent::TriState) =
    !iszero(consistent.state & CONSISTENT_IF_NOGLOBAL.state)
is_consistent_if_noglobal(effects::Effects, argtypes::Vector{Any}) =
    !is_consistent_if_not_returned(effects) &&
    is_consistent_if_noglobal(effects.consistent) &&
    all(is_effect_free_argtype, argtypes)

function encode_effects(e::Effects)
    return ((e.consistent.state)           << 0) |
           ((e.effect_free.state)          << 3) |
           ((e.nothrow.state)              << 5) |
           ((e.terminates.state)           << 7) |
           ((e.nonoverlayed % UInt32)      << 9) |
           ((e.notaskstate.state % UInt32) << 10) |
           ((e.noglobal.state % UInt32)    << 12)
end

function decode_effects(e::UInt32)
    return Effects(
        TriState((e >> 0)  & 0x07),
        TriState((e >> 3)  & 0x03),
        TriState((e >> 5)  & 0x03),
        TriState((e >> 7)  & 0x03),
        _Bool(   (e >> 9)  & 0x01),
        TriState((e >> 10)  & 0x03),
        TriState((e >> 12) & 0x03))
end

function tristate_merge(old::Effects, new::Effects)
    return Effects(
        tristate_merge(
            old.consistent, new.consistent),
        tristate_merge(
            old.effect_free, new.effect_free),
        tristate_merge(
            old.nothrow, new.nothrow),
        tristate_merge(
            old.terminates, new.terminates),
        old.nonoverlayed & new.nonoverlayed,
        tristate_merge(
            old.notaskstate, new.notaskstate),
        tristate_merge(
            old.noglobal, new.noglobal),
        old.inbounds_taints_consistency | new.inbounds_taints_consistency)
end

struct EffectsOverride
    consistent::Bool
    effect_free::Bool
    nothrow::Bool
    terminates_globally::Bool
    terminates_locally::Bool
    notaskstate::Bool
    noglobal::Bool
end

function encode_effects_override(eo::EffectsOverride)
    e = 0x00
    eo.consistent          && (e |= (0x01 << 0))
    eo.effect_free         && (e |= (0x01 << 1))
    eo.nothrow             && (e |= (0x01 << 2))
    eo.terminates_globally && (e |= (0x01 << 3))
    eo.terminates_locally  && (e |= (0x01 << 4))
    eo.notaskstate         && (e |= (0x01 << 5))
    eo.noglobal            && (e |= (0x01 << 6))
    return e
end

function decode_effects_override(e::UInt8)
    return EffectsOverride(
        (e & (0x01 << 0)) != 0x00,
        (e & (0x01 << 1)) != 0x00,
        (e & (0x01 << 2)) != 0x00,
        (e & (0x01 << 3)) != 0x00,
        (e & (0x01 << 4)) != 0x00,
        (e & (0x01 << 5)) != 0x00,
        (e & (0x01 << 6)) != 0x00)
end
