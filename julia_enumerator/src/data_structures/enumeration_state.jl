

abstract type Turn end

struct LeftTurn <: Turn end
struct RightTurn <: Turn end
struct ArgTurn <: Turn
    type::Tp
end

struct EnumerationState
    skeleton::Program
    context::Context
    path::Vector{Turn}
    cost::Float64
    free_parameters::Int64
    abstractors_only::Bool
end


struct BlockPrototype
    state::EnumerationState
    request::Tp
    input_vars::Vector{Union{Tuple{String,EntriesBranch},Nothing}}
    output_var::Union{Tuple{String,EntriesBranch},Nothing}
    complexity_factor::Float64
    reverse::Bool
end


initial_block_prototype(request, g::Grammar, inputs, output, complexity_factor) = BlockPrototype(
    EnumerationState(Hole(request, g), empty_context, [], 1.0, 0, false),
    request,
    inputs,
    output,
    complexity_factor,
    false,
)


function get_candidates_for_unknown_var(key, branch, branch_item, g)
    [initial_block_prototype(branch_item.value.type, g.no_context, [], (key, branch), branch_item.complexity_factor)]
end

function get_candidates_for_known_var(key, branch, branch_item, g::ContextualGrammar)
    candidates = [
        BlockPrototype(
            EnumerationState(Hole(branch_item.value.type, g.no_context), empty_context, [], 1.0, 0, true),
            branch_item.value.type,
            [],
            (key, branch),
            branch_item.complexity_factor,
            true,
        ),
    ]
    for (p, t, context, ll, i) in following_expressions(g.no_context, branch_item.value.type)
        skeleton = p
        path = []
        for (j, arg_type) in enumerate(arguments_of_type(t))
            if j == i
                skeleton = Apply(skeleton, FreeVar(branch_item.value.type, key))
                if !isempty(path)
                    path = vcat([LeftTurn()], path)
                end
            else
                skeleton = Apply(skeleton, Hole(arg_type, g.contextual_library[p][j]))
                if isempty(path)
                    path = [RightTurn()]
                else
                    path = vcat([LeftTurn()], path)
                end
            end
        end
        state = EnumerationState(skeleton, context, path, 1.0 + ll + g.no_context.log_variable, 1, false)
        push!(
            candidates,
            BlockPrototype(
                state,
                return_of_type(t),
                [j == i ? (key, branch) : nothing for j = 1:length(arguments_of_type(t))],
                nothing,
                branch_item.complexity_factor,
                false,
            ),
        )
    end
    candidates
end

state_finished(state::EnumerationState) =
    if isa(state.skeleton, Hole)
        false
    else
        isempty(state.path)
    end
