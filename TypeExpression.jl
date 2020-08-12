module TypeExpression
##=========common head===============
using HMRowUnification
using Sequent
using MLStyle

ImD = Base.ImmutableDict
struct Store{K, O}
    unbox :: ImD{K, O}
end

# given σ ∈ Store{K, O} where K, O
# 'σ[k => v]' add a scoped pair k=>v and returns a new store
# where the old one is not affected.
function Store{K, O}() where {K, O}
    Store(ImD{K, O}())
end
Base.getindex(s::Store{K, O}, x::Pair{K, A}...) where {K, O, A<:O} =
    let im = s.unbox
        for each in x
            im = ImD(im, each)
        end
        Store(im)
    end
Base.getindex(s::Store{K, O}, x::K) where {K, O} = s.unbox[x]
##===========auxiliaries==================

@active T(x) begin
    @match x begin
        App(Nom(:Type), x) => Some(x)
        _ => nothing
    end
end

(::Type{T})(x::HMT) = App(Nom(:Type), x)

(f::HMT)(arg::HMT) = App(f, arg)
(a::HMT) ↦ (r::HMT) = Arrow(a, r)

σ₀ = Store{Symbol, HMT}()[
    :int => T(Nom(:int)),
    :str => T(Nom(:str))
]

##=============semantics===================
tr_type = @sequent TType begin
    σ ⊢ₜ t => t′
    σ ⊢ₜ :(Type[$t]) => T(t′)
end

tr_app = @sequent TAPP begin
    σ ⊢ₜ op => T(op_t)
    σ ⊢ₜ args .=> [T(arg_t) for arg_t in args_t]
    
    σ ⊢ₜ :($op[$(args...)]) =>
        length(args) == 1 ?
        T(op_t(args_t[1])) :
        let args_t = Tuple(args_t)
            T(op_t(Tup(args_t)))
        end
end

tr_tup = @sequent TTUP begin
    σ ⊢ₜ args .=> [T(arg_t) for arg_t in args_t]
    σ ⊢ₜ Expr(:tuple, args...) => 
        let args_t = Tuple(args_t)
            T(Tup(args_t))
        end
end

tr_sym = @sequent TSYM begin
    σ ⊢ₜ a::Symbol => σ[a]
end

tr_arrow = @sequent TARROW begin
    σ ⊢ₜ f => T(ft)
    σ ⊢ₜ arg => T(argt)
    σ ⊢ₜ :($f ↦ $arg) => T(ft ↦ argt)
end

tr_forall = @sequent TFORALL begin
    bounds = Pair{Symbol, HMT}[s=>T(Fresh(s)) for s in syms]
    σ[bounds...] ⊢ₜ t => T(t′)
    σ ⊢ₜ :(forall[$([s::Symbol for s in syms]...)][$t]) => 
        let freshvars = Tuple(syms)
            T(Forall(freshvars, t′))
        end
end

##=============codegen for rules==========
# the order of rules are always sigficant, because given
# 
#      Judge1
#      Judge2
#   ________________
#     Ctx ⊢ Input => Output
#
# we will do pattern matching for (Ctx, Input).
# Only the first rule matching in the given order applies.
# For instance, `tr_forall` should be prior than `tr_app`,
# as the pattern
#    :($op[$(args...)])
# covers
#    :(forall[$([s::Symbol for s in syms]...)][$t])

@semantics [
    tr_forall,
    tr_type,
    tr_app,
    tr_tup,
    tr_sym,
    tr_arrow
]
##==========================================
# after codegen, we have ⊢ₜ

println(σ₀ ⊢ₜ :(forall[a, b][a ↦ (int, b)]))
# Type (forall a b.a->{int, b})

end # module