##=========common head===============
using HMRowUnification
using Sequent
using MLStyle

@nospecialize
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

@data List{A} begin
    Nil{A} :: () => List{A}
    Cons{A} :: (A, List{A}) => List{A}
end

# from vector to List
function fromVec(x::AbstractVector{A}) where A
    a = Nil{A}()
    for i in eachindex(x)
        i = reverseind(x, i)
        e = x[i]
        a = Cons(e, a)
    end
    a
end

# from List to Expr(:block, ...)
function toBlock(x::List)
    r = Expr(:block)
    while true
        @switch x begin
        @case Nil() 
            return r
        @case Cons(h, x)
            push!(r.args, h)
            continue
        end
    end
end
# Define a pattern to handle unzip
# 
# @match [(1, :a), (2, :b)]
#    Unzip{Int, Symbol}(ints, syms) => (ints, syms)
# 
# => Int[1, 2], Symbol[:a, :b]
@active Unzip{A, B}(x) begin
    fsts = A[]
    snds = B[]
    for field in x
        @switch field begin
            @case (a, b)
            push!(fsts, a)
            push!(snds, b)
            continue

            @case _
            return nothing
        end
    end
    return (fsts, snds)
end

##================semantics===============

# ⊢ₑ does expression judgement, returns (expr, type)
er_sym = @sequent ESYM begin
    (TC, σ) ⊢ₑ e::Symbol =>
        let t = σ[e]
            :($e :: $t), t
        end
end

er_app = @sequent EAPP begin
    (TC, σ) ⊢ₑ f => (ef, tf)
    # 'a = b' performs pattern matching
    # 'a' is the pattern
    tf′ = TC.instantiate(TC.prune(tf))
    # 'Ctx ⊢ ManyOut .=> ManyOut' apply the rule to a sequence of inputs
    (TC, σ) ⊢ₑ args .=> Unzip{Any, HMT}(aexps, ats)
    tret =
        let ats = [TC.instantiate(TC.prune(a)) for a in ats]
            ats = length(ats) == 1 ? ats[1] : Tup(Tuple(ats))
            targ = TC.new_tvar()
            tret = TC.new_tvar()
            TC.unify(targ ↦ tret, tf′)
            TC.unify(targ, ats)
            tret
        end
    (TC, σ) ⊢ₑ Expr(:call, f, args...) => 
        (:($ef($(aexps...)) :: $tret), tret)
end

er_fun = @sequent ELAM begin
    true = all(args) do e; e isa Symbol end
    bindings = [p => TC.new_tvar() for p in args]
    (TC, σ[bindings...]) ⊢ₛ  body => (lst, t)
    (TC, σ) ⊢ₑ Expr(:function, arg && Expr(:tuple, args...), body) => 
        begin
            argtypes = [it.second for it in bindings]
            if length(argtypes) == 1
                argtype = argtypes[1]
            else
                argtype = Tup(Tuple(argtypes))
            end
        
            Expr(:function, arg, toBlock(lst)), (argtype ↦ t)
        end

end

const Lit = Union{AbstractString, Number}

er_lit = @sequent ELIT begin
    (TC, σ) ⊢ₑ e::Lit =>
        let t =
            if e isa AbstractString
                Nom(:str)
            elseif e isa Integer
                Nom(:int)
            elseif e isa AbstractFloat
                Nom(:float)
            else
                error("unknown")
            end
            :($e :: $t), t
        end
end

sr_let = @sequent SLET begin
    E = Tup(Tuple(TC.tctx))
    (TC, σ) ⊢ₑ exp => (exp′, texp)
    FV = collect(setdiff(ftv(TC.prune(texp)), ftv(TC.prune(E))))
    tbind =
        isempty(FV) ?
        texp :
        let vs = map(FV) do i
                v = Symbol("'a", i)
                TC.unify(Var(Refvar(i)), Fresh(v))
                v
            end
            Forall(Tuple(vs), texp)
        end

    (TC, σ[e => tbind]) ⊢ₛ tl => (tl′, ttl)
    (TC, σ) ⊢ₛ Cons(:($(e::Symbol) = $exp), tl) =>
        (Cons(:($e :: $tbind = $exp′), tl′), ttl)
end

sr_ret = @sequent SReturn begin    
    (TC, σ) ⊢ₑ hd => (hd′, thd)
    (TC, σ) ⊢ₛ Cons(hd, Nil()) =>
        (Cons(hd′, Nil{Any}()), thd)
end

sr_b1 = @sequent SB1 begin
    (TC, σ) ⊢ₛ fromVec(stmts) => res
    (TC, σ) ⊢ₛ Expr(:block, stmts...) => res
end

sr_b2 = @sequent SB2 begin
    (TC, σ) ⊢ₛ tl => (res, res_t)
    (TC, σ) ⊢ₛ Cons(ln::LineNumberNode, tl) => (Cons(ln, res), res_t)
end

sr_act = @sequent SAction begin
    (TC, σ) ⊢ₑ hd => (hd′, _)
    (TC, σ) ⊢ₛ tl => (tl′, ttl)
    (TC, σ) ⊢ₛ Cons(hd, tl) =>
        (Cons(hd′, tl′), ttl)
end

@semantics [
    er_sym,
    er_app,
    er_fun,
    er_lit,
    sr_b1,
    sr_b2,
    sr_ret,
    sr_let,
    sr_act
]


##===========execution============
ts = HMT[]
TC = mk_tcstate(ts)
ex, t = ((TC, σ₀) ⊢ₛ quote
    x = function (x, y)
        x
    end
    x(1, (function(x) x end)(1))
end)

@info :inferred_type TC.prune(t)
println("generate implicitly typed code:")

prune_ex!(ex) =
    @switch ex begin
    @case Expr(:(::), a, b)
        prune_ex!(a)
        ex.args[2] = TC.prune(b)
        nothing
    @case Expr(_, exprs...)
        foreach(prune_ex!, exprs)
    @case _
        nothing
    end

ex = toBlock(ex)
prune_ex!(ex)
ex |> println
#=
┌ Info: inferred_type
└   TC.prune(t) = int
generate implicitly typed code:
begin
    #= /home/tainez/github/SequentExamples/HM.jl:221 =#
    x::forall ##a2#7610 ##a1#7611.{##a1#7611, ##a2#7610}->##a1#7611 = function (x, y)
            #= /home/tainez/github/SequentExamples/HM.jl:221 =#
            #= /home/tainez/github/SequentExamples/HM.jl:222 =#
            x::##a1#7611
        end
    #= /home/tainez/github/SequentExamples/HM.jl:224 =#
    (x::forall ##a2#7610 ##a1#7611.{##a1#7611, ##a2#7610}->##a1#7611)(1::int, (function (x,)
                    #= /home/tainez/github/SequentExamples/HM.jl:224 =#
                    #= /home/tainez/github/SequentExamples/HM.jl:224 =#
                    x::int
                end)(1::int)::int)::int
end
=#