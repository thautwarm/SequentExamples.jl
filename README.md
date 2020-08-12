# SequentExamples

- `TypeExpression.jl`

An example shows how to describe parsing's semantics.

```julia
tr_arrow = @sequent TARROW begin
    σ ⊢ₜ f => T(ft)
    σ ⊢ₜ arg => T(argt)
    σ ⊢ₜ :($f ↦ $arg) => T(ft ↦ argt)
end

...

println(σ₀ ⊢ₜ :(forall[a, b][a ↦ (int, b)]))
# Type (forall a b.a->{int, b})
```

- `HM.jl`

An implementation of Damas-Hindley-Milner type system with syntax-directed INST and GEN.

```julia
er_sym = @sequent ESYM begin
    (TC, σ) ⊢ₑ e::Symbol =>
        let t = σ[e]
            :($e :: $t), t
        end
end
```


Usage:
```
ex, t = (TC, σ₀) ⊢ₛ quote
    x = function (x, y)
        x
    end
    x(1, (function(x) x end)(1))
end

@info :inferred_type TC.prune(t)
println("generate implicitly typed code:")
prune_ex!(ex) = @switch ex begin
    @case Expr(:(::), a, b)
        prune_ex!(a); ex.args[2] = TC.prune(b);nothing
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
    #= ./SequentExamples/HM.jl:221 =#
    x::forall 'a2 'a1.{'a1, 'a2}->'a1 = function (x, y)
            #= ./SequentExamples/HM.jl:221 =#
            #= ./SequentExamples/HM.jl:222 =#
            x::'a1
        end
    #= ./SequentExamples/HM.jl:224 =#
    (x::forall 'a2 'a1.{'a1, 'a2}->'a1)(1::int, (function (x,)
                    #= ./SequentExamples/HM.jl:224 =#
                    #= ./SequentExamples/HM.jl:224 =#
                    x::int
                end)(1::int)::int)::int
end
```