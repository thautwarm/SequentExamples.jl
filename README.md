# SequentExamples

- `TypeExpression.jl`

An example shows how to describe parsing's semantics.

```julia
tr_arrow = @sequent TARROW begin
    σ ⊢ₜ f => T(ft)
    σ ⊢ₜ arg => T(argt)
    σ ⊢ₜ :($f ↦ $arg) => T(ft ↦ argt)
end
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