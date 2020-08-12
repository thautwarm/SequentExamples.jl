using SequentExamples
using Documenter

makedocs(;
    modules=[SequentExamples],
    authors="thautwarm <twshere@outlook.com> and contributors",
    repo="https://github.com/thautwarm/SequentExamples.jl/blob/{commit}{path}#L{line}",
    sitename="SequentExamples.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://thautwarm.github.io/SequentExamples.jl",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/thautwarm/SequentExamples.jl",
)
