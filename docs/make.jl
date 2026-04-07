using Documenter, MatchPy

makedocs(sitename="MatchPy Documentation",
         repo = "github.com/jverzani/MatchPy.jl.git",
         format = Documenter.HTML(
             prettyurls = get(ENV, "CI", nothing) == "true"
         )
         )

# Documenter can also automatically deploy documentation to gh-pages.
# See "Hosting Documentation" and deploydocs() in the Documenter manual
# for more information.
deploydocs(
    repo = "github.com/jverzani/MatchPy.jl.git"
)
