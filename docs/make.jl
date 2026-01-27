using Documenter, MatchPy

makedocs(sitename="MatchPy Documentation",
         repo = "github.com/jverzani/MatchPy.jl.git",
         format = Documenter.HTML(
             prettyurls = get(ENV, "CI", nothing) == "true"
         )
         )
