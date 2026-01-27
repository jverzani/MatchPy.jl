using Documenter, MatchPy

makedocs(sitename="MatchPy Documentation",
         format = Documenter.HTML(
             prettyurls = get(ENV, "CI", nothing) == "true"
         )
         )
