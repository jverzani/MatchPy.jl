using AssociativeCommutativePatternMatching
using Combinatorics
using JET

@testset "JET" begin
    ignored_modules=(AnyFrameModule(Base), AnyFrameModule(Combinatorics))
    JET.test_package(AssociativeCommutativePatternMatching; ignored_modules)
end
