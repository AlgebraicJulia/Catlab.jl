using Pkg, Coverage

bashit(str) = run(`bash -c "$str"`)

Pkg.test("Catlab"; coverage=true)
coverage = process_folder()
open("lcov.info", "w") do io
    LCOV.write(io, coverage)
end;
bashit("find . -name *.cov -delete")

@show get_summary(coverage)