# hacky script to parse all Julia files in all packages in General
# to Exprs and report errors
#
# Run this after registry_download.jl (so the pkgs directory is populated).

using JuliaSyntax, Logging, TerminalLoggers, ProgressLogging, Serialization

using JuliaSyntax: GreenNode

include("../test/test_utils.jl")
include("../test/fuzz_test.jl")

pkgspath = joinpath(@__DIR__, "pkgs")
source_paths = find_source_in_path(pkgspath)
file_count = length(source_paths)

exception_count = 0
mismatch_count = 0
t0 = time()
exceptions = []

all_reduced_failures = String[]

function _lowprec_commas_equiv(exprs_equal, tree)
    node_text = sourcetext(tree)
    e1 = parseall(GreenNode, node_text, ignore_errors=true)
    e2 = parseall(GreenNode, node_text, ignore_errors=true,
                  low_precedence_comma_in_brackets=true)
    e1 == e2
end

Logging.with_logger(TerminalLogger()) do
    global exception_count, mismatch_count, t0
    @withprogress for (ifile, fpath) in enumerate(source_paths)
        @logprogress ifile/file_count time_ms=round((time() - t0)/ifile*1000, digits = 2)
        text = read(fpath, String)
        expr_cache = fpath*".Expr"
        #e_ref = JuliaSyntax.fl_parseall(text)
        #e_ref = open(deserialize, fpath*".Expr")
        #@assert Meta.isexpr(e_ref, :toplevel)
        e_ref = try
            JuliaSyntax.parseall(GreenNode, text, filename=fpath, ignore_warnings=true)
        catch
            continue
        end
        try
            e1 = JuliaSyntax.parseall(GreenNode, text, filename=fpath, ignore_warnings=true, low_precedence_comma_in_brackets=true)
            if e1 != e_ref
                source = SourceFile(text, filename=fpath)
                e1sn = SyntaxNode(source, e1)
                mismatch_count += 1
                failing_source = sprint(context=:color=>true) do io
                    for c in reduce_tree(e1sn, equals_ref_parse=_lowprec_commas_equiv)
                        JuliaSyntax.highlight(io, c.source, range(c), context_lines_inner=5)
                        println(io, "\n")
                    end
                end
                reduced_failures = reduce_text.(reduce_tree(text, equals_ref_parse=_lowprec_commas_equiv),
                                                parsers_fuzzy_disagree)
                append!(all_reduced_failures, reduced_failures)
                @error("Parsers succeed but disagree",
                       fpath,
                       failing_source=Text(failing_source),
                       reduced_failures,
                       )
            end
        catch err
            err isa InterruptException && rethrow()
            ex = (err, catch_backtrace())
            push!(exceptions, ex)

            exception_count += 1
            parse_to_syntax = "success"
            try
                JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, code)
            catch err2
                parse_to_syntax = "fail"
            end
            @error "Parse failed" fpath exception=ex parse_to_syntax
        end
    end
end

t_avg = round((time() - t0)/file_count*1000, digits = 2)

println()
@info """
    Finished parsing $file_count files.
        $(exception_count) failures compared to reference parser
        $(mismatch_count) Expr mismatches
        $(t_avg)ms per file"""

open(joinpath(@__DIR__, "reduced_failures.jl"), write=true) do io
    for str in all_reduced_failures
        println(io, repr(str))
    end
    for str in all_reduced_failures
        println(io, "#------------------------------")
        println(io, str)
        println(io)
    end
end
