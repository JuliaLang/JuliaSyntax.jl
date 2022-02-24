using Tokenize
using BenchmarkTools
using Printf

function speed_test()
    tot_files = 0
    tot_tokens = 0
    tot_errors = 0
    basedir = dirname(Base.find_source_file("int.jl"))
    for dir in (basedir, Sys.STDLIB)
        for (root, dirs, files) in walkdir(dir)
            for file in files
                if endswith(file, ".jl")
                    tot_files += 1
                    file = joinpath(root, file)
                    str = read(file, String)::String
                    l = tokenize(str)
                    while !Tokenize.Lexers.eof(l)
                        t = Tokenize.Lexers.next_token(l)
                        tot_tokens += 1
                        if Tokens.iserror(t.kind)
                            tot_errors += 1
                        end
                    end
                end
            end
        end
    end
    tot_files, tot_tokens, tot_errors
end

tot_files, tot_tokens, tot_errors = speed_test()
tot_time_token = @belapsed speed_test()
println("Lexed ", tot_files, " files, with a total of ", tot_tokens,
        " tokens with ", tot_errors, " errors")
println("Time Token: ", @sprintf("%3.4f", tot_time_token), " seconds")
