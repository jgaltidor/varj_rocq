FROM rocq/rocq-prover:9.2

# Language server for the VsRocq VS Code extension (not included in the image).
RUN opam update && opam install -y vsrocq-language-server && opam clean -a -c -s --logs
