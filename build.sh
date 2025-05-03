set -u pipefail

dune clean
dune build
dune runtest