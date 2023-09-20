# Installation of HOL Light #


1. Install Opam, the OCaml package manager (as root). See "https://opam.ocaml.org/doc/Install.html" for fuller details, but for example

        sudo apt-get install opam    (on Debian-based Linux systems)
        brew install opam            (on Mac OS X using Homebrew)

2. Use opam to install appropriate versions of ocaml and camlp5.

        opam init
        eval `opam env`
        opam switch create 4.14.0
        eval `opam env`
        opam pin add camlp5 8.00.04
        opam install num camlp5 camlp-streams ocamlfind

3. Clone the HOL Light repo and build

        git clone https://github.com/jrh13/hol-light.git
        cd ./hol-light
        make

4. Inside the HOL Light directory, start OCaml and load HOL Light

        ocaml
         [...now inside Ocaml]
        #use "hol.ml";;

That takes 1-2 minutes to load, depending on your machine speed. You are then in an OCaml toplevel with the HOL Light basics loaded.


