# Project compilation guide (CoqIDE).

Firstly, make sure that your bash is using the Coq set of commands provided by CoqIDE. To do so, you can append the following line to your `.bash_profile` (replace `<your_CoqIDE_version>` accordingly):
`export PATH="$PATH:/Applications/CoqIDE_<your_CoqIDE_version>.app/Contents/Resources/bin"`

Then, either restart your shell or run `source <path_to_your_bash_profile>/.bash_profile`.

Finally, simply run `coq_makefile -f _CoqProject -o makefile && make` when inside the `src` folder of the project.

# Project structure.
`src/Basics` => Auxiliary modules used as a foundation for the rest of the project. <br/>
`src/Languages` => Custom frame stack style programming languages used for program equivalence analysis. <br/>
`src/ProgramEquivalence/Proofs` => Program equivalence proofs. <br/>
`src/ProgramEquivalence/Tactics` => Custom Coq tactics used for proving program equivalence. <br/>
`src/Programs` => Custom program definitions.
