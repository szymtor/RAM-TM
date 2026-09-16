# Internal sequential RAM compiler support

`proofs/Lax759944Proofs/Legacy/` contains the former sequential RAM definitions
and compiler reasoning library, relocated into this proof package's namespace.
They are an intermediate language for existing algorithm proofs. Public RAM
concepts import the registered `Lax808846` model directly.

Source: <https://github.com/lax-archive/lax-submissions/tree/0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea/word-ram-v4-33>.
The source and this repository use Apache License 2.0. The original source is
by Jan Dreier and the contributors named in that submission. The module
headers record the namespace relocation. No machine axiom was introduced.

The two historical RAM computability predicates are copied from this
submission's previously published concepts and contain definitions only.
They support the existing simulations as an internal intermediate. They are
not the public predicates of this submission.

`LegacyRamBridge` proves that every intermediate program executes on
`Lax808846` at the same word width, on the same supplied input, with identical
output and at most one additional charged instruction.

`TapeRamBufferedSimulation.runsTo_compile` proves the reverse simulation for
all current instructions on the framed inputs used by this submission and
canonical encodings. Initialization copies the immutable input into protected
scratch cells during the measured run. Source memory occupies even cells and
scratch storage occupies odd cells at word width `v+1`. The proof preserves
indexed input, input length, sequential input, EOF, output, and termination.
Its time bound is `18*t + 6*input.length + 26`, including initialization and
the fetched terminal instruction. Input fit and scratch capacity are explicit
hypotheses of this internal compiler theorem; the public class transfers
derive them from their sufficient word-width bounds.

`TapeRamBufferedLegacy` proves that the emitted program contains only
intermediate instructions and projects its actual run to the intermediate
semantics without increasing time. `TapeRamNativeLowering` instantiates the
framing for `x.length :: x`. The complete public computability and polynomial
predicates continue to quantify over arbitrary `Lax808846.Ram.Program`.

The archive retired `lax-865980` on 2026-09-15. No dependency on that deleted
archive entry is retained in the current lakefiles.
