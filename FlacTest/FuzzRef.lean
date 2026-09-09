import Flac.Native.Stream

/-!
# The reference writer, deliberately left unswapped

`Flac.Spec.Emit`'s `@[csimp] Unchecked_encode_eq_emitFast` rewrites every call
to `Stream.Unchecked.encode` in a module elaborated after it. `Flac.Native.Codec`
imports that swap so the shipped entry points get the `ByteArray` emitter, and
anything importing `Codec` inherits it — `FlacTest.FuzzGen` among them.

That is right for shipped code and wrong for a differential oracle. The fuzz
harness pairs `vlean_unchecked_encode` against `vinyl_emit_fast` precisely to
run two *different* implementations on the same input; under the swap both
sides become `Emit.emitFast` and the comparison is a function against itself.

This module imports `Flac.Native.Stream` alone, so the swap is not in scope
when its body is compiled and the export binds the `List Bool` reference
writer. `fuzz/cov/twins.py` pins the pair in `DISTINCT_EXPORT_PAIRS` and
reports `FAIL(ALIASED)` if the two callee sets ever intersect again.
-/

@[export vlean_unchecked_encode]
def fzUncheckedEncode := Flac.Stream.Unchecked.encode
