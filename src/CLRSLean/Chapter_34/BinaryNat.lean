import CLRSLean.Chapter_34.BinaryNat.Length
import CLRSLean.Chapter_34.BinaryNat.Machine

/-!
# Compact natural-number fields for strict Chapter 34 languages

This facade exports a canonical big-endian semantic codec, logarithmic
physical-size bounds, a fixed unary-length encoder, and a fixed canonicality
validator.  It intentionally does not expose a binary-to-unary decoder:
expanding an `m`-bit value may require `2 ^ m` output cells.
-/
