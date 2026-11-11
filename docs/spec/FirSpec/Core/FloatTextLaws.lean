import VersoManual
import Fir.Core.FloatTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on float constants read back, which
renders `Fir.Core.FloatTextLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float constants read back: readable blocks" =>

:::moduleDocs (fingerprint := "15271438408105338152")
:::

:::readable Fir.Core.hexValue_replicate_zero Fir.Core.readFloatLit_hexLit (pin := Fir.Text.hexValue) (pin := Fir.Core.hexLit) (pin := Fir.Core.readFloatLit) (fingerprint := "13659805135410042404")
*Theorem: leading zeros add nothing to hexadecimal digits.* The value of
$`k` zeros followed by the digits $`\mathit{ds}` is the value of
$`\mathit{ds}`.

*Theorem: hexadecimal bits read back.* For all bits $`b` of
$`\mathsf{float}\langle e,m \rangle`,
$`\mathrm{readlit}_{e,m}(\mathrm{hexlit}(b)) = b`. The digits of $`b` are
at most $`\lceil (1+e+m)/4 \rceil`, since $`b < 2^{1+e+m} \le
16^{\lceil (1+e+m)/4 \rceil}`, so the padding makes exactly that many, and
their value is $`b`.
:::

:::readable Fir.Core.mem_padDigits Fir.Core.padDigits_ne_nil Fir.Core.isDigit_of_padDigits (pin := Fir.Core.padDigits) (fingerprint := "6934681738737155414")
*Theorems: padded digits.* Each character of $`\mathrm{pad}_k(\mathit{ds})`
is `0` or a character of $`\mathit{ds}`; padding digits that are not empty
gives digits that are not empty; and each character of the padded decimal
digits of a number is a decimal digit.
:::

:::readable Fir.Core.decimalLayout_valid Fir.Core.hexLit_valid Fir.Core.decimalLit_valid Fir.Core.floatLit_valid (pin := Fir.FloatLit.valid) (pin := Fir.Core.decimalLayout) (pin := Fir.Core.decimalLit) (pin := Fir.Core.floatLit) (fingerprint := "12453137484527690534")
*Theorems: every spelling can be written.* A decimal that
$`\mathrm{layout}` gives, hexadecimal bits, a decimal that
$`\mathrm{declit}` gives, and so the spelling $`\mathrm{floatlit}(b)` of
every float, are
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[writable]
float literals: a decimal's fraction is one or more decimal digits, and
hexadecimal bits are one or more lowercase hexadecimal digits.
:::

:::readable Fir.Core.decodeFloatLit_floatLit Fir.Core.floatLit_of_decode (pin := Fir.Core.floatLit) (pin := Fir.Core.decodeFloatLit) (fingerprint := "16783646121343554582")
*Theorem: the spelling of a float reads back as it.* For all bits $`b` of
$`\mathsf{float}\langle e,m \rangle`,
$`\mathrm{decodelit}_{e,m}(\mathrm{floatlit}_{e,m}(b)) = b`. The spelling
is a decimal only when that decimal reads back as $`b`, and hexadecimal
bits always do.

*Theorem: a literal that decodes is the spelling of its bits.* If
$`\mathrm{decodelit}_{e,m}(l) = b`, then $`\mathrm{floatlit}_{e,m}(b) = l`,
since $`\mathrm{decodelit}` checks exactly that. These are the two laws
that the core dialect's text asks of a float constant.
:::
