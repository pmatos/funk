import VersoManual
import Fir.Sum.AddressLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a sum's address obligations, which
renders `Fir.Sum.AddressLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A sum's address obligations: readable blocks" =>

:::moduleDocs (fingerprint := "9582253694569073584")
:::

:::readable Fir.Dialect.sum.lawfulAddresses (pin := Fir.LawfulDialectAddresses) (fingerprint := "16507533994475846377")
*Theorem: a sum's declarations cover addresses.* When the base's and the
extension's declarations cover addresses and rebuilds, and the extension
accepts every type that the base accepts, so do the sum's: each op meets
the obligations as an op of its own side, and mapping its results to the
sum's types changes no memory.
:::
