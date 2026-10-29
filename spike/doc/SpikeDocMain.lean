import VersoManual
import SpikeDoc

open Verso.Genre Manual

def main := manualMain (%doc SpikeDoc) (config := { emitTeX := false, emitHtmlSingle := true, emitHtmlMulti := false })
