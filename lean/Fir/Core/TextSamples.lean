import Fir.Core.Text

/-!
The samples that check the core dialect's text: one instance of every core
op, which decodes from its name and attributes at its own types.
`FirTest.CoreText` tests the spellings of ops and types that read back, or
do not. The text-format
chapter proves the same for every op instance and every type; these
checks run the definitions themselves, so a slip in a definition shows
at once. Later sections use the samples too, to check each op's poison
class, its rules and its effects.
-/

namespace Fir.Core

/-- One instance of every core op, used to check the encoding below and the
poison classes, rules and effects in later sections. -/
def samples : List Op :=
  [.const 8 (-128), .const 1 1, .const 1 0, .const 7 5, .add 32 {}, .add 32 { nuw := true },
   .sub 16 { nsw := true }, .mul 64 { nuw := true, nsw := true },
   .sdiv 32 true, .udiv 32 false, .srem 8, .urem 8, .and 1, .or 33, .xor 128,
   .shl 32, .lshr 32, .ashr 32, .select 8, .zext 8 32, .sext 1 64, .trunc 64 7,
   .freeze 2, .poison 8, .br, .condBr, .ret [.int 32], .ret [], .unreachable,
   .call "f" [.int 8] [.int 1], .fconst 8 23 0x3f800000, .fconst 11 52 (-1), .fconst 2 1 0,
   .fconst 5 10 0x7e01] ++
  Pred.all.map (.icmp · 32) ++ FPred.all.map (.fcmp · 8 23) ++ [.fcmp .uno 15 112] ++
  [.fbin .fadd 8 23, .fbin .fsub 11 52, .fbin .fmul 5 10, .fbin .fdiv 2 1, .funary .fneg 8 7,
   .funary .fabs 15 112, .funary .sqrt 8 23, .fma 11 52, .fbin .frem 8 23, .fbin .fmod 2 1] ++
  [.toBits 8 23, .ofBits 11 52, .toBits 2 1, .ofBits 15 112] ++
  [.sitofp 32 8 23, .uitofp 64 11 52, .sitofp 1 5 10, .uitofp 128 15 112, .sitofp 7 2 1] ++
  [.fpext 8 23 11 52, .fptrunc 11 52 8 23, .fpext 5 10 15 112, .fptrunc 8 7 5 10, .fptrunc 5 10 8 7] ++
  [.ptradd 0 64, .ptradd 1 8, .ptradd maxMemory 1]

-- Decoding an op's encoding, at its own types, gives the op back.
#guard samples.all fun o => Op.decode o.name o.attrs o.sig o.returnTypes == some o

-- `FirTest.CoreText` checks that each type reads back from its spelling, and
-- that misspelled ops and types do not decode.

end Fir.Core
