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
  Pred.all.map (.icmp · 32) ++ FPred.all.map (.fcmp · {} 8 23) ++
  [.fcmp .uno { nnan := true, ninf := true, nsz := true } 15 112] ++
  [.fbin (.fadd .rne) {} 8 23, .fbin (.fsub .rtz) { nnan := true } 11 52,
   .fbin (.fmul .rna) { ninf := true } 5 10,
   .fbin (.fdiv .rtp) { nsz := true, contract := true, reassoc := true } 2 1, .funary .fneg {} 8 7,
   .funary .fabs { nsz := true } 15 112, .funary (.sqrt .rtn) { nnan := true, ninf := true } 8 23,
   .fma { nnan := true, ninf := true, nsz := true, contract := true, reassoc := true } .rne 11 52,
   .fma { nnan := true } .rtz 8 23,
   .fbin .frem { nnan := true } 8 23, .fbin .fmod { ninf := true, nsz := true } 2 1] ++
  [.toBits 8 23, .ofBits 11 52, .toBits 2 1, .ofBits 15 112] ++
  [.sitofp .rne 32 8 23, .uitofp .rne 64 11 52, .sitofp .rtz 1 5 10, .uitofp .rtp 128 15 112,
   .sitofp .rna 7 2 1] ++
  [.fpext 8 23 11 52, .fptrunc .rne 11 52 8 23, .fpext 5 10 15 112, .fptrunc .rtn 8 7 5 10,
   .fptrunc .rtz 5 10 8 7] ++
  [.ptradd 0 64, .ptradd 1 8, .ptradd maxMemory 1] ++
  [.fieldAddr "pair" 1 0 none, .fieldAddr "row" 0 1 (some 64), .fieldAddr "a b" 3 maxMemory (some 1)] ++
  [.alloca .stack (.int 32) 1 none 0, .alloca .stack (.int 8) 12 (some 4) 1,
   .alloca .heap (.ptr 2) 0 (some 3) maxMemory, .alloca .global (.float 8 23) 2 none 0] ++
  [.load .nonatomic 32 none 0, .load .nonatomic 1 (some 4) 1, .load .seqCst 128 (some 3) maxMemory,
   .load .acqRel 8 none 0] ++
  [.store .nonatomic 32 none 0, .store .nonatomic 1 (some 4) 1,
   .store .release 128 (some 3) maxMemory, .store .monotonic 8 none 0] ++
  [.loadPtr .nonatomic 0 none 0, .loadPtr .nonatomic 1 (some 4) 0,
   .loadPtr .seqCst maxMemory (some 3) 1, .storePtr .nonatomic 0 none 0,
   .storePtr .nonatomic 0 (some 2) 1, .storePtr .release maxMemory none maxMemory] ++
  [.loadFloat .nonatomic 8 23 none 0, .loadFloat .nonatomic 2 1 (some 4) 1,
   .loadFloat .seqCst 15 112 (some 3) maxMemory, .storeFloat .nonatomic 11 52 none 0,
   .storeFloat .nonatomic 5 10 (some 2) 1, .storeFloat .release 1 0 none maxMemory] ++
  [.fptosi 8 23 32, .fptoui 11 52 64, .fptosi 5 10 1, .fptoui 15 112 128, .fptosi 2 1 7] ++
  [.memCopy .copy .nonatomic 64 0, .memCopy .move .nonatomic 8 1,
   .memCopy .copy .seqCst 1 maxMemory, .memCopy .move .acquire 128 0] ++
  [.memSet .nonatomic 8 64 0, .memSet .nonatomic 16 8 1, .memSet .seqCst 1 1 maxMemory]

-- Decoding an op's encoding, at its own types, gives the op back.
#guard samples.all fun o => Op.decode o.name o.attrs o.sig o.returnTypes == some o

-- `FirTest.CoreText` checks that each type reads back from its spelling, and
-- that misspelled ops and types do not decode.

end Fir.Core
