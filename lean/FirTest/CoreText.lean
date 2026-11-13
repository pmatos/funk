import Fir

/-!
Tests of the core dialect's text (`Fir.Core.Text`): each core type reads
back from its spelling, and an op or a type that is misspelled, written
with attributes it does not have or at types it does not take, does not
decode. `Fir.Core.samples` checks that every op instance reads back.
-/

namespace Fir.Core

#guard [Ty.int 1, .int 32, .int 128, .ptr 0, .ptr 1, .ptr maxMemory].all fun t =>
  Ty.decode t.attr == some t
#guard Ty.decode (.app "ptr" [.int 0]) == none && Ty.decode (.app "ptr" [.int (-1)]) == none
#guard Ty.decode (.app "ptr" [.int (maxMemory + 1)]) == none && Ty.decode (.app "ptr" []) == none
#guard Ty.decode (.app "ptr" [.int 1, .int 2]) == none && Ty.decode (.app "ptr" [.word "x"]) == none
#guard [Ty.float 5 10, .float 8 7, .float 8 23, .float 11 52, .float 15 112, .float 2 1,
  .float 5 2, .float 2 (maxWidth - 3)].all fun t => Ty.decode t.attr == some t
#guard Ty.decode (.word "f32") == some (.float 8 23) && Ty.decode (.word "bf16") == some (.float 8 7)
#guard Ty.decode (.app "float" [.int 5, .int 2]) == some (.float 5 2)
#guard Ty.decode (.app "float" [.int 8, .int 23]) == none
#guard Ty.decode (.app "float" [.int (-1), .int 3]) == none
#guard Ty.decode (.app "float" [.int 2, .int (maxWidth - 2)]) == none
#guard Ty.decode (.app "float" [.int 5]) == none && Ty.decode (.app "f16" []) == none
#guard Ty.decode (.word "float") == none && Ty.decode (.word "f8") == none
#guard Ty.decode (.app "float" [.int 1, .int 1]) == some (.float 1 1)
#guard Ty.decode (.word "i032") == none && Ty.decode (.word "u8") == none
#guard Op.decode "const" [.int 128] [] [.int 8] == none
#guard Op.decode "add" [.word "nsw", .word "nuw"] [.int 8, .int 8] [.int 8] == none
#guard Op.decode "add" [] [.int 8, .int 16] [.int 8] == none
#guard Op.decode "const" [.word "true"] [] [.int 1] == some (.const 1 1)
#guard Op.decode "const" [.int 1] [] [.int 1] == none && Op.decode "const" [.int (-1)] [] [.int 1] == none
#guard Op.decode "const" [.word "true"] [] [.int 8] == none
#guard Op.decode "icmp" [.word "slt"] [.int 8, .int 8] [.int 1] == some (.icmp .slt 8)
#guard Op.decode "icmp.slt" [] [.int 8, .int 8] [.int 1] == none
#guard Op.decode "poison" [] [] [.int 1] == some (.poison 1)
#guard Op.decode "poison" [.int 0] [] [.int 8] == none && Op.decode "poison" [] [.int 8] [.int 8] == none
#guard Op.decode "poison" [] [] [] == none && Op.decode "poison" [] [] [.int 8, .int 8] == none
#guard Op.decode "poison" [] [] [.ptr 0] == none
#guard Ty.decode (.word "i16777215") == some (.int maxWidth) && Ty.decode (.word "i16777216") == none
-- A float constant is a float literal: `1.0`, `-0.0` and the quiet NaN of
-- `f32` with its sign set.
#guard Op.decode "const" [.float (.dec false 1 ['0'] none)] [] [.float 8 23] ==
  some (.fconst 8 23 0x3f800000)
#guard Op.decode "const" [.float (.dec true 0 ['0'] none)] [] [.float 8 23] ==
  some (.fconst 8 23 0x80000000)
#guard Op.decode "const" [.float (.hex "ffc00000".toList)] [] [.float 8 23] ==
  some (.fconst 8 23 0xffc00000)
#guard (Op.fconst 8 23 0xffc00000).attrs.map Attr.print == ["0xffc00000"]
-- Each bit pattern has one spelling: the bits read as an integer, the
-- bits of a number in hexadecimal and `true` do not decode.
#guard Op.decode "const" [.int 1065353216] [] [.float 8 23] == none
#guard Op.decode "const" [.float (.hex "3f800000".toList)] [] [.float 8 23] == none
#guard Op.decode "const" [.word "true"] [] [.float 8 23] == none
#guard Op.decode "const" [.int 0] [.float 8 23] [.float 8 23] == none
#guard Op.decode "fcmp" [.word "olt"] [.float 11 52, .float 11 52] [.int 1] == some (.fcmp .olt 11 52)
#guard Op.decode "fcmp" [.word "olt"] [.float 11 52, .float 8 23] [.int 1] == none
#guard Op.decode "fcmp" [.word "slt"] [.float 8 23, .float 8 23] [.int 1] == none
#guard Op.decode "fcmp" [.word "olt"] [.int 32, .int 32] [.int 1] == none
#guard Op.decode "icmp" [.word "eq"] [.float 8 23, .float 8 23] [.int 1] == none
-- A float op that rounds needs `round(rne)`; `fneg` and `fabs` take none.
#guard Op.decode "fadd" [roundAttr] [.float 8 23, .float 8 23] [.float 8 23] == some (.fbin .fadd 8 23)
#guard Op.decode "fadd" [] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "fdiv" [.app "round" [.word "rtz"]] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "fneg" [roundAttr] [.float 8 23] [.float 8 23] == none
#guard Op.decode "frem" [roundAttr] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "sqrt" [] [.float 8 23] [.float 8 23] == none
#guard Op.decode "fma" [roundAttr] [.float 8 23, .float 8 23, .float 8 23] [.float 8 23] ==
  some (.fma 8 23)
#guard Op.decode "fma" [roundAttr] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "fadd" [roundAttr] [.int 32, .int 32] [.int 32] == none
-- `sitofp` and `uitofp` take an integer of any width to a float of any
-- format, with `round(rne)`.
#guard Op.decode "sitofp" [roundAttr] [.int 33] [.float 5 10] == some (.sitofp 33 5 10)
#guard Op.decode "uitofp" [roundAttr] [.int 8] [.float 11 52] == some (.uitofp 8 11 52)
#guard Op.decode "sitofp" [] [.int 32] [.float 8 23] == none
#guard Op.decode "uitofp" [roundAttr] [.float 8 23] [.float 8 23] == none
-- `fpext` and `fptrunc` take a float to a float, of any two formats.
#guard Op.decode "fpext" [] [.float 5 10] [.float 8 23] == some (.fpext 5 10 8 23)
#guard Op.decode "fptrunc" [roundAttr] [.float 8 7] [.float 5 10] == some (.fptrunc 8 7 5 10)
#guard Op.decode "fpext" [roundAttr] [.float 8 23] [.float 11 52] == none
#guard Op.decode "fptrunc" [] [.float 11 52] [.float 8 23] == none
#guard Op.decode "fpext" [] [.int 32] [.float 11 52] == none
-- `fptosi` and `fptoui` take a float of any format to an integer of any
-- width, with no attribute.
#guard Op.decode "fptosi" [] [.float 5 10] [.int 33] == some (.fptosi 5 10 33)
#guard Op.decode "fptoui" [] [.float 11 52] [.int 1] == some (.fptoui 11 52 1)
#guard Op.decode "fptosi" [roundAttr] [.float 8 23] [.int 32] == none
#guard Op.decode "fptoui" [] [.int 32] [.int 32] == none

end Fir.Core
