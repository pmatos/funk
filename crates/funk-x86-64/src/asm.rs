//! Assembly text in GNU `as`'s AT&T syntax (ADR-2026-10-30-1229): the
//! registers and stack slots that instructions name, and the writer that
//! collects the lines of a file.
//!
//! AT&T syntax writes every register with `%`, so a symbol never reads as a
//! register, whatever its name.

use std::fmt::{self, Write};

/// A 64-bit general-purpose register, named at each operand size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reg {
    Rax,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    R8,
    R9,
    R11,
}

impl Reg {
    /// The register's name at `bits` (8, 16, 32 or 64), with its `%`.
    pub fn at(self, bits: u32) -> &'static str {
        let names = match self {
            Reg::Rax => ["%al", "%ax", "%eax", "%rax"],
            Reg::Rcx => ["%cl", "%cx", "%ecx", "%rcx"],
            Reg::Rdx => ["%dl", "%dx", "%edx", "%rdx"],
            Reg::Rsi => ["%sil", "%si", "%esi", "%rsi"],
            Reg::Rdi => ["%dil", "%di", "%edi", "%rdi"],
            Reg::R8 => ["%r8b", "%r8w", "%r8d", "%r8"],
            Reg::R9 => ["%r9b", "%r9w", "%r9d", "%r9"],
            Reg::R11 => ["%r11b", "%r11w", "%r11d", "%r11"],
        };
        match bits {
            8 => names[0],
            16 => names[1],
            32 => names[2],
            64 => names[3],
            _ => panic!("no {bits}-bit register"),
        }
    }

    /// The register's 64-bit name.
    pub fn q(self) -> &'static str {
        self.at(64)
    }
}

/// An 8-byte slot of a frame, addressed from `%rbp`: the operand
/// `disp(%rbp)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mem {
    /// The displacement from `%rbp`.
    pub disp: i32,
}

impl fmt::Display for Mem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(%rbp)", self.disp)
    }
}

/// The lines of an assembly file, written in order.
#[derive(Debug, Default)]
pub struct Asm {
    text: String,
}

impl Asm {
    /// An empty file.
    pub fn new() -> Asm {
        Asm::default()
    }

    /// An instruction: a mnemonic and its operands, separated by commas.
    pub fn ins(&mut self, mnemonic: &str, operands: fmt::Arguments<'_>) {
        let _ = writeln!(self.text, "\t{mnemonic}\t{operands}");
    }

    /// An instruction with no operands.
    pub fn ins0(&mut self, mnemonic: &str) {
        let _ = writeln!(self.text, "\t{mnemonic}");
    }

    /// A directive, such as `.text`, with its arguments.
    pub fn directive(&mut self, line: fmt::Arguments<'_>) {
        let _ = writeln!(self.text, "\t{line}");
    }

    /// A label.
    pub fn label(&mut self, name: &str) {
        let _ = writeln!(self.text, "{name}:");
    }

    /// A comment line. `text` must not hold a line break.
    pub fn comment(&mut self, text: fmt::Arguments<'_>) {
        let _ = writeln!(self.text, "\t# {text}");
    }

    /// Appends text that is already assembly, such as the runtime.
    pub fn raw(&mut self, text: &str) {
        self.text.push_str(text);
    }

    /// The file's text.
    pub fn finish(self) -> String {
        self.text
    }
}

/// The section note that marks a file's code as needing no executable
/// stack. Without it, `ld` warns and makes the stack executable.
pub const NO_EXEC_STACK: &str = "\t.section\t.note.GNU-stack,\"\",@progbits\n";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registers_are_named_at_each_size() {
        assert_eq!(Reg::Rax.at(8), "%al");
        assert_eq!(Reg::Rdi.at(16), "%di");
        assert_eq!(Reg::R9.at(32), "%r9d");
        assert_eq!(Reg::Rsi.q(), "%rsi");
        assert_eq!(Mem { disp: -16 }.to_string(), "-16(%rbp)");
    }

    #[test]
    fn lines_are_written_in_order() {
        let mut a = Asm::new();
        a.label("f");
        a.ins(
            "movq",
            format_args!("{}, {}", Reg::Rdi.q(), Mem { disp: -8 }),
        );
        a.ins0("ret");
        assert_eq!(a.finish(), "f:\n\tmovq\t%rdi, -8(%rbp)\n\tret\n");
    }
}
