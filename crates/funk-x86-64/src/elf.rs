//! Reading the symbols that an object file uses but does not define.
//!
//! `funk build` links a program with the C library when the module's
//! object file references a symbol it does not define, and links it alone
//! otherwise. This module reads the symbol table of the object that `as`
//! wrote: an ELF64 little-endian relocatable file.

/// The section type of a symbol table.
const SHT_SYMTAB: u32 = 2;

/// The bytes of one entry of a symbol table.
const SYM_SIZE: usize = 24;

/// The bytes of a section header.
const SH_SIZE: usize = 0x40;

/// The names of the symbols that the ELF64 object file `object` references
/// but does not define, in the order of its symbol table. An object that
/// is not ELF64 little-endian, or whose headers point outside it, is an
/// error.
pub fn undefined_symbols(object: &[u8]) -> Result<Vec<String>, String> {
    if object.get(..6) != Some(b"\x7fELF\x02\x01".as_slice()) {
        return Err("the object file is not ELF64 little-endian".into());
    }
    let shnum = usize::from(half(object, 0x3c)?);
    let mut names = Vec::new();
    for i in 0..shnum {
        let sh = section(object, i)?;
        if word(sh, 4)? != SHT_SYMTAB {
            continue;
        }
        let symbols = contents(object, sh)?;
        let strtab = usize::try_from(word(sh, 0x28)?).map_err(|_| truncated())?;
        let strings = contents(object, section(object, strtab)?)?;
        for sym in symbols.as_chunks::<SYM_SIZE>().0.iter().skip(1) {
            if half(sym, 6)? != 0 {
                continue;
            }
            let name = usize::try_from(word(sym, 0)?).map_err(|_| truncated())?;
            let rest = strings.get(name..).ok_or_else(truncated)?;
            let end = rest.iter().position(|&b| b == 0).ok_or_else(truncated)?;
            if end > 0 {
                names.push(String::from_utf8_lossy(&rest[..end]).into_owned());
            }
        }
    }
    Ok(names)
}

/// The header of the `index`-th section of `object`.
fn section(object: &[u8], index: usize) -> Result<&[u8], String> {
    let shoff = xword(object, 0x28)?;
    let shentsize = usize::from(half(object, 0x3a)?);
    let at = index
        .checked_mul(shentsize)
        .and_then(|o| o.checked_add(shoff))
        .ok_or_else(truncated)?;
    slice(object, at, SH_SIZE)
}

/// The bytes of `object` that the section header `sh` points to.
fn contents<'a>(object: &'a [u8], sh: &[u8]) -> Result<&'a [u8], String> {
    slice(object, xword(sh, 0x18)?, xword(sh, 0x20)?)
}

fn truncated() -> String {
    "the object file is truncated or malformed".into()
}

fn bytes<const N: usize>(b: &[u8], at: usize) -> Result<[u8; N], String> {
    at.checked_add(N)
        .and_then(|end| b.get(at..end))
        .and_then(|s| s.try_into().ok())
        .ok_or_else(truncated)
}

fn half(b: &[u8], at: usize) -> Result<u16, String> {
    bytes(b, at).map(u16::from_le_bytes)
}

fn word(b: &[u8], at: usize) -> Result<u32, String> {
    bytes(b, at).map(u32::from_le_bytes)
}

fn xword(b: &[u8], at: usize) -> Result<usize, String> {
    let w = u64::from_le_bytes(bytes(b, at)?);
    usize::try_from(w).map_err(|_| truncated())
}

fn slice(b: &[u8], offset: usize, size: usize) -> Result<&[u8], String> {
    offset
        .checked_add(size)
        .and_then(|end| b.get(offset..end))
        .ok_or_else(truncated)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tools::{TempDir, assemble};

    fn undefined_in(source: &str) -> Vec<String> {
        let dir = TempDir::new_in(&std::env::temp_dir()).unwrap();
        let (s, o) = (dir.join("x.s"), dir.join("x.o"));
        std::fs::write(&s, source).unwrap();
        assemble(&s, &o).unwrap();
        undefined_symbols(&std::fs::read(&o).unwrap()).unwrap()
    }

    #[test]
    fn a_call_to_a_symbol_defined_elsewhere_is_undefined() {
        let source = "\t.text\n\t.globl\tf\nf:\n\tcall\tputs\n\tcall\tf\n\tcall\t.Ll\n\tleaq\tmemcpy(%rip), %rax\n.Ll:\tret\n";
        assert_eq!(undefined_in(source), ["puts", "memcpy"]);
    }

    #[test]
    fn an_object_that_defines_all_it_uses_has_none() {
        let source = "\t.text\n\t.globl\tf\nf:\n\tcall\tg\n\tret\ng:\tret\n";
        assert!(undefined_in(source).is_empty());
    }

    #[test]
    fn a_file_that_is_not_an_elf64_object_is_an_error() {
        assert!(undefined_symbols(b"").is_err());
        assert!(undefined_symbols(b"\x7fELF\x01\x01").is_err());
        let mut header = b"\x7fELF\x02\x01".to_vec();
        header.resize(0x40, 0);
        assert_eq!(undefined_symbols(&header), Ok(Vec::new()));
        header[0x28] = 0x40;
        header[0x3a] = 0x40;
        header[0x3c] = 1;
        assert!(undefined_symbols(&header).is_err());
        header[0x28..0x30].fill(0xff);
        assert!(undefined_symbols(&header).is_err());
    }
}
