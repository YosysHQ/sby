use color_eyre::eyre::bail;
use flussab::DeferredWriter;
use flussab_aiger::Lit;

pub fn unpack_lit<L: Lit>(lit: L) -> (usize, bool) {
    let lit = lit.code();
    (lit >> 1, lit & 1 != 0)
}

pub fn parse_input_bit(byte: u8) -> color_eyre::Result<Option<bool>> {
    Ok(match byte {
        b'0' => Some(false),
        b'1' => Some(true),
        b'x' => None,
        _ => bail!("unexpected input bit {byte:?}"),
    })
}

pub fn write_output_bit(writer: &mut DeferredWriter, bit: Option<bool>) {
    writer.write_all_defer_err(match bit {
        Some(false) => b"0",
        Some(true) => b"1",
        None => b"x",
    })
}
