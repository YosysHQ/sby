#![allow(clippy::needless_range_loop)]

use std::{fs, mem::replace, path::PathBuf};

use clap::{Parser, ValueEnum};
use color_eyre::eyre::bail;

use flussab_aiger::binary;

pub mod aig_eval;
pub mod care_graph;
pub mod util;

/// AIG counter example minimization
#[derive(clap::Parser)]
#[command(author, version, about, long_about = None, help_template="\
{before-help}{name} {version}
{author-with-newline}{about-with-newline}
{usage-heading} {usage}

{all-args}{after-help}
")]
pub struct Options {
    /// Input AIGER file
    aig: PathBuf,
    /// Input AIGER witness file
    witness: PathBuf,
    /// Output AIGER witness file
    output: PathBuf,

    /// Verify the minimized counter example
    #[clap(long, default_value = "cex")]
    verify: VerificationOption,

    /// Minimize latch initialization values
    ///
    /// Without this option the latch initialization values of the witness file are assumed to be
    /// fixed and will remain as-is in the minimized witness file.
    ///
    /// Note that some tools (including the current Yosys/SBY flow) do not use AIGER native latch
    /// initialization but instead perform initialization using inputs in the first frame.
    #[clap(long)]
    latches: bool,
}

#[derive(Copy, Clone, ValueEnum)]
enum VerificationOption {
    /// Skip verification
    Off,
    /// Verify the counter example
    Cex,
    /// Verify the counter example and that it is minimal (expensive)
    Full,
}

fn main() -> color_eyre::Result<()> {
    let options = Options::parse();

    color_eyre::install()?;

    let file_input = fs::File::open(options.aig)?;
    let file_witness = fs::File::open(options.witness)?;
    let file_output = fs::File::create(options.output)?;

    let mut writer_output = flussab::DeferredWriter::from_write(file_output);

    let mut read_witness_owned = flussab::DeferredReader::from_read(file_witness);
    let read_witness = &mut read_witness_owned;

    let aig_reader = binary::Parser::<u32>::from_read(file_input, binary::Config::default())?;

    let aig = aig_reader.parse()?;

    let mut offset = 0;
    offset = flussab::text::next_newline(read_witness, offset);

    if offset == 2 {
        read_witness.advance(replace(&mut offset, 0));
        offset = flussab::text::next_newline(read_witness, offset);
        read_witness.advance(replace(&mut offset, 0));

        offset = flussab::text::next_newline(read_witness, offset);
    }

    if offset != aig.latches.len() + 1 {
        bail!(
            "unexpected number of initial latch states, found {} expected {}",
            offset.saturating_sub(1),
            aig.latches.len()
        );
    }

    let latch_init = read_witness.buf()[..aig.latches.len()]
        .iter()
        .copied()
        .map(util::parse_input_bit)
        .collect::<Result<Vec<_>, _>>()?;

    read_witness.advance(replace(&mut offset, 0));

    let mut frame_inputs = vec![];

    loop {
        offset = flussab::text::next_newline(read_witness, offset);

        if matches!(read_witness.buf().first(), None | Some(b'.') | Some(b'#')) {
            read_witness.check_io_error()?;
            break;
        }

        if offset != aig.input_count + 1 {
            bail!(
                "unexpected number of input bits, found {} expected {}",
                offset.saturating_sub(1),
                aig.input_count
            );
        }

        frame_inputs.push(
            read_witness.buf()[..aig.input_count]
                .iter()
                .copied()
                .map(util::parse_input_bit)
                .collect::<Result<Vec<_>, _>>()?,
        );
        read_witness.advance(replace(&mut offset, 0));
    }

    care_graph::minimize(
        &aig,
        &latch_init,
        &frame_inputs,
        &mut writer_output,
        &care_graph::MinimizationOptions {
            fixed_init: !options.latches,
            verify: match options.verify {
                VerificationOption::Off => None,
                VerificationOption::Cex => Some(care_graph::Verification::Cex),
                VerificationOption::Full => Some(care_graph::Verification::Full),
            },
        },
    )?;

    Ok(())
}
