use flussab_aiger::{aig::OrderedAig, Lit};

use crate::util::unpack_lit;

pub trait AigValue<Context>: Copy {
    fn invert_if(self, en: bool, ctx: &mut Context) -> Self;
    fn and(self, other: Self, ctx: &mut Context) -> Self;
    fn constant(value: bool, ctx: &mut Context) -> Self;
}

pub fn initial_frame<L, V, Context>(
    aig: &OrderedAig<L>,
    state: &mut Vec<V>,
    mut latch_init: impl FnMut(usize, &mut Context) -> V,
    mut input: impl FnMut(usize, &mut Context) -> V,
    ctx: &mut Context,
) where
    L: Lit,
    V: AigValue<Context>,
{
    state.clear();
    state.push(V::constant(false, ctx));

    for i in 0..aig.input_count {
        state.push(input(i, ctx));
    }

    for i in 0..aig.latches.len() {
        state.push(latch_init(i, ctx));
    }

    for and_gate in aig.and_gates.iter() {
        let [a, b] = and_gate.inputs.map(|lit| {
            let (var, polarity) = unpack_lit(lit);
            state[var].invert_if(polarity, ctx)
        });

        state.push(a.and(b, ctx));
    }
}

pub fn successor_frame<L, V, Context>(
    aig: &OrderedAig<L>,
    state: &mut Vec<V>,
    mut input: impl FnMut(usize, &mut Context) -> V,
    ctx: &mut Context,
) where
    L: Lit,
    V: AigValue<Context>,
{
    assert_eq!(state.len(), 1 + aig.max_var_index);

    for i in 0..aig.input_count {
        state.push(input(i, ctx));
    }

    for latch in aig.latches.iter() {
        let (var, polarity) = unpack_lit(latch.next_state);
        state.push(state[var].invert_if(polarity, ctx));
    }

    state.drain(1..1 + aig.max_var_index);

    for and_gate in aig.and_gates.iter() {
        let [a, b] = and_gate.inputs.map(|lit| {
            let (var, polarity) = unpack_lit(lit);
            state[var].invert_if(polarity, ctx)
        });

        state.push(a.and(b, ctx));
    }
}

impl AigValue<()> for bool {
    fn invert_if(self, en: bool, _ctx: &mut ()) -> Self {
        self ^ en
    }

    fn and(self, other: Self, _ctx: &mut ()) -> Self {
        self & other
    }

    fn constant(value: bool, _ctx: &mut ()) -> Self {
        value
    }
}

impl AigValue<()> for Option<bool> {
    fn invert_if(self, en: bool, _ctx: &mut ()) -> Self {
        self.map(|b| b ^ en)
    }

    fn and(self, other: Self, _ctx: &mut ()) -> Self {
        match (self, other) {
            (Some(true), Some(true)) => Some(true),
            (Some(false), _) | (_, Some(false)) => Some(false),
            _ => None,
        }
    }

    fn constant(value: bool, _ctx: &mut ()) -> Self {
        Some(value)
    }
}
