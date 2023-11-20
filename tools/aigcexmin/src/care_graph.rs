use std::{
    cmp::Reverse,
    collections::{BTreeSet, BinaryHeap},
    mem::{replace, take},
    num::NonZeroU32,
};

use color_eyre::eyre::bail;
use flussab::DeferredWriter;
use flussab_aiger::{aig::OrderedAig, Lit};
use zwohash::HashMap;

use crate::{
    aig_eval::{initial_frame, successor_frame, AigValue},
    util::{unpack_lit, write_output_bit},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NodeRef {
    code: Reverse<NonZeroU32>,
}

impl std::fmt::Debug for NodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("NodeRef::new").field(&self.index()).finish()
    }
}

impl NodeRef {
    const INVALID_INDEX: usize = u32::MAX as usize;
    const TRUE_INDEX: usize = Self::INVALID_INDEX - 1;
    const FALSE_INDEX: usize = Self::INVALID_INDEX - 2;

    pub const TRUE: Self = Self::new(Self::TRUE_INDEX);
    pub const FALSE: Self = Self::new(Self::FALSE_INDEX);

    pub const fn new(index: usize) -> Self {
        assert!(index < u32::MAX as usize);
        let Some(code) = NonZeroU32::new(!(index as u32)) else {
            unreachable!();
        };
        Self {
            code: Reverse(code),
        }
    }

    pub fn index(self) -> usize {
        !(self.code.0.get()) as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Gate {
    And,
    Or,
}

#[derive(Debug)]
enum NodeDef {
    Gate([NodeRef; 2]),
    Input(u32),
}

impl NodeDef {
    fn and(inputs: [NodeRef; 2]) -> Self {
        assert!(inputs[0] < inputs[1]);
        Self::Gate(inputs)
    }

    fn or(inputs: [NodeRef; 2]) -> Self {
        assert!(inputs[0] < inputs[1]);
        Self::Gate([inputs[1], inputs[0]])
    }

    fn input(id: u32) -> Self {
        Self::Input(id)
    }

    fn as_gate(&self) -> Result<(Gate, [NodeRef; 2]), u32> {
        match *self {
            NodeDef::Gate(inputs) => {
                if inputs[0] < inputs[1] {
                    Ok((Gate::And, inputs))
                } else {
                    Ok((Gate::Or, [inputs[1], inputs[0]]))
                }
            }
            NodeDef::Input(input) => Err(input),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Debug)]
enum NodeState {
    #[default]
    Unknown,
    Nonselected,
    Selected,
    Required,
}

#[derive(Debug)]
struct Node {
    def: NodeDef,
    priority: u32,
    state: NodeState,
    renamed: Option<NodeRef>,
}

impl Node {
    fn update_state(&mut self, state: NodeState) -> NodeState {
        let old_state = self.state;
        self.state = self.state.max(state);
        old_state
    }
}

#[derive(Default)]
pub struct AndOrGraph {
    find_input: HashMap<u32, NodeRef>,
    find_and: HashMap<[NodeRef; 2], NodeRef>,
    find_or: HashMap<[NodeRef; 2], NodeRef>,

    // find_renamed: HashMap<NodeRef, NodeRef>,
    nodes: Vec<Node>,
    queue: BinaryHeap<NodeRef>,
    stack: Vec<NodeRef>,

    unknown_inputs: BTreeSet<u32>,
    required_inputs: BTreeSet<u32>,
    active_node_count: usize,

    input_order: Vec<(NodeRef, u32)>,
    cache: bool,
}

impl AndOrGraph {
    pub fn input(&mut self, id: u32) -> NodeRef {
        assert!(id <= u32::MAX - 2);
        *self.find_input.entry(id).or_insert_with(|| {
            let node_ref = NodeRef::new(self.nodes.len());
            let node = Node {
                def: NodeDef::input(id),
                priority: id,
                state: NodeState::Unknown,
                renamed: None,
            };
            self.nodes.push(node);
            self.unknown_inputs.insert(id);
            node_ref
        })
    }

    pub fn and(&mut self, mut inputs: [NodeRef; 2]) -> NodeRef {
        inputs.sort_unstable();
        if inputs[1] == NodeRef::FALSE {
            NodeRef::FALSE
        } else if inputs[1] == NodeRef::TRUE || inputs[1] == inputs[0] {
            inputs[0]
        } else {
            let [a, b] = inputs;
            match inputs.map(|input| self.nodes[input.index()].def.as_gate()) {
                [Ok((Gate::And, [a0, a1])), _] if b == a0 || b == a1 => {
                    return a;
                }
                [_, Ok((Gate::And, [b0, b1]))] if a == b0 || a == b1 => {
                    return b;
                }

                [Ok((Gate::Or, [a0, a1])), _] if b == a0 || b == a1 => {
                    return b;
                }
                [_, Ok((Gate::Or, [b0, b1]))] if a == b0 || a == b1 => {
                    return a;
                }

                _ => (),
            }

            let mut mknode = || {
                let node_ref = NodeRef::new(self.nodes.len());

                let [a, b] = inputs.map(|input| self.nodes[input.index()].priority);

                let node = Node {
                    def: NodeDef::and(inputs),
                    priority: a.min(b),
                    state: NodeState::Unknown,
                    renamed: None,
                };
                self.nodes.push(node);
                node_ref
            };

            if self.cache {
                *self.find_and.entry(inputs).or_insert_with(mknode)
            } else {
                mknode()
            }
        }
    }

    pub fn or(&mut self, mut inputs: [NodeRef; 2]) -> NodeRef {
        inputs.sort_unstable();

        if inputs[1] == NodeRef::TRUE {
            NodeRef::TRUE
        } else if inputs[1] == NodeRef::FALSE || inputs[1] == inputs[0] {
            inputs[0]
        } else {
            let [a, b] = inputs;
            match inputs.map(|input| self.nodes[input.index()].def.as_gate()) {
                [Ok((Gate::Or, [a0, a1])), _] if b == a0 || b == a1 => {
                    return a;
                }
                [_, Ok((Gate::Or, [b0, b1]))] if a == b0 || a == b1 => {
                    return b;
                }

                [Ok((Gate::And, [a0, a1])), _] if b == a0 || b == a1 => {
                    return b;
                }
                [_, Ok((Gate::And, [b0, b1]))] if a == b0 || a == b1 => {
                    return a;
                }

                _ => (),
            }

            let mut mknode = || {
                let node_ref = NodeRef::new(self.nodes.len());

                let [a, b] = inputs.map(|input| self.nodes[input.index()].priority);

                let node = Node {
                    def: NodeDef::or(inputs),
                    priority: a.max(b),
                    state: NodeState::Unknown,
                    renamed: None,
                };
                self.nodes.push(node);
                node_ref
            };

            if self.cache {
                *self.find_or.entry(inputs).or_insert_with(mknode)
            } else {
                mknode()
            }
        }
    }

    pub fn pass(&mut self, target: NodeRef, shuffle: usize, mut enable_cache: bool) -> NodeRef {
        if self.cache {
            enable_cache = false;
        }

        self.nodes[target.index()].state = NodeState::Required;
        self.queue.push(target);

        let target_priority = self.nodes[target.index()].priority;

        'queue: while let Some(current) = self.queue.pop() {
            let node = &self.nodes[current.index()];
            let state = node.state;

            self.stack.push(current);

            match node.def.as_gate() {
                Ok((Gate::And, inputs)) => {
                    if enable_cache {
                        self.find_and.insert(inputs, current);
                    }
                    for input in inputs {
                        let node = &mut self.nodes[input.index()];
                        if node.update_state(state) == NodeState::Unknown {
                            self.queue.push(input);
                        }
                    }
                }
                Ok((Gate::Or, inputs)) => {
                    if enable_cache {
                        self.find_or.insert(inputs, current);
                    }
                    for input in inputs {
                        let node = &mut self.nodes[input.index()];
                        if node.update_state(NodeState::Nonselected) == NodeState::Unknown {
                            self.queue.push(input);
                        }
                    }

                    if state <= NodeState::Nonselected {
                        continue;
                    }

                    let input_priorities = inputs.map(|input| self.nodes[input.index()].priority);

                    for (i, input_priority) in input_priorities.into_iter().enumerate() {
                        if input_priority < target_priority {
                            // The other input will be false, so propagate the state
                            self.nodes[inputs[i ^ 1].index()].update_state(state);
                            continue;
                        }
                    }

                    for input in inputs {
                        let input_state = self.nodes[input.index()].state;
                        if input_state >= NodeState::Selected {
                            // One input of the or is already marked, no need to mark the other
                            continue 'queue;
                        }
                    }

                    // Mark the highest priority input
                    let input = inputs[(input_priorities[1] > input_priorities[0]) as usize];
                    self.nodes[input.index()].update_state(NodeState::Selected);
                }
                Err(_input) => (),
            }
        }

        if enable_cache {
            self.cache = true;
        }

        let mut stack = take(&mut self.stack);

        self.active_node_count = stack.len();

        self.unknown_inputs.clear();

        for current in stack.drain(..).rev() {
            let node = &mut self.nodes[current.index()];
            let state = replace(&mut node.state, NodeState::Unknown);
            let priority = node.priority;

            match node.def.as_gate() {
                Ok((gate, inputs)) => {
                    let new_inputs = inputs.map(|input| self.nodes[input.index()].renamed.unwrap());

                    let output = if new_inputs == inputs {
                        current
                    } else {
                        match gate {
                            Gate::And => self.and(new_inputs),
                            Gate::Or => self.or(new_inputs),
                        }
                    };

                    if shuffle > 0 && output != NodeRef::FALSE && output != NodeRef::TRUE {
                        if let Ok((gate, inputs)) = self.nodes[output.index()].def.as_gate() {
                            let [a, b] = inputs.map(|input| self.nodes[input.index()].priority);

                            self.nodes[output.index()].priority = match gate {
                                Gate::And => a.min(b),
                                Gate::Or => a.max(b),
                            };
                        }
                    }

                    self.nodes[current.index()].renamed = Some(output);
                }
                Err(input) => match priority.cmp(&target_priority) {
                    std::cmp::Ordering::Less => {
                        self.nodes[current.index()].renamed = Some(NodeRef::FALSE);
                    }
                    std::cmp::Ordering::Equal => {
                        self.required_inputs.insert(input);
                        self.nodes[current.index()].renamed = Some(NodeRef::TRUE);
                    }
                    std::cmp::Ordering::Greater => match state {
                        NodeState::Required => {
                            self.required_inputs.insert(input);
                            self.nodes[current.index()].renamed = Some(NodeRef::TRUE);
                        }
                        NodeState::Selected => {
                            self.unknown_inputs.insert(input);
                            self.nodes[current.index()].renamed = Some(current);

                            if shuffle > 0 {
                                let priority = &mut self.nodes[current.index()].priority;
                                let mask = !(u64::MAX << 32.min(shuffle - 1)) as u32;

                                *priority ^=
                                    !(*priority ^ priority.wrapping_mul(0x2c9277b5)) & mask;
                            }
                        }
                        NodeState::Nonselected => {
                            self.nodes[current.index()].renamed = Some(NodeRef::FALSE);
                        }
                        NodeState::Unknown => {
                            unreachable!();
                        }
                    },
                },
            }
        }

        self.input_order.clear();

        let result = self.nodes[target.index()].renamed.unwrap();
        self.stack = stack;

        result
    }
}

impl AigValue<AndOrGraph> for (Option<bool>, NodeRef) {
    fn invert_if(self, en: bool, _: &mut AndOrGraph) -> Self {
        let (value, care) = self;
        (value.map(|b| b ^ en), care)
    }

    fn and(self, other: Self, ctx: &mut AndOrGraph) -> Self {
        let (value_a, care_a) = self;
        let (value_b, care_b) = other;

        match (value_a, value_b) {
            (Some(true), Some(true)) => (Some(true), ctx.and([care_a, care_b])),
            (Some(false), Some(false)) => (Some(false), ctx.or([care_a, care_b])),
            (Some(false), _) => (Some(false), care_a),
            (_, Some(false)) => (Some(false), care_b),
            _ => (None, NodeRef::FALSE),
        }
    }

    fn constant(value: bool, _: &mut AndOrGraph) -> Self {
        (Some(value), NodeRef::TRUE)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verification {
    Cex,
    Full,
}

pub struct MinimizationOptions {
    pub fixed_init: bool,
    pub verify: Option<Verification>,
}

pub fn minimize<L: Lit>(
    aig: &OrderedAig<L>,
    latch_init: &[Option<bool>],
    frame_inputs: &[Vec<Option<bool>>],
    writer: &mut DeferredWriter,
    options: &MinimizationOptions,
) -> color_eyre::Result<()> {
    let Some(initial_inputs) = frame_inputs.first() else {
        bail!("no inputs found");
    };

    let mut state = vec![];

    let mut graph = AndOrGraph::default();

    let input_id = |frame: Option<usize>, index: usize| -> u32 {
        (if let Some(frame) = frame {
            latch_init.len() + frame * initial_inputs.len() + index
        } else {
            index
        })
        .try_into()
        .unwrap()
    };

    let decode_input_id = |id: u32| -> (Option<usize>, usize) {
        let id = id as usize;
        if id < latch_init.len() {
            (None, id)
        } else {
            let id = id - latch_init.len();
            let frame = id / initial_inputs.len();
            let index = id % initial_inputs.len();
            (Some(frame), index)
        }
    };

    initial_frame(
        aig,
        &mut state,
        |i, ctx| {
            (
                latch_init[i],
                if latch_init[i].is_some() {
                    if options.fixed_init {
                        NodeRef::TRUE
                    } else {
                        ctx.input(input_id(None, i))
                    }
                } else {
                    NodeRef::FALSE
                },
            )
        },
        |i, ctx| {
            (
                initial_inputs[i],
                if initial_inputs[i].is_some() {
                    ctx.input(input_id(Some(0), i))
                } else {
                    NodeRef::FALSE
                },
            )
        },
        &mut graph,
    );

    let mut minimization_target = 'minimization_target: {
        for (t, inputs) in frame_inputs.iter().enumerate() {
            if t > 0 {
                successor_frame(
                    aig,
                    &mut state,
                    |i, ctx| {
                        (
                            inputs[i],
                            if inputs[i].is_some() {
                                ctx.input(input_id(Some(t), i))
                            } else {
                                NodeRef::FALSE
                            },
                        )
                    },
                    &mut graph,
                );
            }
            let mut good_state = (Some(true), NodeRef::TRUE);

            for (i, bad) in aig.bad_state_properties.iter().enumerate() {
                let (var, polarity) = unpack_lit(*bad);
                let inv_bad = state[var].invert_if(!polarity, &mut graph);

                if inv_bad.0 == Some(false) {
                    println!("bad state property {i} active in frame {t}");
                }

                good_state = good_state.and(inv_bad, &mut graph);
            }
            if good_state.0 == Some(false) {
                println!("bad state found in frame {t}");

                break 'minimization_target good_state.1;
            }

            if t > 0 && t % 500 == 0 {
                println!(
                    "traced frame {t}/{frames}: node count = {node_count}",
                    frames = frame_inputs.len(),
                    node_count = graph.nodes.len(),
                );
            }
        }

        bail!("no bad state found");
    };

    let node_count_width = (graph.nodes.len().max(2) - 1).ilog10() as usize + 1;
    let input_count_width = (graph.unknown_inputs.len().max(2) - 1).ilog10() as usize + 1;

    println!(
        "input: node count = {node_count:w0$}, defined inputs = {defined_inputs:w1$}",
        node_count = graph.nodes.len(),
        defined_inputs = graph.unknown_inputs.len(),
        w0 = node_count_width,
        w1 = input_count_width,
    );

    let mut shuffle = 0;

    let mut iteration = 0;

    while minimization_target != NodeRef::TRUE {
        let prev_unknown_inputs = graph.unknown_inputs.len();
        minimization_target = graph.pass(minimization_target, shuffle, iteration >= 1);
        let unknown_inputs = graph.unknown_inputs.len();
        let required_inputs = graph.required_inputs.len();
        println!(
            concat!(
                "iter:  node count = {node_count:w0$}, defined inputs = {defined_inputs:w1$}, ",
                "required inputs = {required_inputs:w1$}, shuffle = {shuffle}"
            ),
            node_count = graph.active_node_count,
            required_inputs = required_inputs,
            defined_inputs = unknown_inputs + required_inputs,
            shuffle = shuffle,
            w0 = node_count_width,
            w1 = input_count_width,
        );

        if unknown_inputs + (unknown_inputs / 4) < prev_unknown_inputs {
            shuffle = 0;
        } else {
            shuffle += 1;
        }
        iteration += 1;
    }

    println!("minimization complete");

    for i in 0..aig.latches.len() {
        let bit = if options.fixed_init || graph.required_inputs.contains(&input_id(None, i)) {
            latch_init[i]
        } else {
            None
        };

        write_output_bit(writer, bit);
    }

    writer.write_all_defer_err(b"\n");

    for (t, inputs) in frame_inputs.iter().enumerate() {
        for i in 0..aig.input_count {
            let bit = if graph.required_inputs.contains(&input_id(Some(t), i)) {
                inputs[i]
            } else {
                None
            };

            write_output_bit(writer, bit);
        }
        writer.write_all_defer_err(b"\n");
    }

    writer.write_all_defer_err(b"# DONE\n");
    writer.flush_defer_err();
    writer.check_io_error()?;

    let Some(verify) = options.verify else {
        return Ok(());
    };

    let mut check_state: Vec<Option<bool>> = vec![];

    let empty_set = BTreeSet::new();

    let verify_from = match verify {
        Verification::Cex => &empty_set,
        Verification::Full => &graph.required_inputs,
    };

    for check in [None]
        .into_iter()
        .chain(verify_from.iter().copied().map(Some))
    {
        check_state.clear();

        initial_frame(
            aig,
            &mut check_state,
            |i, _| {
                let input = input_id(None, i);
                if options.fixed_init
                    || (Some(input) != check && graph.required_inputs.contains(&input))
                {
                    latch_init[i]
                } else {
                    None
                }
            },
            |i, _| {
                let input = input_id(Some(0), i);
                if Some(input) != check && graph.required_inputs.contains(&input) {
                    initial_inputs[i]
                } else {
                    None
                }
            },
            &mut (),
        );

        let mut bad_state = false;

        'frame: for (t, inputs) in frame_inputs.iter().enumerate() {
            if t > 0 {
                successor_frame(
                    aig,
                    &mut check_state,
                    |i, _| {
                        let input = input_id(Some(t), i);
                        if Some(input) != check && graph.required_inputs.contains(&input) {
                            inputs[i]
                        } else {
                            None
                        }
                    },
                    &mut (),
                );
            }

            for bad in aig.bad_state_properties.iter() {
                let (var, polarity) = unpack_lit(*bad);
                let bad_output = check_state[var].invert_if(polarity, &mut ());
                if bad_output == Some(true) {
                    bad_state = true;
                    break 'frame;
                }
            }
        }

        if bad_state != check.is_none() {
            if let Some(check) = check {
                let (frame, input) = decode_input_id(check);
                if let Some(frame) = frame {
                    bail!("minimality verification wrt. frame {frame} input {input} failed");
                } else {
                    bail!("minimality verification wrt. initial latch {input} failed");
                }
            } else {
                bail!("counter example verification failed");
            }
        }

        if let Some(check) = check {
            let (frame, input) = decode_input_id(check);
            if let Some(frame) = frame {
                println!("verified minimality wrt. frame {frame} input {input}");
            } else {
                println!("verified minimality wrt. initial latch {input}");
            }
        } else {
            println!("verified counter example");
        }
    }

    Ok(())
}
