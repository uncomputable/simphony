/// Library for parsing and compiling s-lang

pub type ProgNode = Arc<named::NamedConstructNode>;

mod array;
pub mod compile;
pub mod dummy_env;
pub mod error;
pub mod named;
pub mod num;
pub mod parse;
pub mod scope;
mod util;

use std::{collections::HashMap, sync::Arc};

use named::{ConstructExt, Named};
use pest::Parser;
use pest_derive::Parser;
use simplicity::{
    dag::{NoSharing, PostOrderIterItem},
    jet::Elements,
    node::{Commit, Converter, Inner, Node, Redeem, RedeemData},
    BitIter, RedeemNode,
};

pub extern crate simplicity;
pub use simplicity::elements;

use crate::parse::Pattern;
use crate::{
    error::{RichError, WithFile},
    named::{NamedCommitNode, NamedExt},
    parse::{PestParse, Program},
    scope::GlobalScope,
};

#[derive(Parser)]
#[grammar = "minimal.pest"]
pub struct IdentParser;

pub struct Empty;

pub struct WithProgram(Arc<str>);

pub struct WithWitness(Witness);

pub struct Compiler<A, B> {
    program: A,
    witness: B,
}

impl Compiler<Empty, Empty> {
    pub const fn new() -> Self {
        Compiler {
            program: Empty,
            witness: Empty,
        }
    }
}

impl<A, B> Compiler<A, B> {
    pub fn with_program(self, program_str: Arc<str>) -> Compiler<WithProgram, B> {
        Compiler {
            program: WithProgram(program_str),
            witness: self.witness,
        }
    }

    pub fn with_witness(self, witness: Witness) -> Compiler<A, WithWitness> {
        Compiler {
            program: self.program,
            witness: WithWitness(witness),
        }
    }
}

impl<B> Compiler<WithProgram, B> {
    /// Parse a Simfony program from a string and
    /// compile to a Simplicity program without witness information.
    pub fn get_named_commit(&self) -> Result<Arc<Node<Named<Commit<Elements>>>>, String> {
        let simfony_program = IdentParser::parse(Rule::program, &self.program.0)
            .map_err(RichError::from)
            .and_then(|mut pairs| Program::parse(pairs.next().unwrap()))
            .with_file(self.program.0.clone())?;
        let mut scope = GlobalScope::new(Pattern::Ignore);
        let simplicity_program = simfony_program
            .eval(&mut scope)
            .with_file(self.program.0.clone())?;
        let named_commit = simplicity_program
            .finalize_types_main()
            .expect("Type check error");
        Ok(named_commit)
    }
}

impl Compiler<WithProgram, WithWitness> {
    pub fn get_redeem(&self) -> Result<Arc<RedeemNode<Elements>>, String> {
        let named_commit = self.get_named_commit()?;
        let redeem = named_commit
            .convert::<NoSharing, Redeem<Elements>, _>(&mut &self.witness.0)
            .unwrap();
        Ok(redeem)
    }
}

#[derive(Debug, Clone, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct Witness {
    map: HashMap<String, String>,
}

impl<'a, S: ToString> FromIterator<&'a (S, S)> for Witness {
    fn from_iter<T: IntoIterator<Item = &'a (S, S)>>(iter: T) -> Self {
        Self {
            map: HashMap::from_iter(
                iter.into_iter()
                    .map(|(k, v)| (k.to_string(), v.to_string())),
            ),
        }
    }
}

impl std::str::FromStr for Witness {
    type Err = serde_json::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let map = serde_json::from_str::<HashMap<String, String>>(s)?;
        Ok(Witness { map })
    }
}

impl<'a> Converter<Named<Commit<Elements>>, Redeem<Elements>> for &'a Witness {
    type Error = ();

    fn convert_witness(
        &mut self,
        data: &PostOrderIterItem<&NamedCommitNode>,
        _witness: &<Named<Commit<Elements>> as simplicity::node::Marker>::Witness,
    ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Witness, Self::Error> {
        let key = data.node.name();
        let ty = &data.node.arrow().target;
        match self.map.get(key.as_ref()) {
            Some(wit) => {
                let bytes: Vec<u8> = hex_conservative::FromHex::from_hex(wit).unwrap();
                let total_bit_len = bytes.len() * 8;
                let mut bit_iter = BitIter::new(bytes.into_iter());
                let value = bit_iter.read_value(&data.node.arrow().target);
                let v = match value {
                    Ok(v) => v,
                    Err(e) => panic!("Error reading witness: {:?}", e),
                };
                // TODO: Make sure that remaining iterator is empty or all zeros till the specified remaining len.
                let bit_len = ty.bit_width();
                let remaining = total_bit_len - bit_len;
                assert!(remaining < 8);
                for _ in 0..remaining {
                    assert!(!bit_iter.next().unwrap());
                }
                assert!(bit_iter.next().is_none());
                Ok(v)
            }
            None => panic!("Value not found `{}`", key),
        }
    }

    fn convert_disconnect(
        &mut self,
        _data: &PostOrderIterItem<&NamedCommitNode>,
        _maybe_converted: Option<&Arc<Node<Redeem<Elements>>>>,
        _disconnect: &<Named<Commit<Elements>> as simplicity::node::Marker>::Disconnect,
    ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::Disconnect, Self::Error> {
        todo!()
    }

    fn convert_data(
        &mut self,
        data: &PostOrderIterItem<&NamedCommitNode>,
        inner: Inner<
            &Arc<Node<Redeem<Elements>>>,
            <Redeem<Elements> as simplicity::node::Marker>::Jet,
            &<Redeem<Elements> as simplicity::node::Marker>::Disconnect,
            &<Redeem<Elements> as simplicity::node::Marker>::Witness,
        >,
    ) -> Result<<Redeem<Elements> as simplicity::node::Marker>::CachedData, Self::Error> {
        let converted_data = inner
            .map(|node| node.cached_data())
            .map_disconnect(|node| node.cached_data())
            .map_witness(Arc::clone);
        Ok(Arc::new(RedeemData::new(
            data.node.arrow().shallow_clone(),
            converted_data,
        )))
    }
}

#[cfg(test)]
mod tests {
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use simplicity::{encode, BitMachine, BitWriter, Cmr, Value};
    use std::str::FromStr;

    use crate::{named::ProgExt, *};

    #[test]
    fn test_progs() {
        Test::from_program("./example_progs/test.simpl")
            .with_witness("./example_progs/test.wit")
            .run();
        Test::from_program("./example_progs/assertr.simpl").run();
        Test::from_program("./example_progs/scopes.simpl").run();
        Test::from_program("./example_progs/nesting.simpl").run();
        Test::from_program("./example_progs/add.simpl").run();
        Test::from_program("./example_progs/cat.simpl").run();
        Test::from_program("./example_progs/match.simpl").run();
        Test::from_program("./example_progs/array.simpl").run();
        Test::from_program("./example_progs/list.simpl").run();
        Test::from_program("./example_progs/function.simf").run();
        Test::from_program("./example_progs/list_fold.simf").run();
        Test::from_program("./example_progs/for_while.simf").run();
    }

    struct Test {
        program_str: Arc<str>,
        witness: Option<Witness>,
    }

    impl Test {
        pub fn from_program(file: &str) -> Self {
            let path = std::path::Path::new(file);
            let program_str = std::fs::read_to_string(path)
                .map(Arc::<str>::from)
                .expect("Cannot open program");
            Self {
                program_str,
                witness: None,
            }
        }

        pub fn with_witness(self, file: &str) -> Self {
            let path = std::path::Path::new(file);
            let witness_str = std::fs::read_to_string(path).expect("Cannot open witness");
            let witness = Witness::from_str(&witness_str).expect("Cannot parse witness");
            Self {
                program_str: self.program_str,
                witness: Some(witness),
            }
        }

        pub fn run(self) {
            let witness = self.witness.unwrap_or_default();
            let redeem = Compiler::new()
                .with_program(self.program_str)
                .with_witness(witness)
                .get_redeem()
                .expect("Compile error");

            let mut vec = Vec::new();
            let mut writer = BitWriter::new(&mut vec);
            let _encoded = encode::encode_program(&redeem, &mut writer).unwrap();
            dbg!(&redeem);
            println!("{}", Base64Display::new(&vec, &STANDARD));

            let mut bit_mac = BitMachine::for_program(&redeem);
            let env = dummy_env::dummy();
            bit_mac
                .exec(&redeem, &env)
                .expect("Machine execution failure");
        }
    }

    #[test]
    fn temp_progs() {
        let inp = ProgNode::const_word(Value::u32(10));
        let node = ProgNode::jet(Elements::ParseLock);
        println!("l1: {}", node.arrow());
        let node = ProgNode::comp(inp, node).unwrap();
        println!("l2: {}", node.arrow());
        let node = ProgNode::pair(node, ProgNode::unit()).unwrap();
        println!("l3: {}", node.arrow());
        let later_operation = ProgNode::take(ProgNode::unit());
        println!("l4: {}", later_operation.arrow());
        let assert_node = ProgNode::assertl(later_operation, Cmr::unit()).unwrap();
        println!("l5: {}", assert_node.arrow());
        let comp = ProgNode::comp(node, assert_node).unwrap();
        println!("l6: {}", comp.arrow());
        // let node2 = ProgNode::assert(&node, Cmr::unit()).unwrap();
        // println!("l3: {}", node2.arrow());
        // let node3 = ProgNode::comp(&ProgNode::pair(&ProgNode::unit(), &ProgNode::unit()).unwrap(), &node2).unwrap();
        // println!("l4: {}", node3.arrow());
        let res = comp.finalize_types_main().unwrap();
        dbg!(&res);
    }
}
