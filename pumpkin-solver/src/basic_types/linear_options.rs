use clap::ValueEnum;

#[derive(Debug, PartialEq, Eq, ValueEnum,  Copy, Clone)]
pub enum Shuffle {
    None,
    Scalar,
    Random,
}

impl Default for Shuffle {
    fn default() -> Self {
        Shuffle::None
    }
}

// TODO also add an enum to determine the type of linear inequality to utilize.