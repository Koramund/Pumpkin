use std::fmt::{self, Display};


#[derive(Copy, Clone, Debug)]
pub(crate) struct Histogram {
    buckets: [u64; 2048],
}

impl Default for Histogram {
    fn default() -> Self {
        Self {
            buckets: [0u64; 2048],
        }
    }
}

impl Histogram {
    /// Adds a value to the bucket at the specified index (0–2047).
    pub(crate) fn add(&mut self, index: u64, value: u64) {
        if index < 2048 {
            self.buckets[index as usize] += value;
        } else {
            eprintln!("Index out of bounds: {} (must be < 2048)", index);
        }
    }

    /// Returns a tab-separated list of non-zero buckets: "index,count"
    pub(crate) fn format(&self) -> String {
        self.buckets
            .iter()
            .enumerate()
            .filter(|&(_, &count)| count > 0)
            .map(|(i, &count)| format!("{},{}", i, count))
            .collect::<Vec<_>>()
            .join(";")
    }
}

impl Display for Histogram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format())
    }
}
