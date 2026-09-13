//! Bringing a text corpus onto the machine.
//!
//! Nothing here is rebuilt or re-verified: upstream verification is taken on
//! trust. For a corpus that wants 67 GB of disk and 5 GB of memory per job this
//! is also forced — indexing its text costs a fraction of that and minutes
//! rather than days.

use crate::application::ports::{FetchSpec, Vcs};
use crate::domain::source::SourceId;
use crate::error::Result;
use std::path::PathBuf;

pub struct Fetched {
    pub source: SourceId,
    pub path: PathBuf,
    pub revision: Option<String>,
}

pub struct Fetch<'a> {
    pub vcs: &'a dyn Vcs,
}

impl Fetch<'_> {
    pub fn run(&self, spec: &FetchSpec) -> Result<Fetched> {
        let path = self.vcs.fetch(spec)?;
        let revision = self.vcs.revision(&path)?;
        Ok(Fetched { source: spec.source.clone(), path, revision })
    }
}
