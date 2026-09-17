//! `dt rdeps <name>` — what rests on a declaration.
//!
//! The question asked before changing a signature, and one `find --uses`
//! cannot answer: `uses` holds the constants of a statement, and most of what
//! depends on a lemma depends on it in a proof.

use crate::application::ports::{Build, DeclRepo, Mention};
use crate::domain::name::DeclName;
use crate::domain::query::Query;
use crate::error::{Result, bail};

pub struct Rdeps<'a> {
    pub repo: &'a dyn DeclRepo,
    /// Consulted only when the name is missing, as for `dt deps`.
    pub build: &'a dyn Build,
}

/// Who mentions a declaration: the first `limit`, and how many in all.
pub struct Users {
    pub root: DeclName,
    pub shown: Vec<Mention>,
    pub total: usize,
}

impl Rdeps<'_> {
    /// `within` narrows by `--source` and `--in`; its other conditions are
    /// not read.
    ///
    /// A field, `.integral_mono_on`, is the one declaration it names, and
    /// [`Users::root`] then says which. It is not every declaration it names,
    /// as it is for `find --uses`: a refactor changes one of them, and
    /// `.length` names fifty-two whose users have nothing in common.
    pub fn run(&self, name: &DeclName, within: &Query) -> Result<Users> {
        let name = &self.meant(name)?;
        if self.repo.get(name)?.is_none() {
            if let Some(missing) = self.build.declaring(name.as_str()) {
                bail!("{}", missing.about(name))
            }
            bail!("{name} is not in the index")
        }
        let mut all = self.repo.used_by(name, within)?;
        // A declaration mentions itself when it is recursive; that is not
        // something resting on it.
        all.retain(|m| &m.decl.name != name);
        all.sort_by(|a, b| {
            (a.decl.source.as_str(), a.decl.module.as_str(), a.decl.name.as_str()).cmp(&(
                b.decl.source.as_str(),
                b.decl.module.as_str(),
                b.decl.name.as_str(),
            ))
        });
        let total = all.len();
        all.truncate(within.limit);
        Ok(Users { root: name.clone(), shown: all, total })
    }

    fn meant(&self, name: &DeclName) -> Result<DeclName> {
        if !name.is_field() {
            return Ok(name.clone());
        }
        let mut named = self.repo.ending_in(name)?;
        match named.len() {
            0 => bail!("no declaration in the index ends in {name}"),
            1 => Ok(named.remove(0)),
            n => {
                let shown: Vec<&str> = named.iter().take(SHOWN).map(DeclName::as_str).collect();
                let more = match n.saturating_sub(SHOWN) {
                    0 => String::new(),
                    m => format!(", and {m} more"),
                };
                bail!("{name} ends {n} declarations; name one: {}{more}", shown.join(", "))
            }
        }
    }
}

/// How many of the declarations an ambiguous field names the error lists.
pub const SHOWN: usize = 10;
