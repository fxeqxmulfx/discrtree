//! Telling a declaration Lean generated from one someone wrote.
//!
//! Lean gives every declaration a source range, including the ones no one
//! typed. `to_additive` gives `Finset.sum_image` the range of the attribute
//! block sitting inside `theorem Finset.prod_image`; a structure's fields and
//! constructor get lines of the `structure`; `alias` and `@[simps]` do the
//! same. 36 266 of Mathlib's 225 508 rows are in this position — one in six.
//!
//! Printing or copying those lines and calling them the declaration is worse
//! than printing nothing: they read like an answer and stop exactly where the
//! useful part begins. Two questions settle it, and neither needs Lean. Do the
//! lines declare this name? If not, what declaration contains them?

use crate::application::ports::DeclRepo;
use crate::domain::decl::Decl;
use crate::domain::lean_text;
use crate::error::Result;

/// The written declaration `decl` came out of, given the text of its module.
///
/// The smallest containing range can itself be generated: `MonoidHom.mk` sits
/// inside the projection `MonoidHom.toMulHom`, which sits inside `structure
/// MonoidHom`. Only the outermost of those was typed by anyone, and naming
/// either of the others sends the reader to another declaration with no source.
/// So the walk continues outward until the container accounts for itself.
///
/// Each step strictly widens the range, so this ends; the bound is for an index
/// that has been corrupted into a cycle.
pub fn generator(repo: &dyn DeclRepo, decl: &Decl, text: &str) -> Result<Option<Decl>> {
    let mut at = decl.clone();
    for _ in 0..8 {
        let Some(up) = repo.enclosing(&at)? else {
            return Ok((at.name != decl.name).then_some(at));
        };
        let lines = up.span.map(|s| s.slice(text).join("\n")).unwrap_or_default();
        if lean_text::declares_name(&lines, &up.name) {
            return Ok(Some(up));
        }
        at = up;
    }
    Ok(Some(at))
}
