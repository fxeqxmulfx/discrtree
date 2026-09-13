//! Phase 4's first half: getting a text corpus onto the machine without paying
//! for what will never be read.
//!
//! Blobless and sparse. The FLT corpus is 1.17 GB across 60 474 files once the
//! three directories that matter are checked out, and 390 MB of rendered HTML
//! if they are not excluded.

use crate::application::ports::{FetchSpec, Vcs};
use crate::error::{Error, Result, bail};
use std::path::{Path, PathBuf};
use std::process::Command;

pub struct Git {
    pub verbose: bool,
}

impl Git {
    fn run(&self, dir: &Path, args: &[&str]) -> Result<String> {
        if self.verbose {
            eprintln!("dt: git {}", args.join(" "));
        }
        let out = Command::new("git")
            .args(args)
            .current_dir(dir)
            .output()
            .map_err(|e| Error::new(format!("could not run git: {e}")))?;
        if !out.status.success() {
            bail!("git {} failed: {}", args.join(" "), String::from_utf8_lossy(&out.stderr).trim())
        }
        Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
    }
}

impl Vcs for Git {
    fn fetch(&self, spec: &FetchSpec) -> Result<PathBuf> {
        let parent = spec
            .into
            .parent()
            .ok_or_else(|| Error::new("the checkout path has no parent directory"))?;
        std::fs::create_dir_all(parent)?;

        if spec.into.join(".git").is_dir() {
            self.run(&spec.into, &["fetch", "--filter=blob:none", "origin", &spec.rev])?;
            self.run(&spec.into, &["checkout", "--force", &spec.rev])?;
            return Ok(spec.into.clone());
        }

        let dir = spec.into.to_string_lossy().into_owned();
        let mut args = vec!["clone", "--filter=blob:none", "--no-checkout"];
        if !spec.sparse.is_empty() {
            args.push("--sparse");
        }
        args.extend(["--branch", spec.rev.as_str(), spec.url.as_str(), dir.as_str()]);
        self.run(parent, &args)?;

        if !spec.sparse.is_empty() {
            let mut set = vec!["sparse-checkout", "set", "--no-cone"];
            set.extend(spec.sparse.iter().map(String::as_str));
            self.run(&spec.into, &set)?;
        }
        self.run(&spec.into, &["checkout"])?;
        Ok(spec.into.clone())
    }

    fn revision(&self, path: &Path) -> Result<Option<String>> {
        if !path.join(".git").exists() {
            return Ok(None);
        }
        Ok(self.run(path, &["rev-parse", "HEAD"]).ok())
    }
}
