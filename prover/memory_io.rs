//! Host I/O only: anonymous memory descriptors supplied by the custody launcher.
//! No AIR, transcript, prover parameters or verification rules change here.
// Standalone size-accounting commands use ordinary files; the custody pipeline does not.
#[allow(unused_imports)]
pub use std::fs::{File, OpenOptions};
use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::{Component, Path, PathBuf};

pub fn is_memory(path: &Path) -> bool { path.starts_with("/pq-memory") }

fn descriptor(path: &Path) -> io::Result<PathBuf> {
    let mut key = PathBuf::new();
    for part in path.components() {
        match part { Component::ParentDir => { key.pop(); }, Component::CurDir => {}, other => key.push(other) }
    }
    let raw = std::env::var("PQ_CUSTODY_FDS").map_err(|_| io::Error::other("memory descriptor map missing"))?;
    let map: BTreeMap<String, i32> = serde_json::from_str(&raw).map_err(|_| io::Error::other("invalid descriptor map"))?;
    let fd = map.get(key.to_str().ok_or_else(|| io::Error::other("invalid memory path"))?)
        .filter(|fd| **fd >= 3).ok_or_else(|| io::Error::other("unmapped memory artifact"))?;
    Ok(PathBuf::from(format!("/proc/self/fd/{fd}")))
}

pub fn read(path: impl AsRef<Path>) -> io::Result<Vec<u8>> {
    let path = path.as_ref();
    std::fs::read(if is_memory(path) { descriptor(path)? } else { path.to_path_buf() })
}
pub fn read_to_string(path: impl AsRef<Path>) -> io::Result<String> {
    String::from_utf8(read(path)?).map_err(|_| io::Error::other("invalid UTF-8"))
}
pub fn create_dir(path: impl AsRef<Path>) -> io::Result<()> {
    if is_memory(path.as_ref()) { Ok(()) } else { std::fs::create_dir(path) }
}
pub fn write_new(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut file = if is_memory(path) {
        let file = std::fs::OpenOptions::new().write(true).open(descriptor(path)?)?;
        if file.metadata()?.len() != 0 { return Err(io::Error::other("memory artifact already written")); }
        file
    } else {
        std::fs::OpenOptions::new().write(true).create_new(true).open(path)?
    };
    file.write_all(bytes)
}
