//! Re-audit the unchanged source certificate without linking an SDP optimizer.
use minexposure_core::stationary_certificate::{
    SplitExactDualCertificate, audit_split_exact_certificate_with_jobs,
};
use std::{error::Error, fs::File, io::BufReader};

fn main() -> Result<(), Box<dyn Error>> {
    let path = std::env::args().nth(1).ok_or("usage: audit_terminal_bootstrap_source CERTIFICATE.json")?;
    let certificate: SplitExactDualCertificate = serde_json::from_reader(BufReader::new(File::open(path)?))?;
    let report = audit_split_exact_certificate_with_jobs(&certificate, 2)?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    if report.nonzero_exact_residual_count != 0
        || !report.all_gram_matrices_exactly_positive_semidefinite
        || report.certified_bound != "5861/2000"
    {
        return Err("source certificate failed required exact audit gates".into());
    }
    Ok(())
}
