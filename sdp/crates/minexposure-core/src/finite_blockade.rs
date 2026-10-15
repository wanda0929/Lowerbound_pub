//! Native finite-blockade Hamiltonians and piecewise-constant propagation.
//!
//! Ported from `FiniteBlockade/subspaces.py` and `czz_cal` at source commit
//! `677eba8905756a4dd4d1f0c760b0375ebec67161`.

use nalgebra::linalg::SymmetricEigen;
use nalgebra::{DMatrix, DVector};
use num_complex::Complex64;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub type ComplexMatrix = DMatrix<Complex64>;

const TWO_PI: f64 = 2.0 * std::f64::consts::PI;
const SPECIES: [Species; 3] = [Species::Rb, Species::Cs, Species::Rb];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Species {
    Rb,
    Cs,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct ThreeQubitParameters {
    pub omega_rb: f64,
    pub omega_cs: f64,
    pub delta_rb: f64,
    pub delta_cs: f64,
    pub v_rb_rb: f64,
    pub v_rb_cs: f64,
}

impl ThreeQubitParameters {
    pub fn magic(kappa: f64, blockade: f64) -> Result<Self, String> {
        if kappa == 0.0 || blockade == 0.0 || !kappa.is_finite() || !blockade.is_finite() {
            return Err("kappa and blockade must be finite and nonzero".into());
        }
        Ok(Self {
            omega_rb: kappa * blockade,
            omega_cs: 2.0 * kappa * blockade,
            delta_rb: 0.0,
            delta_cs: -blockade,
            v_rb_rb: 0.0,
            v_rb_cs: blockade,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Segment {
    pub duration_us: f64,
    pub omega_rb_mhz: f64,
    pub omega_cs_mhz: f64,
    pub phase_rb_rad: f64,
    pub phase_cs_rad: f64,
    pub delta_rb_mhz: f64,
    pub delta_cs_mhz: f64,
    pub v_rb_rb_mhz: f64,
    pub v_rb_cs_mhz: f64,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FinitePulseArtifact {
    pub identity: String,
    pub duration_us: f64,
    pub n_segments: usize,
    pub hamiltonian_parameters_mhz: FiniteHamiltonianParameters,
    pub phi_rb_unwrapped_rad: Vec<f64>,
    pub phi_cs_unwrapped_rad: Vec<f64>,
    pub theta_rb: f64,
    pub theta_cs: f64,
    pub discrete_staircase_fidelity: f64,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct FiniteHamiltonianParameters {
    pub omega_rb: f64,
    pub omega_cs: f64,
    pub delta_rb: f64,
    pub delta_cs: f64,
    pub v_rbcs: f64,
    pub v_rbrb: f64,
}

impl FinitePulseArtifact {
    pub fn segments(&self) -> Result<Vec<Segment>, String> {
        if self.n_segments == 0
            || self.phi_rb_unwrapped_rad.len() != self.n_segments
            || self.phi_cs_unwrapped_rad.len() != self.n_segments
            || !self.duration_us.is_finite()
            || self.duration_us <= 0.0
        {
            return Err("invalid pulse duration, segment count, or phase arrays".into());
        }
        let h = self.hamiltonian_parameters_mhz;
        let duration_us = self.duration_us / self.n_segments as f64;
        Ok(self
            .phi_rb_unwrapped_rad
            .iter()
            .zip(&self.phi_cs_unwrapped_rad)
            .map(|(&phase_rb_rad, &phase_cs_rad)| Segment {
                duration_us,
                omega_rb_mhz: h.omega_rb,
                omega_cs_mhz: h.omega_cs,
                phase_rb_rad,
                phase_cs_rad,
                delta_rb_mhz: h.delta_rb,
                delta_cs_mhz: h.delta_cs,
                v_rb_rb_mhz: h.v_rbrb,
                v_rb_cs_mhz: h.v_rbcs,
            })
            .collect())
    }
}

impl Segment {
    fn parameters(self) -> ThreeQubitParameters {
        ThreeQubitParameters {
            omega_rb: self.omega_rb_mhz,
            omega_cs: self.omega_cs_mhz,
            delta_rb: self.delta_rb_mhz,
            delta_cs: self.delta_cs_mhz,
            v_rb_rb: self.v_rb_rb_mhz,
            v_rb_cs: self.v_rb_cs_mhz,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Propagation {
    pub bits: String,
    pub basis: Vec<String>,
    pub amplitude: Complex64,
    pub unitary: ComplexMatrix,
    pub rydberg_exposure_us: f64,
}

#[derive(Clone, Debug, PartialEq)]
pub struct PhaseDerivatives {
    pub propagation: Propagation,
    pub amplitude_phase_rb: Vec<Complex64>,
    pub amplitude_phase_cs: Vec<Complex64>,
    pub amplitude_omega_rb: Vec<Complex64>,
    pub amplitude_omega_cs: Vec<Complex64>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct PulseMetrics {
    pub fidelity: f64,
    pub rydberg_exposure_us: f64,
    pub exposure_per_sector_us: BTreeMap<String, f64>,
    pub amplitudes: BTreeMap<String, PhaseResult>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct PhaseObjective {
    pub cost: f64,
    pub fidelity: f64,
    pub gradient_phase_rb: Vec<f64>,
    pub gradient_phase_cs: Vec<f64>,
    pub gradient_omega_rb: Vec<f64>,
    pub gradient_omega_cs: Vec<f64>,
    pub gradient_theta_rb: f64,
    pub gradient_theta_cs: f64,
}

fn parse_bits(bits: &str) -> Result<[bool; 3], String> {
    let bytes = bits.as_bytes();
    if bytes.len() != 3 || bytes.iter().any(|byte| !matches!(byte, b'0' | b'1')) {
        return Err("bits must contain exactly three binary digits".into());
    }
    Ok([bytes[0] == b'1', bytes[1] == b'1', bytes[2] == b'1'])
}

pub fn subspace_basis(bits: &str) -> Result<Vec<String>, String> {
    let active = parse_bits(bits)?;
    let sites = active
        .iter()
        .enumerate()
        .filter_map(|(index, &is_active)| is_active.then_some(index))
        .collect::<Vec<_>>();
    let mut labels = Vec::with_capacity(1 << sites.len());
    for choice in 0..(1_usize << sites.len()) {
        let mut label = bits.as_bytes().to_vec();
        for (position, &site) in sites.iter().enumerate() {
            let shift = sites.len() - position - 1;
            if (choice >> shift) & 1 == 1 {
                label[site] = b'r';
            }
        }
        labels.push(String::from_utf8(label).expect("binary/Rydberg labels are UTF-8"));
    }
    Ok(labels)
}

fn species_value(species: Species, rb: f64, cs: f64) -> f64 {
    match species {
        Species::Rb => rb,
        Species::Cs => cs,
    }
}

pub fn subspace_hamiltonian(
    bits: &str,
    parameters: ThreeQubitParameters,
    phase_rb: f64,
    phase_cs: f64,
) -> Result<(Vec<String>, ComplexMatrix), String> {
    let active = parse_bits(bits)?;
    let values = [
        parameters.omega_rb,
        parameters.omega_cs,
        parameters.delta_rb,
        parameters.delta_cs,
        parameters.v_rb_rb,
        parameters.v_rb_cs,
        phase_rb,
        phase_cs,
    ];
    if values.iter().any(|value| !value.is_finite()) {
        return Err("finite-blockade parameters and phases must be finite".into());
    }
    let basis = subspace_basis(bits)?;
    let mut hamiltonian = ComplexMatrix::zeros(basis.len(), basis.len());

    for (row, label) in basis.iter().enumerate() {
        let bytes = label.as_bytes();
        let rydberg = (0..3)
            .filter(|&index| bytes[index] == b'r')
            .collect::<Vec<_>>();
        let mut energy = rydberg
            .iter()
            .map(|&index| species_value(SPECIES[index], parameters.delta_rb, parameters.delta_cs))
            .sum::<f64>();
        for (position, &left) in rydberg.iter().enumerate() {
            for &right in &rydberg[position + 1..] {
                energy += if SPECIES[left] == Species::Rb && SPECIES[right] == Species::Rb {
                    parameters.v_rb_rb
                } else {
                    parameters.v_rb_cs
                };
            }
        }
        hamiltonian[(row, row)] = Complex64::new(energy, 0.0);
    }

    for (column, label) in basis.iter().enumerate() {
        let bytes = label.as_bytes();
        for atom in 0..3 {
            if !active[atom] || bytes[atom] != b'1' {
                continue;
            }
            let mut excited = bytes.to_vec();
            excited[atom] = b'r';
            let excited = String::from_utf8(excited).expect("state label is UTF-8");
            let row = basis
                .iter()
                .position(|label| label == &excited)
                .expect("excited state belongs to subspace");
            let omega = species_value(SPECIES[atom], parameters.omega_rb, parameters.omega_cs);
            let phase = species_value(SPECIES[atom], phase_rb, phase_cs);
            let amplitude = Complex64::from_polar(omega / 2.0, -phase);
            hamiltonian[(row, column)] += amplitude;
            hamiltonian[(column, row)] += amplitude.conj();
        }
    }
    Ok((basis, hamiltonian))
}

fn matrix_one_norm(matrix: &ComplexMatrix) -> f64 {
    (0..matrix.ncols())
        .map(|column| {
            (0..matrix.nrows())
                .map(|row| matrix[(row, column)].norm())
                .sum::<f64>()
        })
        .fold(0.0, f64::max)
}

/// Scaling-and-squaring Padé(13), following the Higham/SciPy algorithm.
pub fn matrix_exponential(matrix: &ComplexMatrix) -> Result<ComplexMatrix, String> {
    if matrix.nrows() != matrix.ncols() {
        return Err("matrix exponential requires a square matrix".into());
    }
    if matrix
        .iter()
        .any(|value| !value.re.is_finite() || !value.im.is_finite())
    {
        return Err("matrix exponential input must be finite".into());
    }
    if matrix.nrows() == 0 {
        return Ok(matrix.clone());
    }
    const THETA_13: f64 = 5.371_920_351_148_152;
    let norm = matrix_one_norm(matrix);
    let squarings = if norm <= THETA_13 || norm == 0.0 {
        0_u32
    } else {
        (norm / THETA_13).log2().ceil() as u32
    };
    let a = matrix * Complex64::new(2_f64.powi(-(squarings as i32)), 0.0);
    let a2 = &a * &a;
    let a4 = &a2 * &a2;
    let a6 = &a4 * &a2;
    let identity = ComplexMatrix::identity(a.nrows(), a.ncols());
    let coefficients = [
        64_764_752_532_480_000.0,
        32_382_376_266_240_000.0,
        7_771_770_303_897_600.0,
        1_187_353_796_428_800.0,
        129_060_195_264_000.0,
        10_559_470_521_600.0,
        670_442_572_800.0,
        33_522_128_640.0,
        1_323_241_920.0,
        40_840_800.0,
        960_960.0,
        16_380.0,
        182.0,
        1.0,
    ]
    .map(|value| Complex64::new(value, 0.0));
    let u = &a
        * (&a6 * (&a6 * coefficients[13] + &a4 * coefficients[11] + &a2 * coefficients[9])
            + &a6 * coefficients[7]
            + &a4 * coefficients[5]
            + &a2 * coefficients[3]
            + &identity * coefficients[1]);
    let v = &a6 * (&a6 * coefficients[12] + &a4 * coefficients[10] + &a2 * coefficients[8])
        + &a6 * coefficients[6]
        + &a4 * coefficients[4]
        + &a2 * coefficients[2]
        + &identity * coefficients[0];
    let numerator = &v + &u;
    let denominator = v - u;
    let mut result = denominator
        .lu()
        .solve(&numerator)
        .ok_or_else(|| "Padé denominator is singular".to_string())?;
    for _ in 0..squarings {
        result = &result * &result;
    }
    Ok(result)
}

pub fn segment_unitary(
    hamiltonian_mhz: &ComplexMatrix,
    duration_us: f64,
) -> Result<ComplexMatrix, String> {
    if !duration_us.is_finite() {
        return Err("segment duration must be finite".into());
    }
    matrix_exponential(&(hamiltonian_mhz * Complex64::new(0.0, -TWO_PI * duration_us)))
}

fn exponential_frechet(
    generator: &ComplexMatrix,
    direction: &ComplexMatrix,
) -> Result<ComplexMatrix, String> {
    if generator.shape() != direction.shape() || generator.nrows() != generator.ncols() {
        return Err("Fréchet derivative matrices must be square and equal-sized".into());
    }
    let n = generator.nrows();
    let mut block = ComplexMatrix::zeros(2 * n, 2 * n);
    block.view_mut((0, 0), (n, n)).copy_from(generator);
    block.view_mut((0, n), (n, n)).copy_from(direction);
    block.view_mut((n, n), (n, n)).copy_from(generator);
    Ok(matrix_exponential(&block)?.view((0, n), (n, n)).into())
}

fn phase_derivative_hamiltonian(
    bits: &str,
    basis: &[String],
    segment: Segment,
    species: Species,
) -> Result<ComplexMatrix, String> {
    let active = parse_bits(bits)?;
    let mut derivative = ComplexMatrix::zeros(basis.len(), basis.len());
    for (column, label) in basis.iter().enumerate() {
        let bytes = label.as_bytes();
        for atom in 0..3 {
            if !active[atom] || bytes[atom] != b'1' || SPECIES[atom] != species {
                continue;
            }
            let mut excited = bytes.to_vec();
            excited[atom] = b'r';
            let excited = String::from_utf8(excited).expect("state label is UTF-8");
            let row = basis
                .iter()
                .position(|label| label == &excited)
                .expect("excited state belongs to subspace");
            let omega = species_value(species, segment.omega_rb_mhz, segment.omega_cs_mhz);
            let phase = species_value(species, segment.phase_rb_rad, segment.phase_cs_rad);
            let coupling = Complex64::from_polar(omega / 2.0, -phase);
            derivative[(row, column)] += Complex64::new(0.0, -1.0) * coupling;
            derivative[(column, row)] += Complex64::new(0.0, 1.0) * coupling.conj();
        }
    }
    Ok(derivative)
}

fn amplitude_derivative_hamiltonian(
    bits: &str,
    basis: &[String],
    segment: Segment,
    species: Species,
) -> Result<ComplexMatrix, String> {
    let active = parse_bits(bits)?;
    let mut derivative = ComplexMatrix::zeros(basis.len(), basis.len());
    for (column, label) in basis.iter().enumerate() {
        let bytes = label.as_bytes();
        for atom in 0..3 {
            if !active[atom] || bytes[atom] != b'1' || SPECIES[atom] != species {
                continue;
            }
            let mut excited = bytes.to_vec();
            excited[atom] = b'r';
            let excited = String::from_utf8(excited).expect("state label is UTF-8");
            let row = basis
                .iter()
                .position(|label| label == &excited)
                .expect("excited state belongs to subspace");
            let phase = species_value(species, segment.phase_rb_rad, segment.phase_cs_rad);
            let coupling = Complex64::from_polar(0.5, -phase);
            derivative[(row, column)] += coupling;
            derivative[(column, row)] += coupling.conj();
        }
    }
    Ok(derivative)
}

pub fn propagate_subspace(bits: &str, segments: &[Segment]) -> Result<Propagation, String> {
    if segments.is_empty() {
        return Err("pulse must contain at least one segment".into());
    }
    let basis = subspace_basis(bits)?;
    let mut total = ComplexMatrix::identity(basis.len(), basis.len());
    let initial = basis
        .iter()
        .position(|label| label == bits)
        .expect("computational state belongs to its subspace");
    let mut state = DVector::zeros(basis.len());
    state[initial] = Complex64::new(1.0, 0.0);
    let counts = DMatrix::from_diagonal(&DVector::from_iterator(
        basis.len(),
        basis.iter().map(|label| {
            Complex64::new(
                label.bytes().filter(|&byte| byte == b'r').count() as f64,
                0.0,
            )
        }),
    ));
    let mut exposure = 0.0;
    for &segment in segments {
        if segment.duration_us < 0.0 {
            return Err("segment duration must be nonnegative".into());
        }
        let (segment_basis, hamiltonian) = subspace_hamiltonian(
            bits,
            segment.parameters(),
            segment.phase_rb_rad,
            segment.phase_cs_rad,
        )?;
        if segment_basis != basis {
            return Err("subspace basis changed between segments".into());
        }
        let unitary = segment_unitary(&hamiltonian, segment.duration_us)?;
        exposure += integrated_observable(&hamiltonian, &state, &counts, segment.duration_us)?;
        state = &unitary * state;
        total = unitary * total;
    }
    Ok(Propagation {
        bits: bits.into(),
        basis,
        amplitude: total[(initial, initial)],
        unitary: total,
        rydberg_exposure_us: exposure,
    })
}

/// Return the propagation and analytic derivatives of its return amplitude
/// with respect to every Rb/Cs segment phase and Rabi frequency.
pub fn propagate_with_phase_derivatives(
    bits: &str,
    segments: &[Segment],
) -> Result<PhaseDerivatives, String> {
    if segments.is_empty() {
        return Err("pulse must contain at least one segment".into());
    }
    let basis = subspace_basis(bits)?;
    let initial = basis
        .iter()
        .position(|label| label == bits)
        .expect("computational state belongs to its subspace");
    let identity = ComplexMatrix::identity(basis.len(), basis.len());
    let mut unitaries = Vec::with_capacity(segments.len());
    let mut derivatives_rb = Vec::with_capacity(segments.len());
    let mut derivatives_cs = Vec::with_capacity(segments.len());
    let mut derivatives_omega_rb = Vec::with_capacity(segments.len());
    let mut derivatives_omega_cs = Vec::with_capacity(segments.len());
    for &segment in segments {
        let (_, hamiltonian) = subspace_hamiltonian(
            bits,
            segment.parameters(),
            segment.phase_rb_rad,
            segment.phase_cs_rad,
        )?;
        let scale = Complex64::new(0.0, -TWO_PI * segment.duration_us);
        let generator = &hamiltonian * scale;
        unitaries.push(matrix_exponential(&generator)?);
        derivatives_rb.push(exponential_frechet(
            &generator,
            &(phase_derivative_hamiltonian(bits, &basis, segment, Species::Rb)? * scale),
        )?);
        derivatives_cs.push(exponential_frechet(
            &generator,
            &(phase_derivative_hamiltonian(bits, &basis, segment, Species::Cs)? * scale),
        )?);
        derivatives_omega_rb.push(exponential_frechet(
            &generator,
            &(amplitude_derivative_hamiltonian(bits, &basis, segment, Species::Rb)? * scale),
        )?);
        derivatives_omega_cs.push(exponential_frechet(
            &generator,
            &(amplitude_derivative_hamiltonian(bits, &basis, segment, Species::Cs)? * scale),
        )?);
    }
    let mut prefix = Vec::with_capacity(segments.len() + 1);
    prefix.push(identity.clone());
    for unitary in &unitaries {
        prefix.push(unitary * prefix.last().expect("prefix contains identity"));
    }
    let mut suffix = vec![identity; segments.len() + 1];
    for index in (0..segments.len()).rev() {
        suffix[index] = &suffix[index + 1] * &unitaries[index];
    }
    let amplitude_phase_rb = (0..segments.len())
        .map(|index| {
            (&suffix[index + 1] * &derivatives_rb[index] * &prefix[index])[(initial, initial)]
        })
        .collect();
    let amplitude_phase_cs = (0..segments.len())
        .map(|index| {
            (&suffix[index + 1] * &derivatives_cs[index] * &prefix[index])[(initial, initial)]
        })
        .collect();
    let amplitude_omega_rb = (0..segments.len())
        .map(|index| {
            (&suffix[index + 1] * &derivatives_omega_rb[index] * &prefix[index])[(initial, initial)]
        })
        .collect();
    let amplitude_omega_cs = (0..segments.len())
        .map(|index| {
            (&suffix[index + 1] * &derivatives_omega_cs[index] * &prefix[index])[(initial, initial)]
        })
        .collect();
    Ok(PhaseDerivatives {
        propagation: propagate_subspace(bits, segments)?,
        amplitude_phase_rb,
        amplitude_phase_cs,
        amplitude_omega_rb,
        amplitude_omega_cs,
    })
}

fn czz_phase(bits: &str, theta_rb: f64, theta_cs: f64) -> Result<f64, String> {
    let active = parse_bits(bits)?;
    let rb_count = usize::from(active[0]) + usize::from(active[2]);
    let cs_count = usize::from(active[1]);
    let adjacent = usize::from(active[0] && active[1]) + usize::from(active[1] && active[2]);
    Ok(rb_count as f64 * theta_rb
        + cs_count as f64 * theta_cs
        + adjacent as f64 * std::f64::consts::PI)
}

pub fn pulse_metrics(
    segments: &[Segment],
    theta_rb: f64,
    theta_cs: f64,
) -> Result<PulseMetrics, String> {
    let mut trace = Complex64::new(0.0, 0.0);
    let mut trace_mm = 0.0;
    let mut total_exposure = 0.0;
    let mut exposure_per_sector_us = BTreeMap::new();
    let mut amplitudes = BTreeMap::new();
    for number in 0..8 {
        let bits = format!("{number:03b}");
        let result = propagate_subspace(&bits, segments)?;
        trace +=
            Complex64::from_polar(1.0, -czz_phase(&bits, theta_rb, theta_cs)?) * result.amplitude;
        trace_mm += result.amplitude.norm_sqr();
        total_exposure += result.rydberg_exposure_us;
        exposure_per_sector_us.insert(bits.clone(), result.rydberg_exposure_us);
        amplitudes.insert(
            bits,
            PhaseResult {
                amplitude_re: result.amplitude.re,
                amplitude_im: result.amplitude.im,
                phase_rad: result.amplitude.arg(),
                return_probability: result.amplitude.norm_sqr(),
            },
        );
    }
    Ok(PulseMetrics {
        fidelity: (trace.norm_sqr() + trace_mm) / 72.0,
        rydberg_exposure_us: total_exposure / 8.0,
        exposure_per_sector_us,
        amplitudes,
    })
}

pub fn phase_objective(
    segments: &[Segment],
    theta_rb: f64,
    theta_cs: f64,
) -> Result<PhaseObjective, String> {
    let n = segments.len();
    let mut sectors = Vec::with_capacity(8);
    let mut trace = Complex64::new(0.0, 0.0);
    let mut leakage = 0.0;
    for number in 0..8 {
        let bits = format!("{number:03b}");
        let result = propagate_with_phase_derivatives(&bits, segments)?;
        let z = Complex64::from_polar(1.0, -czz_phase(&bits, theta_rb, theta_cs)?);
        trace += z * result.propagation.amplitude;
        leakage += result.propagation.amplitude.norm_sqr();
        sectors.push((bits, z, result));
    }
    let fidelity = (trace.norm_sqr() + leakage) / 72.0;
    let gradient = |control: usize| {
        (0..n)
            .map(|index| {
                let mut d_trace = Complex64::new(0.0, 0.0);
                let mut d_leakage_half = Complex64::new(0.0, 0.0);
                for (_, z, sector) in &sectors {
                    let derivative = match control {
                        0 => sector.amplitude_phase_rb[index],
                        1 => sector.amplitude_phase_cs[index],
                        2 => sector.amplitude_omega_rb[index],
                        3 => sector.amplitude_omega_cs[index],
                        _ => unreachable!(),
                    };
                    d_trace += z * derivative;
                    d_leakage_half += sector.propagation.amplitude.conj() * derivative;
                }
                -(2.0 / 72.0) * (trace.conj() * d_trace + d_leakage_half).re
            })
            .collect::<Vec<_>>()
    };
    let theta_gradient = |rb: bool| {
        let mut d_trace = Complex64::new(0.0, 0.0);
        for (bits, z, sector) in &sectors {
            let active = parse_bits(bits).expect("validated computational bits");
            let count = if rb {
                usize::from(active[0]) + usize::from(active[2])
            } else {
                usize::from(active[1])
            };
            d_trace += Complex64::new(0.0, -(count as f64)) * z * sector.propagation.amplitude;
        }
        -(2.0 / 72.0) * (trace.conj() * d_trace).re
    };
    Ok(PhaseObjective {
        cost: 1.0 - fidelity,
        fidelity,
        gradient_phase_rb: gradient(0),
        gradient_phase_cs: gradient(1),
        gradient_omega_rb: gradient(2),
        gradient_omega_cs: gradient(3),
        gradient_theta_rb: theta_gradient(true),
        gradient_theta_cs: theta_gradient(false),
    })
}

fn integrated_observable(
    hamiltonian_mhz: &ComplexMatrix,
    initial: &DVector<Complex64>,
    observable: &ComplexMatrix,
    duration_us: f64,
) -> Result<f64, String> {
    if hamiltonian_mhz.nrows() != initial.len() || observable.shape() != hamiltonian_mhz.shape() {
        return Err("observable integration dimension mismatch".into());
    }
    let eigen = SymmetricEigen::new(hamiltonian_mhz.clone());
    let coefficients = eigen.eigenvectors.adjoint() * initial;
    let observable_eigen = eigen.eigenvectors.adjoint() * observable * &eigen.eigenvectors;
    let mut integral = Complex64::new(0.0, 0.0);
    for left in 0..initial.len() {
        for right in 0..initial.len() {
            let difference = TWO_PI * (eigen.eigenvalues[left] - eigen.eigenvalues[right]);
            let factor = if difference.abs() < 1e-12 {
                Complex64::new(duration_us, 0.0)
            } else {
                (Complex64::from_polar(1.0, difference * duration_us) - 1.0)
                    / Complex64::new(0.0, difference)
            };
            integral += coefficients[left].conj()
                * coefficients[right]
                * observable_eigen[(left, right)]
                * factor;
        }
    }
    if integral.im.abs() > 1e-9 * (1.0 + integral.re.abs()) {
        return Err(format!(
            "integrated Hermitian observable has imaginary residual {}",
            integral.im
        ));
    }
    Ok(integral.re)
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct ColeParameters {
    pub v_rb_cs_mhz: f64,
    pub v_rb_rb_mhz: f64,
    pub omega_rb_mhz: f64,
    pub delta_rb_mhz: f64,
    pub cs_to_rb_ratio: f64,
}

impl ColeParameters {
    pub fn from_cole(v_rb_cs_mhz: f64, v_rb_rb_mhz: f64, ratio: f64) -> Self {
        Self {
            v_rb_cs_mhz,
            v_rb_rb_mhz,
            omega_rb_mhz: 3.0_f64.sqrt() * v_rb_cs_mhz / 2.0,
            delta_rb_mhz: v_rb_cs_mhz / 2.0,
            cs_to_rb_ratio: ratio,
        }
    }

    pub fn ire24() -> Self {
        Self::from_cole(36.0756, 0.04420, 1.0)
    }

    pub fn omega_cs_mhz(self) -> f64 {
        self.cs_to_rb_ratio * self.omega_rb_mhz
    }

    pub fn omega_detuned_mhz(self) -> f64 {
        self.omega_rb_mhz.hypot(self.delta_rb_mhz)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct PhaseResult {
    pub amplitude_re: f64,
    pub amplitude_im: f64,
    pub phase_rad: f64,
    pub return_probability: f64,
}

fn cole_hamiltonian_one(omega: f64, delta: f64) -> ComplexMatrix {
    ComplexMatrix::from_row_slice(
        2,
        2,
        &[
            Complex64::new(0.0, 0.0),
            Complex64::new(omega / 2.0, 0.0),
            Complex64::new(omega / 2.0, 0.0),
            Complex64::new(-delta, 0.0),
        ],
    )
}

fn cole_hamiltonian_two(omega: f64, delta: f64, v_rb_rb: f64) -> ComplexMatrix {
    let coupling = Complex64::new(omega / 2.0, 0.0);
    let zero = Complex64::new(0.0, 0.0);
    ComplexMatrix::from_row_slice(
        4,
        4,
        &[
            zero,
            coupling,
            coupling,
            zero,
            coupling,
            Complex64::new(-delta, 0.0),
            zero,
            coupling,
            coupling,
            zero,
            Complex64::new(-delta, 0.0),
            coupling,
            zero,
            coupling,
            coupling,
            Complex64::new(-2.0 * delta + v_rb_rb, 0.0),
        ],
    )
}

pub fn simulate_cole_state(bits: &str, parameters: ColeParameters) -> Result<PhaseResult, String> {
    let active = parse_bits(bits)?;
    let values = [
        parameters.v_rb_cs_mhz,
        parameters.v_rb_rb_mhz,
        parameters.omega_rb_mhz,
        parameters.delta_rb_mhz,
        parameters.cs_to_rb_ratio,
    ];
    if values.iter().any(|value| !value.is_finite()) {
        return Err("Cole parameters must be finite".into());
    }
    let cs_amplitude = if active[1] {
        if parameters.omega_cs_mhz() <= 0.0 {
            return Err("Cs Rabi frequency must be positive".into());
        }
        Complex64::new(-1.0, 0.0)
    } else {
        Complex64::new(1.0, 0.0)
    };
    let delta = parameters.delta_rb_mhz
        - if active[1] {
            parameters.v_rb_cs_mhz
        } else {
            0.0
        };
    let rb_count = usize::from(active[0]) + usize::from(active[2]);
    let rb_amplitude = match rb_count {
        0 => Complex64::new(1.0, 0.0),
        1 => {
            let unitary = matrix_exponential(
                &(cole_hamiltonian_one(parameters.omega_rb_mhz, delta)
                    * Complex64::new(
                        0.0,
                        -2.0 * std::f64::consts::PI / parameters.omega_detuned_mhz(),
                    )),
            )?;
            unitary[(0, 0)]
        }
        2 => {
            let unitary = matrix_exponential(
                &(cole_hamiltonian_two(parameters.omega_rb_mhz, delta, parameters.v_rb_rb_mhz)
                    * Complex64::new(
                        0.0,
                        -2.0 * std::f64::consts::PI / parameters.omega_detuned_mhz(),
                    )),
            )?;
            unitary[(0, 0)]
        }
        _ => unreachable!(),
    };
    let amplitude = cs_amplitude * rb_amplitude;
    Ok(PhaseResult {
        amplitude_re: amplitude.re,
        amplitude_im: amplitude.im,
        phase_rad: amplitude.arg(),
        return_probability: amplitude.norm_sqr(),
    })
}

pub fn simulate_cole_all(
    parameters: ColeParameters,
) -> Result<BTreeMap<String, PhaseResult>, String> {
    (0..8)
        .map(|number| {
            let bits = format!("{number:03b}");
            simulate_cole_state(&bits, parameters).map(|result| (bits, result))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn max_identity_error(matrix: &ComplexMatrix) -> f64 {
        let identity = ComplexMatrix::identity(matrix.nrows(), matrix.ncols());
        (matrix.adjoint() * matrix - identity)
            .iter()
            .map(|value| value.norm())
            .fold(0.0, f64::max)
    }

    #[test]
    fn subspace_basis_matches_source_order() {
        assert_eq!(subspace_basis("000").unwrap(), ["000"]);
        assert_eq!(subspace_basis("100").unwrap(), ["100", "r00"]);
        assert_eq!(subspace_basis("011").unwrap(), ["011", "01r", "0r1", "0rr"]);
        assert_eq!(subspace_basis("111").unwrap().len(), 8);
    }

    #[test]
    fn magic_finite_hamiltonian_matches_source_elements() {
        let parameters = ThreeQubitParameters::magic(1.0, 1.0).unwrap();
        let (basis, hamiltonian) = subspace_hamiltonian("100", parameters, 0.0, 0.0).unwrap();
        assert_eq!(basis, ["100", "r00"]);
        assert_eq!(hamiltonian[(1, 0)], Complex64::new(0.5, 0.0));
        assert_eq!(hamiltonian[(1, 1)], Complex64::new(0.0, 0.0));
    }

    #[test]
    fn pade_exponential_is_unitary_for_hermitian_generator() {
        let parameters = ThreeQubitParameters::magic(0.7, 1.3).unwrap();
        let (_, hamiltonian) = subspace_hamiltonian("111", parameters, 0.37, -0.28).unwrap();
        let unitary = segment_unitary(&hamiltonian, 0.23).unwrap();
        assert!(max_identity_error(&unitary) < 2e-13);
    }

    #[test]
    fn integrates_a_two_level_rydberg_population_exactly() {
        let segment = Segment {
            duration_us: 0.05,
            omega_rb_mhz: 20.0,
            omega_cs_mhz: 0.0,
            phase_rb_rad: 0.31,
            phase_cs_rad: 0.0,
            delta_rb_mhz: 0.0,
            delta_cs_mhz: 0.0,
            v_rb_rb_mhz: 0.0,
            v_rb_cs_mhz: 0.0,
        };
        let result = propagate_subspace("100", &[segment]).unwrap();
        assert!((result.rydberg_exposure_us - 0.025).abs() < 2e-14);
        assert!((result.amplitude + 1.0).norm() < 2e-14);
    }

    #[test]
    fn cole_zero_rb_interaction_reproduces_exact_phase_table() {
        let parameters = ColeParameters::from_cole(1.0, 0.0, 1.0);
        let expected = [
            ("000", 0.0),
            ("001", -std::f64::consts::FRAC_PI_2),
            ("010", std::f64::consts::PI),
            ("011", -std::f64::consts::FRAC_PI_2),
            ("100", -std::f64::consts::FRAC_PI_2),
            ("101", std::f64::consts::PI),
            ("110", -std::f64::consts::FRAC_PI_2),
            ("111", 0.0),
        ];
        let results = simulate_cole_all(parameters).unwrap();
        for (bits, phase) in expected {
            let result = results[bits];
            assert!((Complex64::from_polar(1.0, result.phase_rad - phase) - 1.0).norm() < 2e-12);
            assert!((result.return_probability - 1.0).abs() < 2e-12);
        }
    }

    #[test]
    fn physical_ire24_protocol_remains_nearly_cyclic() {
        let results = simulate_cole_all(ColeParameters::ire24()).unwrap();
        for result in results.values() {
            assert!(result.return_probability > 0.999);
        }
        assert!((results["101"].amplitude_re - -0.999_997_783_720_750_9).abs() < 2e-14);
        assert!((results["101"].amplitude_im - 0.001_625_078_087_198_224_6).abs() < 2e-14);
        assert!((results["111"].amplitude_re - 0.999_997_788_985_548_9).abs() < 2e-14);
        assert!((results["111"].amplitude_im - -0.001_622_591_178_487_476_2).abs() < 2e-14);
    }

    #[test]
    fn phase_gradients_match_centered_finite_differences() {
        let segments = vec![
            Segment {
                duration_us: 0.017,
                omega_rb_mhz: 12.0,
                omega_cs_mhz: 15.0,
                phase_rb_rad: 0.31,
                phase_cs_rad: -0.27,
                delta_rb_mhz: 1.2,
                delta_cs_mhz: -2.3,
                v_rb_rb_mhz: 0.04,
                v_rb_cs_mhz: 31.0,
            },
            Segment {
                duration_us: 0.023,
                phase_rb_rad: -0.42,
                phase_cs_rad: 0.19,
                ..Segment {
                    duration_us: 0.017,
                    omega_rb_mhz: 12.0,
                    omega_cs_mhz: 15.0,
                    phase_rb_rad: 0.31,
                    phase_cs_rad: -0.27,
                    delta_rb_mhz: 1.2,
                    delta_cs_mhz: -2.3,
                    v_rb_rb_mhz: 0.04,
                    v_rb_cs_mhz: 31.0,
                }
            },
        ];
        let theta_rb = 0.13;
        let theta_cs = -0.21;
        let objective = phase_objective(&segments, theta_rb, theta_cs).unwrap();
        let epsilon = 1e-6;
        for (rb, analytic) in [
            (true, &objective.gradient_phase_rb),
            (false, &objective.gradient_phase_cs),
        ] {
            for index in 0..segments.len() {
                let mut plus = segments.clone();
                let mut minus = segments.clone();
                if rb {
                    plus[index].phase_rb_rad += epsilon;
                    minus[index].phase_rb_rad -= epsilon;
                } else {
                    plus[index].phase_cs_rad += epsilon;
                    minus[index].phase_cs_rad -= epsilon;
                }
                let numerical = ((1.0
                    - pulse_metrics(&plus, theta_rb, theta_cs).unwrap().fidelity)
                    - (1.0 - pulse_metrics(&minus, theta_rb, theta_cs).unwrap().fidelity))
                    / (2.0 * epsilon);
                assert!((analytic[index] - numerical).abs() < 2e-8);
            }
        }
        for (rb, analytic) in [
            (true, &objective.gradient_omega_rb),
            (false, &objective.gradient_omega_cs),
        ] {
            for index in 0..segments.len() {
                let mut plus = segments.clone();
                let mut minus = segments.clone();
                if rb {
                    plus[index].omega_rb_mhz += epsilon;
                    minus[index].omega_rb_mhz -= epsilon;
                } else {
                    plus[index].omega_cs_mhz += epsilon;
                    minus[index].omega_cs_mhz -= epsilon;
                }
                let numerical = ((1.0
                    - pulse_metrics(&plus, theta_rb, theta_cs).unwrap().fidelity)
                    - (1.0 - pulse_metrics(&minus, theta_rb, theta_cs).unwrap().fidelity))
                    / (2.0 * epsilon);
                assert!((analytic[index] - numerical).abs() < 2e-8);
            }
        }
        for (rb, analytic) in [
            (true, objective.gradient_theta_rb),
            (false, objective.gradient_theta_cs),
        ] {
            let plus = if rb {
                pulse_metrics(&segments, theta_rb + epsilon, theta_cs).unwrap()
            } else {
                pulse_metrics(&segments, theta_rb, theta_cs + epsilon).unwrap()
            };
            let minus = if rb {
                pulse_metrics(&segments, theta_rb - epsilon, theta_cs).unwrap()
            } else {
                pulse_metrics(&segments, theta_rb, theta_cs - epsilon).unwrap()
            };
            let numerical = ((1.0 - plus.fidelity) - (1.0 - minus.fidelity)) / (2.0 * epsilon);
            assert!((analytic - numerical).abs() < 2e-8);
        }
    }

    #[test]
    fn flagship_finite_pulse_matches_archived_result() {
        let artifact: FinitePulseArtifact = serde_json::from_str(include_str!(
            "../../../legacy/finite-677eba8/results/grape_phase_rate/jandura99_omega18_czz_81p5444ns_n99_v1.json"
        ))
        .unwrap();
        let metrics = pulse_metrics(
            &artifact.segments().unwrap(),
            artifact.theta_rb,
            artifact.theta_cs,
        )
        .unwrap();
        assert!((metrics.fidelity - artifact.discrete_staircase_fidelity).abs() < 3e-14);
        assert!((metrics.rydberg_exposure_us - 0.052_938_172_103_265_54).abs() < 2e-14);
        assert!((metrics.amplitudes["111"].amplitude_re - 0.322_457_893_675_138_6).abs() < 2e-14);
        assert!((metrics.amplitudes["111"].amplitude_im - -0.946_582_879_194_982_3).abs() < 2e-14);
    }
}
