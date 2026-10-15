//! Deterministic algebra, models, relaxations, certificates, and provenance for
//! minimum-exposure moment/SOS computations.

pub mod algebra;
pub mod assembly;
pub mod certificate;
pub mod conic;
pub mod estimate;
pub mod finite_blockade;
pub mod finite_sdp;
pub mod model;
pub mod monomial;
pub mod provenance;
pub mod result;
pub mod shared_control_lift;
pub mod stationary_certificate;
pub mod stationary_cost_rate_split;
pub mod stationary_hausdorff;
pub mod stationary_hausdorff_split;
pub mod stationary_torus;

pub use algebra::{Qsqrt2, Rational};
pub use estimate::{Estimate, estimate};
pub use model::{Model, ModelId, model};

/// On-disk schema version. Increment only for an incompatible serialization change.
pub const SCHEMA_VERSION: &str = "minexposure/v1";
