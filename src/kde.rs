use std::f64::consts::PI;

/// Gaussian kernel density estimator (dependency-free).
pub struct Kde {
    data: Vec<f64>,
    bandwidth: f64,
}

impl Kde {
    /// Creates a KDE. If `bandwidth` is `None`, Silverman's rule of thumb is used.
    pub fn new(data: &[f64], bandwidth: Option<f64>) -> Result<Self, String> {
        if data.len() < 2 {
            return Err("need at least 2 samples".into());
        }
        if data.iter().any(|x| !x.is_finite()) {
            return Err("samples must be finite".into());
        }

        let h = match bandwidth {
            Some(h) => h,
            None => silverman_bandwidth(data),
        };
        if !(h > 0.0 && h.is_finite()) {
            return Err("bandwidth must be positive and finite (data may be constant)".into());
        }

        Ok(Self {
            data: data.to_vec(),
            bandwidth: h,
        })
    }

    pub fn bandwidth(&self) -> f64 {
        self.bandwidth
    }

    /// Density estimate at a single point. O(n).
    pub fn pdf(&self, x: f64) -> f64 {
        let inv_h = 1.0 / self.bandwidth;
        let sum: f64 = self
            .data
            .iter()
            .map(|&xi| {
                let u = (x - xi) * inv_h;
                (-0.5 * u * u).exp()
            })
            .sum();
        sum / (self.data.len() as f64 * self.bandwidth * (2.0 * PI).sqrt())
    }

    /// Evaluates the density on `m` evenly spaced points in `[lo, hi]`. O(n * m).
    pub fn evaluate_grid(&self, lo: f64, hi: f64, m: usize) -> Vec<(f64, f64)> {
        assert!(m >= 2, "grid needs at least 2 points");
        let step = (hi - lo) / (m - 1) as f64;
        (0..m)
            .map(|i| {
                let x = lo + step * i as f64;
                (x, self.pdf(x))
            })
            .collect()
    }
}

/// Silverman's rule: h = 0.9 * min(sd, IQR / 1.34) * n^(-1/5).
/// Falls back to sd if IQR is zero. Returns 0.0 for constant data.
fn silverman_bandwidth(data: &[f64]) -> f64 {
    let n = data.len() as f64;
    let mean = data.iter().sum::<f64>() / n;
    let sd = (data.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1.0)).sqrt();

    let mut sorted = data.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap()); // finite values, so no NaN
    let iqr = quantile(&sorted, 0.75) - quantile(&sorted, 0.25);

    let spread = if iqr > 0.0 { sd.min(iqr / 1.34) } else { sd };
    0.9 * spread * n.powf(-0.2)
}

/// Linear-interpolated quantile of a sorted slice.
fn quantile(sorted: &[f64], p: f64) -> f64 {
    let pos = p * (sorted.len() - 1) as f64;
    let lo = pos.floor() as usize;
    let hi = pos.ceil() as usize;
    let frac = pos - lo as f64;
    sorted[lo] + frac * (sorted[hi] - sorted[lo])
}

pub fn kde(data: &[f64], lo: f64, hi: f64, m: usize) -> Vec<(f64, f64)> {
    let kd = Kde::new(data, None).expect("valid input");
    println!("bandwidth = {:.4}", kd.bandwidth());
    for (x, y) in kd.evaluate_grid(0.0, 9.0, 10) {
        println!("{x:6.2}  {y:.5}");
    }
    kd.evaluate_grid(lo, hi, m)
}

pub fn hist(data: &[f64], lo: f64, hi: f64, m: usize) -> Vec<(usize, f64)> {
    let mut bands: Vec<f64> = vec![0.0; m];
    let step: f64 = (hi - lo) / (m as f64);
    for d in data.iter() {
        let i: usize = (d / step).clamp(0.0, (m - 1) as f64) as usize;
        bands[i] += 1.0;
    }
    bands
        .into_iter()
        .enumerate()
        // .map(|(i, h)| (i as f64 * step + lo, h))
        .collect::<Vec<_>>()
}
