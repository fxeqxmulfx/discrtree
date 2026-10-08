//! Numeric spelling without evaluating a Lean expression or bounding its Nat.

/// Decimal and hexadecimal numerals share the decimal value recorded by Lean.
pub(super) fn natural(text: &str) -> Option<String> {
    if let Some(hex) = text.strip_prefix("0x") {
        if hex.is_empty() || !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        let mut decimal = vec![0u8];
        for digit in hex.chars().filter_map(|c| c.to_digit(16)) {
            let mut carry = digit;
            for d in &mut decimal {
                carry += u32::from(*d) * 16;
                *d = (carry % 10) as u8;
                carry /= 10;
            }
            while carry > 0 {
                decimal.push((carry % 10) as u8);
                carry /= 10;
            }
        }
        return Some(decimal.iter().rev().map(|d| char::from(b'0' + d)).collect());
    }
    (!text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()))
        .then(|| trimmed(text).to_string())
}

fn trimmed(text: &str) -> &str {
    let trimmed = text.trim_start_matches('0');
    if trimmed.is_empty() { "0" } else { trimmed }
}

/// A decimal mantissa times a signed power of ten, with trailing zeroes
/// removed. Neither a huge mantissa nor a huge exponent is expanded.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct Scientific {
    pub mantissa: String,
    pub negative: bool,
    pub exponent: String,
}

impl Scientific {
    pub fn parse(text: &str) -> Option<Self> {
        let (mantissa, exponent) = text.split_once(['e', 'E']).unwrap_or((text, "0"));
        let negative = exponent.starts_with('-');
        let exponent = natural(exponent.strip_prefix(['+', '-']).unwrap_or(exponent))?;
        let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        if whole.is_empty()
            || !whole.bytes().all(|b| b.is_ascii_digit())
            || !fraction.bytes().all(|b| b.is_ascii_digit())
        {
            return None;
        }
        let mut value =
            Self { mantissa: natural(&format!("{whole}{fraction}"))?, negative, exponent };
        value.shift(fraction.len(), true);
        Some(value.normalize())
    }

    pub fn from_parts(mantissa: &str, negative: bool, exponent: &str) -> Option<Self> {
        Some(
            Self { mantissa: natural(mantissa)?, negative, exponent: natural(exponent)? }
                .normalize(),
        )
    }

    fn normalize(mut self) -> Self {
        if self.mantissa == "0" {
            self.negative = false;
            self.exponent = "0".into();
        } else {
            let digits = self.mantissa.trim_end_matches('0').len();
            self.shift(self.mantissa.len() - digits, false);
            self.mantissa.truncate(digits);
            if self.exponent == "0" {
                self.negative = false;
            }
        }
        self
    }

    fn shift(&mut self, places: usize, negative: bool) {
        if places == 0 {
            return;
        }
        let places = places.to_string();
        if self.negative == negative {
            self.exponent = add(&self.exponent, &places);
        } else if (self.exponent.len(), &self.exponent) >= (places.len(), &places) {
            self.exponent = subtract(&self.exponent, &places);
        } else {
            self.exponent = subtract(&places, &self.exponent);
            self.negative = negative;
        }
    }
}

fn add(a: &str, b: &str) -> String {
    let mut b = b.bytes().rev();
    let mut carry = 0;
    let mut result = Vec::new();
    for digit in a.bytes().rev().chain(std::iter::repeat_n(b'0', b.len().saturating_sub(a.len()))) {
        carry += digit - b'0' + b.next().map_or(0, |digit| digit - b'0');
        result.push(b'0' + carry % 10);
        carry /= 10;
    }
    if carry > 0 {
        result.push(b'0' + carry);
    }
    result.reverse();
    String::from_utf8(result).expect("decimal digits")
}

/// Subtract a smaller nonnegative decimal number from a larger one.
fn subtract(a: &str, b: &str) -> String {
    let mut b = b.bytes().rev();
    let mut borrow = 0i16;
    let mut result = Vec::new();
    for digit in a.bytes().rev() {
        let difference =
            i16::from(digit - b'0') - b.next().map_or(0, |digit| i16::from(digit - b'0')) - borrow;
        borrow = i16::from(difference < 0);
        result.push(b'0' + difference.rem_euclid(10) as u8);
    }
    result.reverse();
    trimmed(std::str::from_utf8(&result).expect("decimal digits")).to_string()
}
