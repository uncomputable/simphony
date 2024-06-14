use std::fmt;
use std::str::FromStr;

/// Implementation for newtypes that wrap a number `u8`, `u16`, ...
/// such that the number has some property.
/// The newtype needs to have a constructor `Self::new(inner) -> Option<Self>`.
macro_rules! checked_num {
    (
        $wrapper: ident,
        $inner: ty,
        $description: expr
    ) => {
        impl $wrapper {
            /// Access the value as a primitive type.
            pub const fn get(&self) -> usize {
                self.0
            }
        }

        impl std::fmt::Display for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::fmt::Debug for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(self, f)
            }
        }

        impl std::str::FromStr for $wrapper {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                let n = s.parse::<$inner>().map_err(|e| e.to_string())?;
                Self::new(n).ok_or(format!("{s} is not {}", $description))
            }
        }
    };
}

/// An integer that is known to be a power of two with nonzero exponent.
///
/// The integer is equal to 2^n for some n > 0.
///
/// The integer is strictly greater than 1.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct NonZeroPow2Usize(usize);

impl NonZeroPow2Usize {
    /// Smallest power of two with nonzero exponent.
    // FIXME `std::option::Option::<T>::unwrap` is not yet stable as a const fn
    // pub const TWO: Self = Self::new(2).unwrap();
    pub const TWO: Self = Self(2);

    /// Create a power of two with nonzero exponent.
    pub const fn new(n: usize) -> Option<Self> {
        if n.is_power_of_two() && 1 < n {
            Some(Self(n))
        } else {
            None
        }
    }

    /// Create the smallest power of two with nonzero exponent greater equal `n`.
    pub const fn next(n: usize) -> Self {
        if n < 2 {
            Self::TWO
        } else {
            // FIXME `std::option::Option::<T>::unwrap` is not yet stable as a const fn
            // Self::new(n.next_power_of_two()).unwrap()
            Self(n.next_power_of_two())
        }
    }

    /// Return the binary logarithm of the value.
    ///
    /// The integer is equal to 2^n. Return n.
    pub const fn log2(self) -> u32 {
        self.0.trailing_zeros()
    }
}

checked_num!(NonZeroPow2Usize, usize, "a power of two greater than 1");

/// An integer that is known to be a power _of a power_ of two.
///
/// The integer is equal to 2^(2^n) for some n ≥ 0.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct DoublePow2Usize(usize);

checked_num!(DoublePow2Usize, usize, "a double power of two");

impl DoublePow2Usize {
    /// Create a double power of two.
    pub const fn new(n: usize) -> Option<Self> {
        if n.is_power_of_two() && n.trailing_zeros().is_power_of_two() {
            Some(Self(n))
        } else {
            None
        }
    }

    /// Return the binary logarithm _of the binary logarithm_ of the value.
    ///
    /// The integer is equal to 2^(2^n). Return n.
    pub const fn log2_log2(self) -> u32 {
        self.0.trailing_zeros().trailing_zeros()
    }
}

/// A 256-bit unsigned integer.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct U256([u8; 32]);

impl U256 {
    /// The smallest value that can be represented by this integer type (0).
    pub const MIN: Self = Self([0; 32]);
    /// The largest value that can be represented by this integer type (2²⁵⁶ − 1).
    pub const MAX: Self = Self([255; 32]);
    /// The number of decimal digits of [`Self::MAX`].
    const MAX_DIGITS: usize = 78;

    /// Create a 256-bit unsigned integer from a byte array.
    ///
    /// The byte array is in Big Endian order.
    pub fn from_byte_array(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Convert the integer to a byte array.
    ///
    /// The byte array is in Big Endian order.
    pub fn to_byte_array(self) -> [u8; 32] {
        self.0
    }
}

impl AsRef<[u8]> for U256 {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl From<u8> for U256 {
    fn from(value: u8) -> Self {
        let mut bytes = [0; 32];
        bytes[31] = value;
        Self(bytes)
    }
}

impl From<u16> for U256 {
    fn from(value: u16) -> Self {
        let mut bytes = [0; 32];
        let value_bytes = value.to_be_bytes();
        bytes[30..].copy_from_slice(&value_bytes);
        Self(bytes)
    }
}

impl From<u32> for U256 {
    fn from(value: u32) -> Self {
        let mut bytes = [0; 32];
        let value_bytes = value.to_be_bytes();
        bytes[28..].copy_from_slice(&value_bytes);
        Self(bytes)
    }
}

impl From<u64> for U256 {
    fn from(value: u64) -> Self {
        let mut bytes = [0; 32];
        let bot_eight = value.to_be_bytes();
        bytes[24..].copy_from_slice(&bot_eight);
        Self(bytes)
    }
}

impl From<u128> for U256 {
    fn from(value: u128) -> Self {
        let mut bytes = [0; 32];
        let value_bytes = value.to_be_bytes();
        bytes[16..].copy_from_slice(&value_bytes);
        Self(bytes)
    }
}

impl fmt::Display for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bytes = self.0;
        let mut digits = Vec::with_capacity(Self::MAX_DIGITS);
        let mut is_zero = false;

        while !is_zero {
            let mut carry = 0;
            is_zero = true;

            // Divide by 10, starting at the most significant bytes
            for byte in bytes.iter_mut() {
                let value = carry * 256 + *byte as u32;
                *byte = (value / 10) as u8;
                carry = value % 10;

                if *byte != 0 {
                    is_zero = false;
                }
            }

            digits.push(carry as u8);
        }

        for digit in digits.iter().rev() {
            write!(f, "{}", digit)?;
        }

        Ok(())
    }
}

impl FromStr for U256 {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let decimal = s.trim_start_matches('0');
        if Self::MAX_DIGITS < decimal.chars().count() {
            return Err(ParseIntError::PosOverflow);
        }
        let mut bytes = [0; 32];

        for ch in decimal.chars() {
            let mut carry = ch.to_digit(10).ok_or(ParseIntError::InvalidDigit)?;

            // Add to the least significant bytes first
            for byte in bytes.iter_mut().rev() {
                let value = *byte as u32 * 10 + carry;
                *byte = (value % 256) as u8;
                carry = value / 256;
            }
            if 0 < carry {
                return Err(ParseIntError::PosOverflow);
            }
        }

        Ok(Self(bytes))
    }
}

/// Reimplementation of [`std::num::ParseIntError`] that we can construct.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ParseIntError {
    InvalidDigit,
    PosOverflow,
}

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDigit => write!(f, "Invalid decimal digit"),
            Self::PosOverflow => write!(f, "Number too large to fit in target type"),
        }
    }
}

impl std::error::Error for ParseIntError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_u256_invalid_digit() {
        assert_eq!(Err(ParseIntError::InvalidDigit), "a".parse::<U256>());
    }

    #[test]
    fn parse_u256_overflow() {
        let u256_max_plus_one =
            "115792089237316195423570985008687907853269984665640564039457584007913129639936";
        assert_eq!(
            Err(ParseIntError::PosOverflow),
            u256_max_plus_one.parse::<U256>()
        );
        let u256_max_times_ten =
            "1157920892373161954235709850086879078532699846656405640394575840079131296399350";
        assert_eq!(
            Err(ParseIntError::PosOverflow),
            u256_max_times_ten.parse::<U256>()
        );
    }

    #[test]
    fn parse_u256_leading_zeroes() {
        assert_eq!(U256::MIN, "00".parse().unwrap());
        assert_eq!(
            U256::MAX,
            "0115792089237316195423570985008687907853269984665640564039457584007913129639935"
                .parse()
                .unwrap()
        );
    }

    #[test]
    fn parse_u256_ok() {
        for n in 0u8..=255 {
            let s = n.to_string();
            assert_eq!(U256::from(n), s.parse().unwrap());
        }
        assert_eq!(
            U256::from(u128::MAX),
            "340282366920938463463374607431768211455".parse().unwrap(),
        );
        assert_eq!(
            U256::MAX,
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
                .parse()
                .unwrap()
        );
    }

    #[test]
    fn display_u256() {
        for n in 0u8..=255 {
            assert_eq!(n.to_string(), U256::from(n).to_string());
        }
        assert_eq!(u128::MAX.to_string(), U256::from(u128::MAX).to_string());
        assert_eq!(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            &U256::MAX.to_string()
        )
    }
}
