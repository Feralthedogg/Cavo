//! SHA-256 (FIPS 180-4), used as an identity, never as an authorization decision.
//! https://csrc.nist.gov/pubs/fips/180-4/upd1/final
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Digest(pub [u8; 32]);
impl Digest {
    pub fn parse(value: &str) -> Option<Self> {
        let hex = value.strip_prefix("sha256:")?;
        if hex.len() != 64 {
            return None;
        }
        let mut bytes = [0; 32];
        for (out, pair) in bytes.iter_mut().zip(hex.as_bytes().chunks_exact(2)) {
            let digit = |byte| match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                _ => None,
            };
            *out = digit(pair[0])? * 16 + digit(pair[1])?;
        }
        Some(Self(bytes))
    }
}
impl fmt::Display for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("sha256:")?;
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

pub fn sha256(input: &[u8]) -> Digest {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut state = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];
    let blocks = input.len().saturating_add(9).div_ceil(64);
    for block in 0..blocks {
        let mut bytes = [0; 64];
        for (i, out) in bytes.iter_mut().enumerate() {
            let offset = block * 64 + i;
            if offset < input.len() {
                *out = input[offset];
            } else if offset == input.len() {
                *out = 0x80;
            }
        }
        if block + 1 == blocks {
            bytes[56..].copy_from_slice(&(input.len() as u64).wrapping_mul(8).to_be_bytes());
        }
        let mut w = [0u32; 64];
        for (out, word) in w.iter_mut().zip(bytes.chunks_exact(4)) {
            *out = u32::from_be_bytes(word.try_into().expect("four bytes"));
        }
        for i in 16..64 {
            let x = w[i - 15];
            let y = w[i - 2];
            let s0 = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
            let s1 = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (out, add) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *out = out.wrapping_add(add);
        }
    }
    let mut bytes = [0; 32];
    for (out, word) in bytes.chunks_exact_mut(4).zip(state) {
        out.copy_from_slice(&word.to_be_bytes());
    }
    Digest(bytes)
}
