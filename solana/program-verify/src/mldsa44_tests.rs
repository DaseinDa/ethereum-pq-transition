//! Tests of the parts of the verifier against direct transcriptions of the algorithms of FIPS 204.
//! The verifier as a whole is compared with the `fips204` crate in `tests/differential.rs`.

use super::*;

/// SplitMix64, a deterministic generator.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn fill(&mut self, bytes: &mut [u8]) {
        for byte in bytes {
            *byte = self.next() as u8;
        }
    }

    /// A working memory of random 32-bit values.
    fn memory(&mut self) -> Memory {
        core::array::from_fn(|_| core::array::from_fn(|_| self.next() as u32))
    }
}

/// The polynomial in one field of the working memory.
fn get(memory: &Memory, field: usize) -> [u64; N] {
    core::array::from_fn(|i| u64::from(memory[i][field]))
}

fn set(memory: &mut Memory, field: usize, poly: &[u64; N]) {
    for (entry, &coefficient) in memory.iter_mut().zip(poly) {
        entry[field] = u32::try_from(coefficient).unwrap();
    }
}

/// True if `after` differs from `before` in the listed fields only.
fn only_changed(before: &Memory, after: &Memory, fields: &[usize]) -> bool {
    (0..FIELDS).filter(|field| !fields.contains(field)).all(|field| get(before, field) == get(after, field))
}

fn pow_mod(base: u64, exponent: u64) -> u64 {
    let mut result = 1;
    for _ in 0..exponent {
        result = result * base % Q;
    }
    result
}

/// The transform by its definition (FIPS 204, Section 2.5): entry j is the value of the polynomial at
/// zeta^(2 * BitRev8(j) + 1).
fn ntt_by_definition(w: &[u64; N]) -> [u64; N] {
    core::array::from_fn(|j| {
        let point = pow_mod(1753, 2 * u64::from((j as u8).reverse_bits()) + 1);
        w.iter().rev().fold(0, |value, &coefficient| (value * point + coefficient) % Q)
    })
}

/// BytesToBits, then BitsToInteger on fields of `width` bits (FIPS 204, Algorithms 12 and 10).
fn unpack(bytes: &[u8], width: usize) -> Vec<u64> {
    let bits: Vec<u64> = bytes.iter().flat_map(|&byte| (0..8).map(move |i| u64::from(byte >> i) & 1)).collect();
    bits.chunks_exact(width).map(|field| field.iter().rev().fold(0, |value, &bit| 2 * value + bit)).collect()
}

/// IntegerToBits on fields of `width` bits, then BitsToBytes (FIPS 204, Algorithms 9 and 11).
fn pack(values: &[u64], width: usize) -> Vec<u8> {
    let bits: Vec<u64> = values.iter().flat_map(|&value| (0..width).map(move |i| (value >> i) & 1)).collect();
    bits.chunks_exact(8).map(|byte| byte.iter().rev().fold(0, |value, &bit| 2 * value + bit as u8)).collect()
}

#[test]
fn constants() {
    assert_eq!((PUBLIC_KEY_LEN, SIGNATURE_LEN), (1312, 2420));
    assert_eq!((GAMMA2, C_TILDE_LEN, T1_POLY_LEN, Z_POLY_LEN, W1_POLY_LEN, HINT_LEN), (95_232, 32, 320, 576, 192, 84));
    assert_eq!(core::mem::size_of::<Memory>(), 7168);
    assert_eq!(256 * INV_N % Q, 1);
    // zeta = 1753 is a 512th root of unity whose 256th power is -1.
    assert_eq!(pow_mod(1753, 256), Q - 1);
    // The first entries of the table of FIPS 204, Appendix B (entry 0 is not used by the transform).
    assert_eq!(
        ZETAS[1..16],
        [
            4808194, 3765607, 3761513, 5178923, 5496691, 5234739, 5178987, 7778734, 3542485, 2682288, 2129892, 3764867,
            7375178, 557458, 7159240
        ]
    );
    for (k, &zeta) in ZETAS.iter().enumerate() {
        assert_eq!(u64::from(zeta), pow_mod(1753, u64::from((k as u8).reverse_bits())));
        assert!(u64::from(zeta) < Q);
    }
}

#[test]
fn ntt_matches_definition_and_bound() {
    let mut rng = Rng(1);
    for round in 0..70 {
        // Coefficients below 2q, the bound that `ntt` states; the first rounds use the extreme values.
        let input: [u64; N] = match round {
            0 => [2 * Q - 1; N],
            1 => [0; N],
            2 => core::array::from_fn(|i| if i % 2 == 0 { 2 * Q - 1 } else { 0 }),
            _ => core::array::from_fn(|_| rng.next() % (2 * Q)),
        };
        let field = round % FIELDS;
        let mut memory = rng.memory();
        set(&mut memory, field, &input);
        let before = memory;
        ntt(&mut memory, field);
        assert!(only_changed(&before, &memory, &[field]));
        let output = get(&memory, field);
        assert!(output.iter().all(|&x| x < 10 * Q));
        assert_eq!(output.map(|x| x % Q), ntt_by_definition(&input));
    }
}

#[test]
fn inv_ntt_inverts_and_bound() {
    let mut rng = Rng(2);
    for round in 0..70 {
        // Coefficients below q, as `inv_ntt` requires.
        let input: [u64; N] = match round {
            0 => [Q - 1; N],
            1 => [0; N],
            2 => core::array::from_fn(|i| if i % 2 == 0 { Q - 1 } else { 0 }),
            3 => core::array::from_fn(|i| if i % 2 == 1 { Q - 1 } else { 0 }),
            4 => core::array::from_fn(|i| if i < N / 2 { Q - 1 } else { 0 }),
            5 => core::array::from_fn(|i| if i < N / 2 { 0 } else { Q - 1 }),
            _ => core::array::from_fn(|_| rng.next() % Q),
        };
        let field = round % FIELDS;
        let mut memory = rng.memory();
        set(&mut memory, field, &input);
        let before = memory;
        inv_ntt(&mut memory, field);
        assert!(only_changed(&before, &memory, &[field]));
        let output = get(&memory, field);
        assert!(output.iter().all(|&x| x < 256 * Q));
        // After the factor 256^-1 the result is the polynomial whose transform is the input.
        assert_eq!(ntt_by_definition(&output.map(|x| INV_N * x % Q)), input);
    }
}

/// Decompose and UseHint (FIPS 204, Algorithms 36 and 40), transcribed with signed integers.
fn use_hint_by_definition(h: bool, r: i64) -> i64 {
    let (q, gamma2) = (Q as i64, GAMMA2 as i64);
    let m = (q - 1) / (2 * gamma2);
    let r_plus = r.rem_euclid(q);
    let mut r0 = r_plus.rem_euclid(2 * gamma2);
    if r0 > gamma2 {
        r0 -= 2 * gamma2;
    }
    let r1 = if r_plus - r0 == q - 1 {
        r0 -= 1;
        0
    } else {
        (r_plus - r0) / (2 * gamma2)
    };
    if h && r0 > 0 {
        (r1 + 1).rem_euclid(m)
    } else if h {
        (r1 - 1).rem_euclid(m)
    } else {
        r1
    }
}

#[test]
fn use_hint_matches_definition_for_every_residue() {
    for r in 0..Q {
        for hint in [false, true] {
            let got = use_hint(r, hint);
            assert!(got < 44);
            assert_eq!(got as i64, use_hint_by_definition(hint, r as i64), "r = {r}, hint = {hint}");
        }
    }
}

#[test]
fn use_hint_and_pack_matches_definition() {
    let mut rng = Rng(3);
    for round in 0..600 {
        // Any output of `inv_ntt`: values below 256q.
        let w: [u64; N] = core::array::from_fn(|_| match round {
            0 => 256 * Q - 1,
            1 => 0,
            _ => rng.next() % (256 * Q),
        });
        let mut memory = rng.memory();
        set(&mut memory, T, &w);
        // A strictly increasing list of positions, of any length up to 256.
        let chance = [0, 1, 20, 128, 256, 3][round % 6];
        let hints: Vec<u8> = (0..=255u8).filter(|_| rng.below(256) < chance).collect();
        let mut packed = [0u8; W1_POLY_LEN];
        use_hint_and_pack(&memory, &hints, &mut packed);
        let expected: Vec<u64> = (0..N)
            .map(|i| {
                let r = (INV_N as u128 * w[i] as u128 % Q as u128) as i64;
                use_hint_by_definition(hints.contains(&(i as u8)), r) as u64
            })
            .collect();
        assert_eq!(packed.to_vec(), pack(&expected, 6));
    }
}

#[test]
fn unpack_z_matches_definition_and_norm_bound() {
    let mut rng = Rng(4);
    let (mut accepted, mut rejected) = (0, 0);
    for round in 0..20_000 {
        let mut values: Vec<u64> = (0..N).map(|_| rng.next() % (1 << 18)).collect();
        // Most rounds keep every coefficient inside the norm bound and then place one value at or next to an
        // edge of the bound or of the 18-bit range.
        if round % 8 != 0 {
            for value in values.iter_mut() {
                *value = *value % (2 * GAMMA1 - 2 * BETA - 1) + BETA + 1;
            }
            let edges = [0, 1, 77, 78, 79, 80, 131_071, 131_072, 131_073, 262_064, 262_065, 262_066, 262_067, 262_143];
            if round % 8 != 1 {
                values[rng.below(N)] = edges[rng.below(edges.len())];
            }
        }
        let bytes: [u8; Z_POLY_LEN] = pack(&values, 18).try_into().unwrap();
        assert_eq!(unpack(&bytes, 18), values);
        // z = gamma1 - value, and the signature is acceptable if every |z| is below gamma1 - beta.
        let z: Vec<i64> = values.iter().map(|&value| GAMMA1 as i64 - value as i64).collect();
        let within = z.iter().all(|z| z.abs() < (GAMMA1 - BETA) as i64);
        let field = round % L;
        let mut memory = rng.memory();
        let before = memory;
        assert_eq!(unpack_z(&bytes, &mut memory, field), within);
        assert!(only_changed(&before, &memory, &[field]));
        if within {
            accepted += 1;
            let stored = get(&memory, field);
            assert_eq!(stored.map(|x| x as i64).to_vec(), z.iter().map(|z| Q as i64 + z).collect::<Vec<_>>());
            assert!(stored.iter().all(|&x| x < 2 * Q));
        } else {
            rejected += 1;
        }
    }
    assert!(accepted > 5_000 && rejected > 5_000, "{accepted} accepted, {rejected} rejected");
}

#[test]
fn unpack_t1_matches_definition() {
    let mut rng = Rng(5);
    for round in 0..2_000 {
        let mut bytes = [0u8; T1_POLY_LEN];
        match round {
            0 => bytes.fill(0xff),
            1 => {}
            _ => rng.fill(&mut bytes),
        }
        let mut memory = rng.memory();
        let before = memory;
        unpack_t1_scaled(&bytes, &mut memory);
        assert!(only_changed(&before, &memory, &[T]));
        let stored = get(&memory, T);
        assert_eq!(stored.to_vec(), unpack(&bytes, 10).iter().map(|t1| t1 << D).collect::<Vec<_>>());
        assert!(stored.iter().all(|&x| x < Q));
    }
}

/// HintBitUnpack (FIPS 204, Algorithm 21), transcribed: the K polynomials of hint bits, or `None`.
fn hint_bit_unpack_by_definition(y: &[u8; HINT_LEN]) -> Option<[[bool; N]; K]> {
    let mut h = [[false; N]; K];
    let mut index = 0usize;
    for i in 0..K {
        if usize::from(y[OMEGA + i]) < index || usize::from(y[OMEGA + i]) > OMEGA {
            return None;
        }
        let first = index;
        while index < usize::from(y[OMEGA + i]) {
            if index > first && y[index - 1] >= y[index] {
                return None;
            }
            h[i][usize::from(y[index])] = true;
            index += 1;
        }
    }
    for i in index..OMEGA {
        if y[i] != 0 {
            return None;
        }
    }
    Some(h)
}

/// A well-formed hint with random lists.
fn well_formed_hint(rng: &mut Rng) -> [u8; HINT_LEN] {
    let mut y = [0u8; HINT_LEN];
    let mut index = 0;
    for i in 0..K {
        let count = rng.below(OMEGA - index + 1).min(rng.below(40));
        let chance = rng.below(257);
        let positions: Vec<u8> = (0..=255u8).filter(|_| rng.below(256) < chance).take(count).collect();
        y[index..index + positions.len()].copy_from_slice(&positions);
        index += positions.len();
        y[OMEGA + i] = index as u8;
    }
    y
}

#[test]
fn hint_checks_match_definition() {
    let mut rng = Rng(6);
    let (mut well_formed, mut malformed) = (0, 0);
    for round in 0..300_000 {
        let mut y = well_formed_hint(&mut rng);
        match round % 8 {
            // Unchanged.
            0 => {}
            // Random bytes.
            1 => rng.fill(&mut y),
            // One random byte anywhere.
            2 => y[rng.below(HINT_LEN)] = rng.next() as u8,
            // One end offset changed by one, or set at random.
            3 => {
                let i = OMEGA + rng.below(K);
                y[i] = match rng.below(3) {
                    0 => y[i].wrapping_add(1),
                    1 => y[i].wrapping_sub(1),
                    _ => rng.below(OMEGA + 4) as u8,
                };
            }
            // Two neighbouring positions swapped or made equal.
            4 => {
                let i = rng.below(OMEGA - 1);
                if rng.below(2) == 0 {
                    y.swap(i, i + 1);
                } else {
                    y[i + 1] = y[i];
                }
            }
            // A byte after the lists set.
            5 => {
                let used = usize::from(y[OMEGA + K - 1]);
                if used < OMEGA {
                    y[used + rng.below(OMEGA - used)] = rng.next() as u8;
                }
            }
            // One bit flipped.
            6 => y[rng.below(HINT_LEN)] ^= 1 << rng.below(8),
            // Several bytes set to small values.
            _ => {
                for _ in 0..1 + rng.below(3) {
                    y[rng.below(HINT_LEN)] = rng.below(OMEGA + 2) as u8;
                }
            }
        }
        let expected = hint_bit_unpack_by_definition(&y);
        let got = hint_list_ends(&y).map(|ends| {
            let mut h = [[false; N]; K];
            let mut from = 0;
            for (row, &to) in h.iter_mut().zip(&ends) {
                for &position in &y[from..to] {
                    row[usize::from(position)] = true;
                }
                from = to;
            }
            h
        });
        assert_eq!(got, expected, "hint {y:?}");
        if expected.is_some() {
            well_formed += 1;
        } else {
            malformed += 1;
        }
    }
    assert!(well_formed > 30_000 && malformed > 30_000, "{well_formed} well-formed, {malformed} malformed");
}

#[test]
fn challenge_has_tau_signs() {
    let mut rng = Rng(7);
    for _ in 0..2_000 {
        let mut c_tilde = [0u8; C_TILDE_LEN];
        rng.fill(&mut c_tilde);
        let mut memory = rng.memory();
        set(&mut memory, C, &[0; N]);
        let before = memory;
        sample_in_ball_negated(&c_tilde, &mut memory);
        assert!(only_changed(&before, &memory, &[C]));
        let minus_c = get(&memory, C);
        let ones = minus_c.iter().filter(|&&x| x == 1).count();
        let minus_ones = minus_c.iter().filter(|&&x| x == Q - 1).count();
        let zeros = minus_c.iter().filter(|&&x| x == 0).count();
        assert_eq!((ones + minus_ones, zeros), (TAU, N - TAU));
        assert!(minus_c[..N - TAU].iter().filter(|&&x| x != 0).count() <= TAU);
    }
}

/// RejNTTPoly (FIPS 204, Algorithm 30) for the entry of A in `row` and `column` (Algorithm 32), transcribed:
/// three bytes at a time from SHAKE128.
fn matrix_entry_by_definition(rho: &[u8; RHO_LEN], row: u8, column: u8) -> [u64; N] {
    let mut hash = Shake128::default();
    hash.update(rho);
    hash.update(&[column]);
    hash.update(&[row]);
    let mut xof = hash.finalize_xof();
    let mut a = [0u64; N];
    let mut j = 0;
    while j < N {
        let mut s = [0u8; 3];
        xof.read(&mut s);
        let value = u64::from(s[0]) + 256 * u64::from(s[1]) + 65_536 * u64::from(s[2] & 127);
        if value < Q {
            a[j] = value;
            j += 1;
        }
    }
    a
}

#[test]
fn expand_a_mul_add_matches_definition() {
    let mut rng = Rng(8);
    for round in 0..200 {
        let mut rho = [0u8; RHO_LEN];
        rng.fill(&mut rho);
        let (row, column) = ((round % K) as u8, (round / K % L) as u8);
        // Any 32-bit values in the field of z; a sum below q.
        let mut memory = rng.memory();
        let sum: [u64; N] = core::array::from_fn(|_| if round == 0 { Q - 1 } else { rng.next() % Q });
        set(&mut memory, SUM, &sum);
        if round == 0 {
            set(&mut memory, Z + usize::from(column), &[u64::from(u32::MAX); N]);
        }
        let before = memory;
        match column {
            0 => expand_a_mul_add::<0>(&rho, row, &mut memory),
            1 => expand_a_mul_add::<1>(&rho, row, &mut memory),
            2 => expand_a_mul_add::<2>(&rho, row, &mut memory),
            _ => expand_a_mul_add::<3>(&rho, row, &mut memory),
        }
        assert!(only_changed(&before, &memory, &[SUM]));
        let a = matrix_entry_by_definition(&rho, row, column);
        let z = get(&before, Z + usize::from(column));
        let expected: [u64; N] =
            core::array::from_fn(|i| ((sum[i] as u128 + a[i] as u128 * z[i] as u128) % Q as u128) as u64);
        assert_eq!(get(&memory, SUM), expected);
    }
}

#[test]
fn add_sum_and_product_matches_definition() {
    let mut rng = Rng(9);
    for round in 0..200 {
        let mut memory = rng.memory();
        if round == 0 {
            set(&mut memory, C, &[u64::from(u32::MAX); N]);
            set(&mut memory, T, &[u64::from(u32::MAX); N]);
            set(&mut memory, SUM, &[u64::from(u32::MAX); N]);
        }
        let before = memory;
        add_sum_and_product(&mut memory);
        assert!(only_changed(&before, &memory, &[T, SUM]));
        let (sum, c, t) = (get(&before, SUM), get(&before, C), get(&before, T));
        let expected: [u64; N] =
            core::array::from_fn(|i| ((sum[i] as u128 + c[i] as u128 * t[i] as u128) % Q as u128) as u64);
        assert_eq!(get(&memory, T), expected);
        assert_eq!(get(&memory, SUM), [0; N]);
    }
}
