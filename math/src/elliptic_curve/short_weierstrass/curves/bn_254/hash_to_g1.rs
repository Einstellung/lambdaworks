use super::{
    curve::BN254Curve,
    field_extension::{BN254PrimeField, Degree12ExtensionField, Degree2ExtensionField},
    twist::BN254TwistCurve,
};
use crate::elliptic_curve::traits::FromAffine;
use crate::field::traits::LegendreSymbol;
use crate::{
    cyclic_group::IsGroup,
    elliptic_curve::{short_weierstrass::traits::IsShortWeierstrass, traits::IsPairing},
    errors::PairingError,
};
use crate::{
    elliptic_curve::short_weierstrass::{
        curves::bn_254::field_extension::Degree6ExtensionField,
        point::ShortWeierstrassProjectivePoint,
    },
    field::element::FieldElement,
};
use ibig::UBig;

type FpE = FieldElement<BN254PrimeField>;
type Fp2E = FieldElement<Degree2ExtensionField>;
type Fp6E = FieldElement<Degree6ExtensionField>;
type Fp12E = FieldElement<Degree12ExtensionField>;
type G1Point = ShortWeierstrassProjectivePoint<BN254Curve>;
type G2Point = ShortWeierstrassProjectivePoint<BN254TwistCurve>;

/// Constants
/// c1 = g(Z)
/// c2 = -Z / 2
/// c3 = sqrt(-g(Z) * (3 * Z² + 4 * A))     # sgn0(c3) MUST equal 0
/// c4 = -4 * g(Z) / (3 * Z² + 4 * A)

/// Z := fp.Element{15230403791020821917, 754611498739239741, 7381016538464732716, 1011752739694698287}
/// c1 := fp.Element{1248766071674976557, 10548065924188627562, 16242874202584236114, 560012691975822483}
/// c2 := fp.Element{12997850613838968789, 14304628359724097447, 2950087706404981016, 1237622763554136189}
/// c3 := fp.Element{8972444824031832946, 5898165201680709844, 10690697896010808308, 824354360198587078}
/// c4 := fp.Element{12077013577332951089, 1872782865047492001, 13514471836495169457, 415649166299893576}

/// TODO: Change constants doing multiplying by R.inv() as in  
/// https://github.com/hashcloak/bn254-hash-to-curve/blob/main/src/hash2g1.rs#L160
pub const Z: FpE =
    FpE::from_hex_unchecked("E0A77C19A07DF2F666EA36F7879462C0A78EB28F5C70B3DD35D438DC58F0D9D");
pub const C1: FpE =
    FpE::from_hex_unchecked("7C5909386EDDC93E16A48076063C052926242126EAA626A115482203DBF392D");
pub const C2: FpE =
    FpE::from_hex_unchecked("112CEB58A394E07D28F0D12384840918C6843FB439555FA7B461A4448976F7D5");
pub const C3: FpE =
    FpE::from_hex_unchecked("B70B1EC48AE62C6945CFD183CBD7BF451DA7E0048BFB8D47C8487078735AB72");
pub const C4: FpE =
    FpE::from_hex_unchecked("5C4AEB6EC7E0F48BB8D0C885550C7B119FD7617E49815A1A79A2BDCA0800831");

pub fn MapToCurve(u: &FpE) -> G1Point {
    let mut tv1 = u.square();
    tv1 = tv1 * C1;
    let tv2 = FpE::one() + &tv1;
    let mut tv3 = tv1 * &tv2;
    tv3 = tv3.inv().unwrap();
    let mut tv4 = u * tv1;
    tv4 = tv4 * &tv3;
    tv4 = &tv3 * C3;

    let x1 = C2 - &tv4;

    let mut gx1 = x1.square();
    gx1 = gx1 * x1;
    gx1 = gx1 + BN254Curve::b();

    let x2 = C2 + &tv4;
    let mut gx2 = x2.square();
    gx2 = gx2 * x2;
    gx2 = gx2 + BN254Curve::b();

    let mut x3 = tv2.square();
    x3 = x3 * &tv3;
    x3 = x3.square();
    x3 = x3 * C4;

    x3 = x3 + Z;

    // TODO: match
    let mut x = if gx1.legendre_symbol() == LegendreSymbol::One {
        &x1
    } else {
        &x3
    };

    if gx2.legendre_symbol() == LegendreSymbol::One
        && !(gx1.legendre_symbol() == LegendreSymbol::One)
    {
        x = &x2
    }

    let mut gx = x.square();
    gx = gx * x;
    gx = gx + BN254Curve::b();

    let (y1, y2) = gx.sqrt().unwrap();

    let mut y = y1;

    let signs_not_equal = g1_sign_0(&u) ^ g1_sign_0(&y);

    if signs_not_equal == 0 {
        y = y
    } else {
        y = y2
    }

    G1Point::from_affine(x.clone(), y).unwrap()
}

fn g1_sign_0(x: &FpE) -> u64 {
    let t: UBig = x.into();
    *UBig::to_bytes_le(&t).get(0).unwrap() as u64 & 1
}
