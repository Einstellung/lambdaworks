use super::hash_to_field::hash_to_field;
use super::sha3::Sha3Hasher;

use ibig::UBig;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::bn_254::field_extension::{
    BN254PrimeField, Degree12ExtensionField, Degree2ExtensionField,
};
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::bn_254::{
    curve::BN254Curve, twist::BN254TwistCurve,
};
use lambdaworks_math::field::traits::LegendreSymbol;
use lambdaworks_math::unsigned_integer::element::U256;
use lambdaworks_math::{
    cyclic_group::IsGroup,
    elliptic_curve::{short_weierstrass::traits::IsShortWeierstrass, traits::IsPairing},
    errors::PairingError,
};
use lambdaworks_math::{
    elliptic_curve::short_weierstrass::{
        curves::bn_254::field_extension::Degree6ExtensionField,
        point::ShortWeierstrassProjectivePoint,
    },
    field::element::FieldElement,
};
use lambdaworks_math::{elliptic_curve::traits::FromAffine, traits::ByteConversion};

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

pub fn map_to_curve(u: &FpE) -> G1Point {
    let mut tv1 = u.square();
    tv1 = tv1 * C1;
    let tv2 = FpE::one() + &tv1;
    let mut tv3 = &tv1 * &tv2;
    tv3 = tv3.inv().unwrap();
    let mut tv4 = u * tv1;
    tv4 = tv4 * &tv3;
    tv4 = &tv3 * C3;

    let x1 = C2 - &tv4;

    let mut gx1 = x1.square();
    gx1 = gx1 * &x1;
    gx1 = gx1 + BN254Curve::b();

    let x2 = C2 + &tv4;
    let mut gx2 = x2.square();
    gx2 = gx2 * &x2;
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

// g1Sgn0 is an algebraic substitute for the notion of sign in ordered fields
// Namely, every non-zero quadratic residue in a finite field of characteristic =/= 2 has exactly two square roots, one of each sign
// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#name-the-sgn0-function
// See https://github.com/hashcloak/bn254-hash-to-curve/blob/main/src/hash2g1.rs#L225
fn g1_sign_0(x: &FpE) -> u64 {
    let t = x.value();
    t.to_bytes_le()[0] as u64 & 1
}

///  For the expand_message the implementation that we are following has
///   let len_per_elm = 48;
/// len_in_bytes = count * len_per_elm;
//  let len_in_bytes = count * len_per_elm;
/// and count is 2s
mod tests {
    use super::*;
    use crate::hash::hash_to_field::hash_to_field;

    #[test]
    #[allow(non_snake_case)]
    fn map_to_curve_test() {
        let u = hash_to_field(
            &Sha3Hasher::expand_message(
                b"abc",
                b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_",
                64,
            )
            .unwrap(),
            2,
        );
        let q0 = map_to_curve(&u[0]);
        let q1 = map_to_curve(&u[1]);
        assert!(
            q0 == G1Point::from_affine(
                FpE::new(U256::from_hex_unchecked(
                    "1452C8CC24F8DEDC25B24D89B87B64E25488191CECC78464FEA84077DD156F8D"
                )),
                FpE::new(U256::from_hex_unchecked(
                    "209C3633505BA956F5CE4D974A868DB972B8F1B69D63C218D360996BCEC1AD41"
                ))
            )
            .unwrap()
        );
        assert!(
            q1 == G1Point::from_affine(
                FpE::new(U256::from_hex_unchecked(
                    "4E8357C98524E6208AE2B771E370F0C449E839003988C2E4CE1EAF8D632559F"
                )),
                FpE::new(U256::from_hex_unchecked(
                    "4396EC43DD8EC8F2B4A705090B5892219759DA30154C39490FC4D59D51BB817"
                ))
            )
            .unwrap()
        );

        let u = FpE::hash_to_field(
            b"abcdef0123456789",
            b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_",
            2,
        );
        assert!(
            u[0] == FpE::from_hex_unchecked(
                "2F7993A6B43A8DBB37060E790011A888157F456B895B925C3568690685F4983D"
            )
        );
        assert!(
            u[1] == FpE::from_hex_unchecked(
                "2677D0532B47A4CEAD2488845E7DF7EBC16C0B8A2CD8A6B7F4CE99F51659794E"
            )
        );
        let q0 = MapToCurve1(u[0]);
        let q1 = MapToCurve1(u[1]);
        assert!(
            q0 == G1Point::from_affine(
                FpE::from_hex_unchecked(
                    "28D01790D2A1CC4832296774438ACD46C2CE162D03099926478CF52319DABA8D"
                ),
                FpE::from_hex_unchecked(
                    "10227AB2707FD65FB45E87F0A48CFE3556F04113D27B1DA9A7AE1709007355E1"
                )
            )
        );
        assert!(
            q1 == G1Point::from_affine(
                FpE::from_hex_unchecked(
                    "C936F13F77C4692169505EC512C5637FFC2D885F4D8627C21E448E59B7B02B5"
                ),
                FpE::from_hex_unchecked(
                    "2589008B2E15DCB3D16CDC1FED2634778001B1B28F0AB433F4F5EC6635C55E1E"
                )
            )
        );

        let u = hash_to_field(
            &Sha3Hasher::expand_message(
                b"",
                b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_",
                32, //
            )
            .unwrap(),
            2,
        );
        assert!(
            u[0] == FpE::from_hex_unchecked(
                "2F87B81D9D6EF05AD4D249737498CC27E1BD485DCA804487844FEB3C67C1A9B5"
            )
        );
        assert!(
            u[1] == FpE::from_hex_unchecked(
                "6DE2D0D7C0D9C7A5A6C0B74675E7543F5B98186B5DBF831067449000B2B1F8E"
            )
        );
        let q0 = MapToCurve1(u[0]);
        let q1 = MapToCurve1(u[1]);
        assert!(
            q0 == G1::new(
                FpE::from_hex_unchecked(
                    "E449B959ABBD0E5AB4C873EAEB1CCD887F1D9AD6CD671FD72CB8D77FB651892"
                ),
                FpE::from_hex_unchecked(
                    "29FF1E36867C60374695EE0C298FCBEF2AF16F8F97ED356FA75E61A797EBB265"
                )
            )
        );
        assert!(
            q1 == G1::new(
                FpE::from_hex_unchecked(
                    "19388D9112A306FBA595C3A8C63DAA8F04205AD9581F7CF105C63C442D7C6511"
                ),
                FpE::from_hex_unchecked(
                    "182DA356478AA7776D1DE8377A18B41E933036D0B71AB03F17114E4E673AD6E4"
                )
            )
        );

        let u = FpE::hash_to_fieldSha3Hasher::expand_message(b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_", 2);
        assert!(
            u[0] == FpE::from_hex_unchecked(
                "48527470F534978BAE262C0F3BA8380D7F560916AF58AF9AD7DCB6A4238E633"
            )
        );
        assert!(
            u[1] == FpE::from_hex_unchecked(
                "19A6D8BE25702820B9B11EADA2D42F425343889637A01ECD7672FBCF590D9FFE"
            )
        );
        let q0 = MapToCurve1(u[0]);
        let q1 = MapToCurve1(u[1]);
        assert!(
            q0 == G1::new(
                FpE::from_hex_unchecked(
                    "2298BA379768DA62495AF6BB390FFCA9156FDE1DC167235B89C6DD008D2F2F3B"
                ),
                FpE::from_hex_unchecked(
                    "660564CF6FCE5CDEA4780F5976DD0932559336FD072B4DDD83EC37F00FC7699"
                )
            )
        );
        assert!(
            q1 == G1::new(
                FpE::from_hex_unchecked(
                    "2811DEA430F7A1F6C8C941ECDF0E1E725B8AD1801AD15E832654BD8F10B62F16"
                ),
                FpE::from_hex_unchecked(
                    "253390ED4FB39E58C30CA43892AB0428684CFB30B9DF05FC239AB532EAA02444"
                )
            )
        );

        // msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq", P: point{"0xfe2b0743575324fc452d590d217390ad48e5a16cf051bee5c40a2eba233f5c", "0x794211e0cc72d3cbbdf8e4e5cd6e7d7e78d101ff94862caae8acbe63e9fdc78"},
        // Q0: point{"0x1c53b05f2fce15ba0b9100650c0fb46de1fb62f1d0968b69151151bd25dfefa4", "0x1fe783faf4bdbd79b717784dc59619106e4acccfe3b5d9750799729d855e7b81"},
        // Q1: point{"0x214a4e6e97adda47558f80088460eabd71ed35bc8ceafb99a493dd6f4e2b3f0a", "0xfaaeb29cc23f9d09b187a99741613aed84443e7c35736258f57982d336d13bd"},
        // u0: "0x2a50be15282ee276b76db1dab761f75401cdc8bd9fff81fcf4d428db16092a7b", u1: "0x23b41953676183c30aca54b5c8bd3ffe3535a6238c39f6b15487a5467d5d20eb",

        let u = FpE::hash_to_field(b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq", b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_", 2);
        assert!(
            u[0] == FpE::from_hex_unchecked(
                "2A50BE15282EE276B76DB1DAB761F75401CDC8BD9FFF81FCF4D428DB16092A7B"
            )
        );
        assert!(
            u[1] == FpE::from_hex_unchecked(
                "23B41953676183C30ACA54B5C8BD3FFE3535A6238C39F6B15487A5467D5D20EB"
            )
        );
        let q0 = MapToCurve1(u[0]);
        let q1 = MapToCurve1(u[1]);
        assert!(
            q0 == G1Point::from_affine(
                FpE::from_hex_unchecked(
                    "1C53B05F2FCE15BA0B9100650C0FB46DE1FB62F1D0968B69151151BD25DFEFA4"
                ),
                FpE::from_hex_unchecked(
                    "1FE783FAF4BDBD79B717784DC59619106E4ACCCFE3B5D9750799729D855E7B81"
                )
            )
        );
        assert!(
            q1 == G1Point::from_affine(
                FpE::from_hex_unchecked(
                    "214A4E6E97ADDA47558F80088460EABD71ED35BC8CEAFB99A493DD6F4E2B3F0A"
                ),
                FpE::from_hex_unchecked(
                    "FAAEB29CC23F9D09B187A99741613AED84443E7C35736258F57982D336D13BD"
                )
            )
        );
    }
}
