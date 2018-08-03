extern crate euler;
extern crate num;

use num::BigUint;
use num::FromPrimitive;

use euler::euler020;

fn main() {
    let n = BigUint::from_u64(10_000).unwrap();

    println!("{}", euler020(n));
}
