extern crate num;

use num::bigint::{BigUint};
use num::{ToPrimitive, FromPrimitive, pow, Zero, One, Integer, NumCast};
use std::collections::HashMap;
use std::ops::{AddAssign, Add, Mul};
use std::hash::{Hash};

// Functions for Problem 2
struct Fibonacci<T>
    where T: Integer
{
    a: T,
    b: T,
}

impl<T> Iterator for Fibonacci<T>
    where T: Integer +
             Add<T, Output = T> +
             AddAssign +
             Clone
{
    type Item = T;
    fn next(&mut self) -> Option<T> {
        let tmp: T = self.a.clone();
        self.a = self.b.clone();
        self.b += tmp;
        Some(self.a.clone())
    }
}

fn fibonacci<T>() -> Fibonacci<T>
    where T: Integer + One
{
    Fibonacci{ a: T::one(), b: T::one() }
}

struct Sieve<T>
    where T: Integer
{
    masks: HashMap<T, T>,
    v: T,
}

impl<T> Iterator for Sieve<T>
    where T: Integer + 
             NumCast + 
             AddAssign + 
             Hash + 
             Clone +
             Add<T, Output = T> + 
             Mul<T, Output = T>
{
    type Item = T;
    fn next(&mut self) -> Option<T> {
        let two : T = NumCast::from(2).unwrap();
        if self.v == two.clone() { // handle starting case
            self.v += T::one();
            return Some(two.clone());
        } else {
            let q = self.v.clone();

            match self.masks.remove(&q) {   // lookup number in map
                Some(p) => {                // if there
                    let mut x = q + p.clone();      // start incrementing its multiples
                    loop {
                        if self.masks.contains_key(&x) {
                            x += p.clone();
                        } else {
                            break;          // until its multiples are no longer in the map
                        }
                    }
                    self.masks.insert(x, p);// insert back into map with updated value

                    self.v += two.clone();            // increment the search number by 2
                    self.next()             // and call self
                }
                None => {                           // else (if not already in map)
                    //self.masks.insert(q*q, NumCast::from(2).unwrap()*q);    // place in map
                    self.masks.insert(q.clone()*q.clone(), two.clone()*q.clone());    // place in map

                    self.v += two; // and it's prime. increment and return

                    Some(q)
                }
            }
        }
    }
}

fn sieve<T>() -> Sieve<T>
    where T: Integer + NumCast + Hash
{
    Sieve{masks: HashMap::new(), v: NumCast::from(2).unwrap()}
}

fn list_primes<T>(n: usize) -> Vec<T>
    where T: Integer + NumCast
{
    let mut primes: Vec<bool> = (0..n + 1)
                                    .map(|num| num == 2 || num & 1 != 0)
                                    .collect();
    let mut num: usize = 3;

    while num * num <= n {
        let mut j = num * num;
        while j <= n {
            primes[j] = false;
            j += num;
        }
        num += 2;
        
    }
    primes
        .into_iter()
        .enumerate()
        .skip(2)
        .filter_map(
            |(i, p)| if p {Some(NumCast::from(i).unwrap())} else {None})
        .collect::<Vec<T>>()
}

fn is_palin(num: usize) -> bool {
    let mut num = num;

    let mut digits:Vec<usize> = vec![];
    while num > 0 {
        digits.push(num%10);
        num /= 10;
    }

    let digits_rev = digits.iter().rev();
    for (d1, d2) in digits_rev.zip(digits.iter()) {
        if d1 != d2 {
            return false;
        }
    }
    true
}

fn largest_multiple(n: usize) -> usize {
    let primes: Vec<usize> = list_primes(n);

    let mut res = primes.iter().skip(1).fold(1, |acc, x| acc * x);

    for i in 1..n {
        if res%i > 0 {
            for j in 1..i {
                if i%j == 0 {
                    res *= j;
                }
            }
        }
    }
    res
}

fn sum_squares(n: usize) -> usize {
    (1..n+1).fold(0, |acc, x| acc + x.pow(2))
}

fn square_sum(n: usize) -> usize {
    (1..n+1).fold(0, |acc, x| acc + x).pow(2)
}

fn is_pythagorean(a: u32, b: u32, c: u32) -> bool {
    a.pow(2) + b.pow(2) == c.pow(2)
}

fn is_pyth_sum_1000(a: u32, b: u32, c: u32) -> bool {
    return a + b + c == 1000
}

fn tri_number(n: u64) -> u64 {
    (n + 1)*n/2
}

fn find_factors(n: u64) -> Vec<u64> {
    let mut n = n;
    let mut factors: Vec<u64> = Vec::new();

    loop {
        if n == 1 {
            break;
        }
        for p in 2.. {
            if n%p == 0 {
                n /= p;
                factors.push(p);
                break;
            }
        }
    }
    factors
}

fn count_factors(factors: Vec<u64>) -> Vec<usize> {
    let mut counts: HashMap<u64, usize> = HashMap::new();
    for &factor in factors.iter() {
        let count = counts.entry(factor).or_insert(1);
        *count += 1;
    }
    counts.values().map(|&x| x).collect()
}

fn number_of_factors(n: u64) -> usize {
    count_factors(find_factors(n)).iter()
        .fold(1, |acc, x| acc*(x))
}

fn collatz(x: u64, count: u64) -> u64 {
    match x {
        1 => count + 1,
        _ => {
            if x % 2 == 0 {
                collatz(x/2, count +1)
            } else {
                collatz(3*x + 1, count + 1)
            }
        },
    }
}

fn add_digits(n: BigUint) -> BigUint {
    if n == BigUint::zero() {
        n
    } else {
        let ten = BigUint::from_u64(10).unwrap();
        &n%&ten + add_digits(&n/&ten)
    }
}


fn fact(n: BigUint) -> BigUint {
    if n == BigUint::one() {
        n
    } else {
        &n * fact(&n - &BigUint::one())
    }
}

pub fn euler001(n: usize) -> usize {
    (1..n)
        .filter_map(|x| if x%3==0 || x%5 == 0 {Some(x)} else {None})
        .fold(0usize, |acc, x| acc + x)
}

#[test]
fn test_euler001() {
    assert_eq!(23, euler001(10));
}

pub fn euler002(n: u64) -> u64
    //where T: Integer +
             //Add<T, Output = T> +
             //Zero +
             //AddAssign +
             //Clone +
             //NumCast
{
    let fibs = fibonacci::<u64>();
    fibs
        .take_while(|x| x <= &n)
        .filter_map(|x| if x%2 == 0 { Some(x) } else { None})
        .fold(0, |acc, x| acc + x)
}

#[test]
fn test_euler002() {
    assert_eq!(2, euler002(3));
    assert_eq!(44, euler002(50));
}

pub fn euler003(n: usize) -> Option<usize> {
    let bignum = n;//600851475143;
    let primes: Vec<usize> = list_primes(n);

    for p in primes.iter().rev() {
        if bignum%(p.to_usize().unwrap()) == 0 {
            return Some(p.to_usize().unwrap());
        } 
    }
    return None;

}

#[test]
fn test_euler003() {
    assert_eq!(Some(29), euler003(13195));
    assert_eq!(Some(6875), euler003(600851475143));
}

pub fn euler004(n: usize) -> Option<usize> {
    let mut max_palin = 0;
    for i in (100..n+1).rev() {
        for j in (i..n+1).rev() {
            let n = i*j;
            if is_palin(n) && n > max_palin{
                max_palin = n;
            }
            if n < max_palin {
                Some(max_palin);
            }
        }
    }
    return None;
}

pub fn euler005(n: usize) -> usize {
    largest_multiple(n)
}

pub fn euler006(n: usize) -> usize {
    square_sum(n) - sum_squares(n)
}

pub fn euler007(n: usize) -> Option<usize> {
    let s = sieve();
    let mut v = s.skip(n);
    v.next()
}

pub fn euler008() -> BigUint {
    let bignum_bytes = b"7316717653133062491922511967442657474235534919493496983520312774506326 
                       239578318016984801869478851843858615607891129494954595017379583319528532
                       088055111254069874715852386305071569329096329522744304355766896648950445
                       244523161731856403098711121722383113622298934233803081353362766142828064
                       444866452387493035890729629049156044077239071381051585930796086670172427
                       121883998797908792274921901699720888093776657273330010533678812202354218
                       097512545405947522435258490771167055601360483958644670632441572215539753
                       697817977846174064955149290862569321978468622482839722413756570560574902
                       614079729686524145351004748216637048440319989000889524345065854122758866
                       688116427171479924442928230863465674813919123162824586178664583591245665
                       294765456828489128831426076900422421902267105562632111110937054421750694
                       165896040807198403850962455444362981230987879927244284909188845801561660
                       979191338754992005240636899125607176060588611646710940507754100225698315
                       520005593572972571636269561882670428252483600823257530420752963450";
    let mut n = BigUint::parse_bytes(bignum_bytes, 10).unwrap();
    let d: BigUint = FromPrimitive::from_u64(10).unwrap();
    let q: BigUint = pow(FromPrimitive::from_u64(10).unwrap(), 13);

    let mut biggest: BigUint = Zero::zero();
    loop {
        if n == Zero::zero() {
            break
        }
        let mut m: BigUint = One::one();
        let mut m0: BigUint = &n%&q;

        loop {
            m *= &m0 % &d;
            m0 /= &d;
            if m0 == Zero::zero() {
                break;
            }
        }
        if m > biggest {
            biggest = m;
        }

        n /= &d;
    }
    biggest
}

pub fn euler009(n: u32) -> Option<u32> {
    for a in 1..n {
        for b in a..n {
            for c in b..n {
                if is_pythagorean(a, b, c) && is_pyth_sum_1000(a, b, c) {
                    return Some(a*b*c);
                }
            }
        }
    }
    return None;
}

pub fn euler010(limit: usize) -> usize {
    let s : Sieve<usize> = sieve();
    s.take_while(|x| x < &limit).fold(0usize, |acc, x| acc + x)
}

pub fn euler012(n: usize) -> u64 {
    let num_factors = (2..).map(|x| tri_number(x)).filter(|x| number_of_factors(*x) > n).nth(0);
    num_factors.unwrap()

}

pub fn euler014(n: u64) -> u64 {
    (1..n).map(|x| collatz(x, 0)).max().unwrap()
}

pub fn euler016(power: usize) -> BigUint {
    let two : BigUint = BigUint::from_u64(2u64).unwrap();
    add_digits(pow(two, power))
}

pub fn euler020(n: BigUint) -> BigUint {
    add_digits(fact(n))
}
