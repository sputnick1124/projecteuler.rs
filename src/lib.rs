extern crate num;

use num::bigint::{BigUint};
use num::{ToPrimitive, FromPrimitive, pow, Zero, One, Integer, NumCast};
use std::collections::HashMap;
use std::ops::{AddAssign, Add, Mul, Sub, Div};
use std::hash::{Hash};
use std::io::{BufReader, BufRead};
use std::fs::File;
use std::mem;
use std::cmp::max;
use std::fmt::Debug;

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
        mem::swap(&mut self.a, &mut self.b);
        self.b += self.a.clone();
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

    for i in 2..n {
        if res%i > 0 {
            for j in list_primes::<usize>(i+1) {
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

fn is_pyth_sum(a: u32, b: u32, c: u32, n: u32) -> bool {
    return a + b + c == n
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
                collatz(x/2, count + 1)
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


fn fact<T>(n: T) -> T
    where T: One + Integer + Sub<T, Output = T> + Mul<T, Output = T> + Clone
{
    if n == T::one() {
        n
    } else {
        n.clone() * fact(n.clone() - T::one())
    }
}

fn pairwise_max<T>(v: Vec<T>) -> Vec<T>
//fn pairwise_max(v: Vec<u32>) -> Vec<&u32>
    where T: Integer + Ord + Zero + Debug + Copy
{
    v.iter().zip(v.iter().skip(1))
        .map(|(x1, x2)| max(*x1, *x2))
        //.map(|x| *x)
        .collect::<Vec<T>>()
}

#[test]
fn test_pairwise_max() {
    let v = vec![0u64, 2u64, 1u64, 7u64, 4u64];
    assert_eq!(vec![2u64, 2u64, 7u64, 7u64], pairwise_max(v));
}

fn element_wise_add<T>(v1: Vec<T>, v2: Vec<T>) -> Vec<T>
    where T: Add<T, Output = T> + Integer + Copy
{
    v1.iter().zip(v2.iter())
        .map(|(a, b)| *a + *b)
        .collect()
}

#[test]
fn test_element_wise_add() {
    let v1: Vec<u32> = vec![1, 2, 3, 4, 5, 6, 7];
    let v2: Vec<u32> = vec![1, 2, 3, 4, 5, 6, 7];
    assert_eq!(vec![2u32, 4u32, 6u32, 8u32, 10u32, 12u32, 14u32],
               element_wise_add(v1, v2));
}

/// If we list all the natural numbers below 10 that are multiples of `3` or `5`, we get `3`, `5`,
/// `6`, and `9`. The sum of these multiples is `23`.
///
/// Find the sum of all the multiples of `3` or `5` below `1000`
pub fn euler001(n: usize) -> usize {
    (1..n)
        .filter_map(|x| if x%3==0 || x%5 == 0 {Some(x)} else {None})
        .fold(0usize, |acc, x| acc + x)
}

#[test]
fn test_euler001() {
    assert_eq!(23, euler001(10));
}

fn triangle_vec(file_path: String) -> Vec<Vec<u64>> {
    let fd = File::open(file_path).expect("unable to open file");
    let file = BufReader::new(&fd);
    file.lines()
        .map(|line| line.unwrap().split_whitespace()
             .map(|numstr| numstr.parse().expect("Not able to parse number"))
             .collect())
        .collect()
}

/// Each new term in the Fibonacci sequence is generated by adding the previous two terms. By starting with 
/// `1` and `2`, the first 10 terms will be:
///
/// ` 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...`
///
/// By considering the terms in the Fibonacci sequence whose values do not exceed four million,
/// find the sum of the even-valued terms.
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

/// The prime factors of `13195` are `5, 7, 13`, and `29`.
///
/// What is the largest prime factor of the number `600851475143`?
pub fn euler003(n: usize) -> Option<usize> {
    let bignum = n;//600851475143;
    let limit = (n as f64).sqrt() as usize;
    let primes: Vec<usize> = list_primes(limit);

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
    assert_eq!(Some(6857), euler003(600851475143));
}

/// A palindromic number reads the same both ways. The largest palindrome made from the product of
/// two 2-digit numbers is `9009 = 91*99`.
///
/// Find the largest palindrome made from the product of two 3-digit numbers.
pub fn euler004(digits: u32) -> usize {
    let mut max_palin = 0;
    for i in (10usize.pow(digits-1)..10usize.pow(digits)).rev() {
        for j in (i..10usize.pow(digits)).rev() {
            let n = i*j;
            if is_palin(n) && n > max_palin{
                println!("{}", n);
                max_palin = n;
            }
            if n < max_palin {
                break;
            }
        }
    }
    max_palin
}

#[test]
fn test_euler004() {
    assert_eq!(9009, euler004(2));
    assert_eq!(906609, euler004(3));
}

/// `2520` is the smallest number that can be divided by each of the numbers from `1` to `10`
/// without any remainder.
///
/// What is the smallest positive number that is __evenly divisible__ by all of the numbers from
/// `1` to `20`?
pub fn euler005(n: usize) -> usize {
    largest_multiple(n)
}

#[test]
fn test_euler005() {
    assert_eq!(2520, euler005(10));
    assert_eq!(232792560, euler005(20));
}

/// The sum of the squares of the first ten natural numbers is,
///
/// ` 1^2 + 2^2 + ... + 10^2 = 385`
///
/// The square of the sum of the first ten natural numbers is,
///
/// ` (1 + 2 + ... + 10)^2 = 55^2 = 3025 `
///
/// Hence the difference between the sum of the squares of the first ten natural numbers and the
/// square of the sum is `3025 - 385 = 2640`.
///
/// Find the difference between the sum of the squares of the first one hundred natural numbers and
/// the square of the sum.
pub fn euler006(n: usize) -> usize {
    square_sum(n) - sum_squares(n)
}

#[test]
fn test_euler006() {
    assert_eq!(2640, euler006(10));
}

/// By listing the first six prime numbers: `2, 3, 5, 7, 11`, and `13`, we can see that the 6th
/// prime is `13`.
///
/// What is the `10_001`st prime number?
pub fn euler007(n: usize) -> usize {
    let s = sieve();
    let mut v = s.skip(n - 1);
    v.next().unwrap()
}

#[test]
fn test_euler007() {
    assert_eq!(13, euler007(6));
}

/// The four adjacent digits in the 1000-digit number that have the greatest product are `9*9*8*9 =
/// 5832`.
///
/// `
/// 73167176531330624919225119674426574742355349194934
/// 96983520312774506326239578318016984801869478851843
/// 85861560789112949495459501737958331952853208805511
/// 12540698747158523863050715693290963295227443043557
/// 66896648950445244523161731856403098711121722383113
/// 62229893423380308135336276614282806444486645238749
/// 30358907296290491560440772390713810515859307960866
/// 70172427121883998797908792274921901699720888093776
/// 65727333001053367881220235421809751254540594752243
/// 52584907711670556013604839586446706324415722155397
/// 53697817977846174064955149290862569321978468622482
/// 83972241375657056057490261407972968652414535100474
/// 82166370484403199890008895243450658541227588666881
/// 16427171479924442928230863465674813919123162824586
/// 17866458359124566529476545682848912883142607690042
/// 24219022671055626321111109370544217506941658960408
/// 07198403850962455444362981230987879927244284909188
/// 84580156166097919133875499200524063689912560717606
/// 05886116467109405077541002256983155200055935729725
/// 71636269561882670428252483600823257530420752963450
/// `
///
/// Find the thirteen adjacent digits in the 1000-digit number that have the greatest product. What
/// is the value of this product?
pub fn euler008(digits: usize) -> BigUint {
    let bignum_bytes = b"\
        73167176531330624919225119674426574742355349194934\
        96983520312774506326239578318016984801869478851843\
        85861560789112949495459501737958331952853208805511\
        12540698747158523863050715693290963295227443043557\
        66896648950445244523161731856403098711121722383113\
        62229893423380308135336276614282806444486645238749\
        30358907296290491560440772390713810515859307960866\
        70172427121883998797908792274921901699720888093776\
        65727333001053367881220235421809751254540594752243\
        52584907711670556013604839586446706324415722155397\
        53697817977846174064955149290862569321978468622482\
        83972241375657056057490261407972968652414535100474\
        82166370484403199890008895243450658541227588666881\
        16427171479924442928230863465674813919123162824586\
        17866458359124566529476545682848912883142607690042\
        24219022671055626321111109370544217506941658960408\
        07198403850962455444362981230987879927244284909188\
        84580156166097919133875499200524063689912560717606\
        05886116467109405077541002256983155200055935729725\
        71636269561882670428252483600823257530420752963450";

    let mut n = BigUint::parse_bytes(bignum_bytes, 10).unwrap();
    let d: BigUint = BigUint::from_u64(10).unwrap();
    let q: BigUint = pow(BigUint::from_u64(10).unwrap(), digits);

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

#[test]
fn test_euler008() {
    assert_eq!(BigUint::from_u64(5832).unwrap(), euler008(4));
}

/// A Pythagorean triplet is a set of three natural numbers, `a < b < c` for which,
///
/// `a^2 + b^2 = c^2`
///
/// For example, `3^2 + 4^2 = 9 + 16 = 25 = 5^2`.
///
/// There exists exactly one Pythagorean triplet for which `a + b + c = 1000`.
///
/// Find the product `a*b*c`.
pub fn euler009(n: u32) -> Option<u32> {
    for a in 1..n {
        for b in a..n {
            for c in b..n {
                if is_pythagorean(a, b, c) && is_pyth_sum(a, b, c, n) {
                    return Some(a*b*c);
                }
            }
        }
    }
    return None;
}

#[test]
fn test_euler009() {
    assert!(is_pythagorean(3, 4, 5));
    assert!(is_pyth_sum(3, 4, 5, 12));
    assert_eq!(Some(31875000), euler009(1000));
}

/// The sum of the primes below 10 is `2 + 3 + 5 + 7 = 17`.
///
/// Find the sum of all the primes below two million.
pub fn euler010(limit: usize) -> usize {
    let s : Sieve<usize> = sieve();
    s.take_while(|x| x < &limit).fold(0usize, |acc, x| acc + x)
}

#[test]
fn test_euler010() {
    assert_eq!(17, euler010(10));
    assert_eq!(142913828922, euler010(2_000_000));
}

/// In the 20x20 grid below, four numbers along a diagonal line have been marked in bold.
///
///  08 02 22 97 38 15 00 40 00 75 04 05 07 78 52 12 50 77 91 08  
///  49 49 99 40 17 81 18 57 60 87 17 40 98 43 69 48 04 56 62 00    
///  81 49 31 73 55 79 14 29 93 71 40 67 53 88 30 03 49 13 36 65    
///  52 70 95 23 04 60 11 42 69 24 68 56 01 32 56 71 37 02 36 91    
///  22 31 16 71 51 67 63 89 41 92 36 54 22 40 40 28 66 33 13 80    
///  24 47 32 60 99 03 45 02 44 75 33 53 78 36 84 20 35 17 12 50    
///  32 98 81 28 64 23 67 10 __26__ 38 40 67 59 54 70 66 18 38 64 70    
///  67 26 20 68 02 62 12 20 95 __63__ 94 39 63 08 40 91 66 49 94 21    
///  24 55 58 05 66 73 99 26 97 17 __78__ 78 96 83 14 88 34 89 63 72    
///  21 36 23 09 75 00 76 44 20 45 35 __14__ 00 61 33 97 34 31 33 95    
///  78 17 53 28 22 75 31 67 15 94 03 80 04 62 16 14 09 53 56 92    
///  16 39 05 42 96 35 31 47 55 58 88 24 00 17 54 24 36 29 85 57    
///  86 56 00 48 35 71 89 07 05 44 44 37 44 60 21 58 51 54 17 58    
///  19 80 81 68 05 94 47 69 28 73 92 13 86 52 17 77 04 89 55 40    
///  04 52 08 83 97 35 99 16 07 97 57 32 16 26 26 79 33 27 98 66    
///  88 36 68 87 57 62 20 72 03 46 33 67 46 55 12 32 63 93 53 69    
///  04 42 16 73 38 25 39 11 24 94 72 18 08 46 29 32 40 62 76 36    
///  20 69 36 41 72 30 23 88 34 62 99 69 82 67 59 85 74 04 36 16    
///  20 73 35 29 78 31 90 01 74 31 49 71 48 86 81 16 23 57 05 54    
///  01 70 54 71 83 51 54 69 16 92 33 48 61 43 52 01 89 19 67 48    
///
/// The product of these numbers is `26*63*78*14 = 1788696`.  
/// What is the greatest product of four adjacent numbers in the same direction (up, down, left,
/// right, or diagonally) in the 20x20 grid?
pub fn euler011() {
}

/// The sequence of triangle numbers is generated by adding the natural numbers. So the 7th
/// triangle number would be `1+2+3+4+5+6+7=28`. The first ten terms would be:
///
/// `1, 3, 6, 10, 15, 21, 28, 36, 45, 55, ...`
///
/// Let us list the factors of the first seven triangle numbers:  
/// __1__: `1`  
/// __3__: `1, 3`  
/// __6__: `1, 2, 3, 6`  
/// __10__: `1, 2, 5, 10`  
/// __15__: `1, 3, 5, 15`  
/// __21__: `1, 3, 7, 21`  
/// __28__: `1, 2, 4, 7, 14, 28`
///
/// We can see that `28` is the first triangle number to have over five divisors.  
/// What is the value of the first triangle number to have over five hundred divisors?
pub fn euler012(n: usize) -> u64 {
    let num_factors = (2..).map(|x| tri_number(x)).filter(|x| number_of_factors(*x) > n).nth(0);
    num_factors.unwrap()
}

#[test]
fn test_euler012() {
    assert_eq!(28, euler012(5));
    assert_eq!(76576500, euler012(500));
}

/// Work out the first ten digits of the sum of the following one-hundred 50-digit numbers.
/// `37107287533902102798797998220837590246510135740250`  
/// `46376937677490009712648124896970078050417018260538`  
/// `74324986199524741059474233309513058123726617309629`  
/// `...`  
/// `details elided. see euler013.txt for full list`  
/// `...`  
/// `53503534226472524250874054075591789781264330331690`
pub fn euler013(digits: usize) -> BigUint {
    let f = File::open("euler013.txt").expect("Unable to read file");
    let file = BufReader::new(&f);
    let mut bignums: Vec<BigUint> = Vec::new();

    for line in file.lines() {
        let num_string = line.unwrap();
        let n = BigUint::parse_bytes(num_string.as_bytes(), 10).unwrap();
        bignums.push(n);
    }

    let summation = bignums.iter().fold(BigUint::zero(), |acc, x| acc + x);

    // determine how many digits are in the sum. Can't do logarithm on BigUint, so find bounds by
    // trial comparison to powers of ten
    let ten = BigUint::from_usize(10).unwrap();
    let mut num_digits = 0usize;
    for power in 1.. {
        let lower = pow(ten.clone(), power);
        let upper = pow(ten.clone(), power + 1);
        if lower <= summation && summation < upper {
            num_digits = power + 1;
            break;
        }
    }
    summation/pow(ten, num_digits - digits)
}

#[test]
fn test_euler013() {
    assert_eq!(BigUint::from_usize(5537376230).unwrap(), euler013(10));
}

/// The following iterative sequence is defined for the set of positive integers:  
/// `n -> n/2` (*n* is even)  
/// `n -> 3n + 1` (*n* is odd)  
/// Using the rule above and starting with 13, we generate the following sequence:  
/// `13 -> 40 -> 20 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1`
///
/// It can be seen that this sequence (starting at 13 and finshing at 1) contains 10 terms.
/// Although it has not been proven yet (Collatz Problem), it is thought that all starting numbers
/// finish at 1.
///
/// Which starting number, under one million, produces the longest chain?
///
/// __Note__: Once the chain starts the terms are allowed to go above one million.
pub fn euler014(n: u64) -> u64 {
    (1..n).map(|x| (x, collatz(x, 0))).max_by_key(|tuple| (*tuple).1).unwrap().0
}

#[test]
fn test_euler014() {
    assert_eq!(10, collatz(13, 0));
    assert_eq!(837799, euler014(1_000_000));
}

/// Starting in the top left corner of a 2×2 grid, and only being able to move to the right and
/// down, there are exactly 6 routes to the bottom right corner.
///
/// How many such routes are there through a 20x20 grid?
pub fn euler015<T>(grid_size: T) -> T
    where T: Mul<T, Output = T> +
             Div<T, Output = T> +
             Clone +
             FromPrimitive + 
             Integer
{
    //40 choose 20 = 
    let path_length = grid_size.clone()*T::from_usize(2).unwrap();
    fact(path_length)/(fact(grid_size.clone())*fact(grid_size))
}

#[test]
fn test_euler015() {
    assert_eq!(6, euler015(2));
    assert_eq!(BigUint::from_usize(137846528820).unwrap(), euler015(BigUint::from_usize(20).unwrap()));
}

/// `2^15 = 32768` and the sum of its digits is `3+2+7+6+8=26`
///
/// What is the sum of the digits of the number `2^1000`?
pub fn euler016(power: usize) -> BigUint {
    let two : BigUint = BigUint::from_u64(2u64).unwrap();
    add_digits(pow(two, power))
}

/// If the numbers 1 to 5 are written out in words: one, two, three, four, five, then there are
/// `3+3+5+4+4=19` letters used in total.
///
/// If all the numbers from 1 to 1000 (one thousand) inclusive were written out in words, how many
/// letters would be used?
///
/// __Note__: Do not count spaces or hyphens. For example, 342 (three hundred and forty-two)
/// contains 23 letters and 115 (one hundred and fifteen) contains 20 letters. The use of "and"
/// when writing out numbers is in compliance with British usage.
pub fn euler017() {
}

/// By starting at the top of the triangle below and moving to adjacent numbers on the row below,
/// the maximum total from top to bottom is 23.  
/// &nbsp;&nbsp;&nbsp;__3__  
/// &nbsp;&nbsp;__7__&nbsp;4  
/// &nbsp;2&nbsp;__4__&nbsp;6  
/// 8&nbsp;5&nbsp;__9__&nbsp;3  
/// That is, `3+7+4+9=23`.
///
/// Find the maximum total from top to bottom of the triangle below:  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;75  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;95&nbsp;64  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;17&nbsp;47&nbsp;82  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;18&nbsp;35&nbsp;87&nbsp;10  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;20&nbsp;04&nbsp;82&nbsp;47&nbsp;65  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;19&nbsp;01&nbsp;23&nbsp;75&nbsp;03&nbsp;34  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;88&nbsp;02&nbsp;77&nbsp;73&nbsp;07&nbsp;63&nbsp;67  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;99&nbsp;65&nbsp;04&nbsp;28&nbsp;06&nbsp;16&nbsp;70&nbsp;92  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;41&nbsp;41&nbsp;26&nbsp;56&nbsp;83&nbsp;40&nbsp;80&nbsp;70&nbsp;33  
/// &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;41&nbsp;48&nbsp;72&nbsp;33&nbsp;47&nbsp;32&nbsp;37&nbsp;16&nbsp;94&nbsp;29  
/// &nbsp;&nbsp;&nbsp;&nbsp;53&nbsp;71&nbsp;44&nbsp;65&nbsp;25&nbsp;43&nbsp;91&nbsp;52&nbsp;97&nbsp;51&nbsp;14  
/// &nbsp;&nbsp;&nbsp;70&nbsp;11&nbsp;33&nbsp;28&nbsp;77&nbsp;73&nbsp;17&nbsp;78&nbsp;39&nbsp;68&nbsp;17&nbsp;57  
/// &nbsp;&nbsp;91&nbsp;71&nbsp;52&nbsp;38&nbsp;17&nbsp;14&nbsp;91&nbsp;43&nbsp;58&nbsp;50&nbsp;27&nbsp;29&nbsp;48  
/// &nbsp;63&nbsp;66&nbsp;04&nbsp;68&nbsp;89&nbsp;53&nbsp;67&nbsp;30&nbsp;73&nbsp;16&nbsp;69&nbsp;87&nbsp;40&nbsp;31  
/// 04&nbsp;62&nbsp;98&nbsp;27&nbsp;23&nbsp;09&nbsp;70&nbsp;98&nbsp;73&nbsp;93&nbsp;38&nbsp;53&nbsp;60&nbsp;04&nbsp;23  
/// __Note__: As there are only 16384 routes, it is possible to solve this problem by trying every
/// route. However, Problem 67, is the same challenge with a triangle containing one-hundred rows;
/// it cannot be solved by brute force, and requires a clever method!
pub fn euler018(tri_file: String) -> Vec<u64> {
    let tri_vec = triangle_vec(tri_file);
    println!("{:?}", tri_vec);
    let mut iter_rows = tri_vec.iter().rev();
    let mut tmp_sum = iter_rows.next().unwrap().to_vec();
    loop {
        println!("tmp_sum: {:?}", tmp_sum);
        tmp_sum = match iter_rows.next() {
            Some(vec) => element_wise_add(vec.to_vec(), pairwise_max(tmp_sum)),
            None => break,
        }
    }
    tmp_sum
}

#[test]
fn test_euler018() {
    assert_eq!(vec![23u64], euler018("euler018-1.txt".to_string()));
    assert_eq!(vec![1074u64], euler018("euler018-2.txt".to_string()));
}

/// You are given the following information, but you may prefer to do some research for yourself.
///
///  - 1 Jan 1900 was a Monday
///  - Thirty days has September,  
///  April, June and November.  
///  All the rest have thirty-one,  
///  Saving February alone,  
///  Which has twenty-eight, rain or shine.  
///  And on leap years, twenty-nine.
///  - A leap year occurs on any year evenly divisible by 4, but not on a century unless it is
///  divisible by 400.
///
/// How many Sundays fell on the first day of the month during the twentieth century (1 Jan 1900 to
/// 31 Dec 2000)?
pub fn euler019() {
}

/// `n!` means `n*(n-1)*...*3**2*1`
///
/// For example, `10! = 10*9*...*3*2*1 = 3628800`, and the sum of the digits in the number `10!` is
/// `3+6+2+8+8+0+0 = 27`.
///
/// Find the sum of the digits in the number `100!`
pub fn euler020(n: BigUint) -> BigUint {
    add_digits(fact(n))
}

/// Let *d(n)* be defined as the sum of proper divisors of *n* (numbers less than *n* which divide
/// evenly into *n*).  
/// If *d(a) = b* and *d(b) = a*, where *a != b*, then *a* and *b* are an amicable pair and each of
/// *a* and *b* are called amicable numbers.
///
/// For example, the proper divisors of 220 are 1, 2, 4, 5, 10, 11, 20, 22, 44, 55, and 110;
/// therefore *d(220) = 284*. The proper divisors of 284 are 1, 2, 4, 71, and 142; so *d(284) =
/// 220*.
///
/// Evaluate the sum of all the amicable numbers under 1000.
pub fn euler021() -> u64 {
}

pub fn euler067() -> Vec<u64> {
    euler018("euler067.txt".to_string())
}

#[test]
fn test_euler067() {
    assert_eq!(vec![7273], euler067());
}
