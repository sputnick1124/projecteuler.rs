extern crate num;

use num::bigint::{BigUint};
use num::{ToPrimitive, FromPrimitive, pow, Zero, One};
use std::collections::HashMap;

struct Sieve {
    masks: HashMap<usize, usize>,
    v: usize,
}

impl Iterator for Sieve {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        if self.v == 2 { // handle starting case
            self.v += 1;
            return Some(2);
        } else {
            let q = self.v;

            match self.masks.remove(&q) {   // lookup number in map
                Some(p) => {                // if there
                    let mut x = q + p;      // start incrementing its multiples
                    loop {
                        if self.masks.contains_key(&x) {
                            x += p;
                        } else {
                            break;          // until its multiples are no longer in the map
                        }
                    }
                    self.masks.insert(x, p);// insert back into map with updated value

                    self.v += 2;            // increment the search number by 2
                    //self.v += 1;            // increment the search number by 2
                    self.next()             // and call self
                }
                None => {                           // else (if not already in map)
                    self.masks.insert(q*q, 2*q);    // place in map
                    //self.masks.insert(q*q, q);    // place in map
                    //println!("{:?}", self.masks);
                    self.v += 2;                    // and it's prime. increment and return
                    //self.v += 1;                    // and it's prime. increment and return
                    Some(q)
                }
            }
        }
    }
}

fn sieve() -> Sieve {
    Sieve{masks: HashMap::new(), v: 2}
}

fn list_primes(n: usize) -> Vec<usize> {
    let mut primes: Vec<bool> = (0..n + 1)
                                    .map(|num| num == 2 || num & 1 != 0)
                                    .collect();
    let mut num: usize = 3;
    //let mut n: usize = 0;
    //let mut p: bool = false;
    while num * num <= n {
        let mut j = num * num;
        while j <= n {
            primes[j] = false;
            j += num;
        }
        num += 2;
        //num *= 2;
        //let r = primes.into_iter().enumerate().find(|&(i, p)| *p);

        //println!("next prime: {:?}", primes[num..].into_iter().enumerate().find(|&(i, p)| (*p)));
        //println!("num: {}", num);
        
    }
    primes
        .into_iter()
        .enumerate()
        .skip(2)
        .filter_map(
            |(i, p)| if p {Some(i)} else {None})
        .collect::<Vec<usize>>()
}

//fn is_prime(n: usize, primes: &Vec<usize>) -> bool {
    //for &p in primes {
        //let q = n / p;
        //if q < p{ return true };
        //let r = n - q * p;
        //if r == 0 { return false };
    //}

    //panic!("too few primes")
//}

pub fn euler003(n: u64) -> Option<u64> {
    let bignum = n;//600851475143;

    let limit = (bignum as f64).sqrt() as usize;
    let primes = list_primes(limit);

    for p in primes.iter().rev() {
        if bignum%(p.to_u64().unwrap()) == 0 {
            return Some(p.to_u64().unwrap());
        } 
    }
    return None;

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

fn largest_multiple(n: usize) -> usize {
    let primes = list_primes(n);

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

pub fn euler005(n: usize) -> usize {
    largest_multiple(n)
}

fn sum_squares(n: usize) -> usize {
    (1..n+1).fold(0, |acc, x| acc + x.pow(2))
}

fn square_sum(n: usize) -> usize {
    (1..n+1).fold(0, |acc, x| acc + x).pow(2)
}

pub fn euler006(n: usize) -> usize {
    square_sum(n) - sum_squares(n)
}

pub fn euler007(n: usize) -> Option<usize> {
    let s = sieve();
    let mut v = s.skip(n);
    v.next()
}

fn is_pythagorean(a: u32, b: u32, c: u32) -> bool {
    a.pow(2) + b.pow(2) == c.pow(2)
}

fn is_pyth_sum_1000(a: u32, b: u32, c: u32) -> bool {
    return a + b + c == 1000
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
    let s = sieve();
    s.take_while(|x| x < &limit).fold(0usize, |acc, x| acc + x)
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

pub fn euler012(n: usize) -> u64 {
    let num_factors = (2..).map(|x| tri_number(x)).filter(|x| number_of_factors(*x) > n).nth(0);
    num_factors.unwrap()

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

pub fn euler014(n: u64) -> u64 {
    (1..n).map(|x| collatz(x, 0)).max().unwrap()
}

fn add_digits(n: BigUint) -> BigUint {
    if n == BigUint::zero() {
        n
    } else {
        let ten = BigUint::from_u64(10).unwrap();
        &n%&ten + add_digits(&n/&ten)
    }
}


pub fn euler016(power: usize) -> BigUint {
    let two : BigUint = BigUint::from_u64(2u64).unwrap();
    add_digits(pow(two, power))
}

fn fact(n: BigUint) -> BigUint {
    if n == BigUint::one() {
        n
    } else {
        &n * fact(&n - &BigUint::one())
    }
}

pub fn euler020(n: BigUint) -> BigUint {
    add_digits(fact(n))
}
