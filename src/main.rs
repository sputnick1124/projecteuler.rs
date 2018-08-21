extern crate euler;
extern crate clap;

use clap::{Arg, App};
use euler::*;

fn main() {
    let matches = App::new("Euler")
                        .version("0.1.0")
                        .author("Nick Stockton <sputnick1124@comcast.net>")
                        .about("Solutions for projecteuler.net problems")
                        .arg(Arg::with_name("problem")
                             .short("p")
                             .long("problem")
                             .value_name("NUMBER")
                             .help("Selects which problem to solve")
                             .takes_value(true)
                             //.required(true)
                             //.index(1))
                        )
                        .get_matches();

    


    println!("{}", euler008(4));
}
