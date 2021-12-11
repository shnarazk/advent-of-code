use {
    crate::y2020::traits::{Description, ProblemSolver},
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashSet,
};

pub fn day07(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Eq, Debug, Hash, PartialEq)]
struct Link {
    outer: String,
    inner: String,
    amount: usize,
}

#[derive(Debug, PartialEq)]
struct Setting {
    links: HashSet<Link>,
}

impl ProblemSolver<String, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 7;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {
            links: HashSet::new(),
        }
    }
    fn insert(&mut self, line: String) {
        lazy_static! {
            static ref HEAD: Regex =
                Regex::new(r"^([a-z]+ [a-z]+) bags? contain (.*)").expect("wrong");
            static ref PREP: Regex =
                Regex::new(r"(\d+) ([a-z]+ [a-z]+) bags?(, (.*))?").expect("wrong");
        }
        if let Some(head) = HEAD.captures(&line) {
            let mut b: String = head[2].to_string();
            while let Some(prep) = PREP.captures(&b) {
                self.links.insert(Link {
                    outer: head[1].to_string(),
                    inner: prep[2].to_string(),
                    amount: prep[1].parse::<usize>().unwrap(),
                });
                if let Some(rest) = prep.get(4) {
                    b = rest.as_str().to_string();
                    if b == "." {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
    }
    fn part1(&mut self) -> usize {
        let mut outers: HashSet<String> = HashSet::new();
        most_outer_of(&self.links, "shiny gold", &mut outers);
        outers.len()
    }
    fn part2(&mut self) -> usize {
        let mut outers: HashSet<String> = HashSet::new();
        most_outer_of(&self.links, "shiny gold", &mut outers);
        collects(&self.links, "shiny gold") - 1
    }
}

fn most_outer_of(links: &HashSet<Link>, origin: &str, outers: &mut HashSet<String>) {
    for link in links {
        if link.inner == origin {
            outers.insert(link.outer.to_string());
            most_outer_of(links, &link.outer, outers);
        }
    }
}

fn collects(links: &HashSet<Link>, origin: &str) -> usize {
    let mut count = 0;
    for link in links {
        if link.outer == origin {
            count += link.amount * collects(links, &link.inner);
        }
    }
    count + 1
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string())).run(1),
            Answer::Part1(4)
        );
    }

    #[test]
    fn test_part2_1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string())).run(2),
            Answer::Part2(32)
        );
    }

    #[test]
    fn test_part2_2() {
        assert_eq!(
            Setting::parse(Description::FileTag("test2".to_string())).run(2),
            Answer::Part2(126)
        );
    }
}
