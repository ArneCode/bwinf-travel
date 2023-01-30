use image::{Pixel, Rgba, RgbaImage};
use imageproc::drawing::{draw_line_segment_mut, Blend, Canvas};
use itertools::Itertools;
use rand::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::collections::BinaryHeap;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::mem;
use std::time::Instant;
use std::{collections::HashMap, f64::consts::PI};

struct Dir(f64, f64);
impl Dir {
    fn angle_to(&self, other: &Dir) -> f64 {
        f64::acos((self.0 * other.0 + self.1 * other.1) % 1.)
    }
}
fn angle_ok(a: &Dir, b: &Dir) -> bool {
    let a = a.angle_to(b);
    a <= PI / 2.0 || a >= 3.0 * PI / 2.0
}
#[derive(Debug)]
struct Point(f64, f64);
impl Point {
    fn dir_to(&self, other: &Point) -> Dir {
        Dir(other.0 - self.0, other.1 - self.1)
    }
    fn new_rand(range: (f64, f64), rng: &mut rand::prelude::ThreadRng) -> Self {
        Point(rng.gen_range(0.0..range.0), rng.gen_range(0.0..range.1))
    }
    fn dist_to(&self, other: &Point) -> f64 {
        let x = self.0 - other.0;
        let y = self.1 - other.1;
        f64::sqrt(x * x + y * y)
    }
    fn to_tuple(&self) -> (f32, f32) {
        (self.0 as f32, self.1 as f32)
    }
}
fn get_points(size: (f64, f64), n: usize, rng: &mut ThreadRng) -> Vec<Point> {
    (0..n).map(|_| Point::new_rand(size, rng)).collect()
}
fn get_len(path: &Vec<&Point>) -> f64 {
    let mut result = 0.0;
    let mut p_pt = &path[0];
    for pt in path.iter().skip(1) {
        result += pt.dist_to(p_pt);
        p_pt = pt;
    }
    result
}
fn path_is_ok(path: &Vec<&Point>) -> bool {
    let mut p_pt = &path[0];
    let mut p_dir = p_pt.dir_to(&path[1]);
    for pt in path.iter().skip(1) {
        let new_dir = p_pt.dir_to(pt);
        p_pt = pt;
        if !angle_ok(&p_dir, &new_dir) {
            return false;
        }
        p_dir = new_dir;
    }
    true
}
fn get_shortest_path<'a>(points: &'a Vec<Point>, check_angles: bool) -> (f64, Vec<&'a Point>) {
    let mut min_path = (f64::MAX, vec![]);
    for combination in points.iter().permutations(points.len()) {
        if check_angles && !path_is_ok(&combination) {
            continue;
        }
        let len = get_len(&combination);
        if len < min_path.0 {
            min_path = (len, combination);
        }
    }
    min_path
}
struct AngleOkList {
    data: Vec<bool>,
    n_points: usize,
}
impl AngleOkList {
    fn get_idx(n_points: usize, idx: (usize, usize, usize)) -> usize {
        n_points * n_points * idx.2 + n_points * idx.1 + idx.0
    }
    fn new(points: &Vec<Point>) -> Self {
        let n_points = points.len();
        let mut data = Vec::with_capacity(n_points * n_points * n_points);
        data.fill(false);
        for (i3, p3) in points.iter().enumerate() {
            for (i2, p2) in points.iter().enumerate() {
                for (i1, p1) in points.iter().enumerate() {
                    let dir1 = p1.dir_to(p2);
                    let dir2 = p2.dir_to(p3);
                    let idx = Self::get_idx(n_points, (i1, i2, i3));
                    data[idx] = angle_ok(&dir1, &dir2);
                }
            }
        }
        Self { n_points, data }
    }
    fn is_ok(&self, i1: usize, i2: usize, i3: usize) -> bool {
        self.data[Self::get_idx(self.n_points, (i1, i2, i3))]
    }
}
//like a list, when hashed order of values doesn't matter
#[derive(Clone, PartialEq, Eq, Hash)]
struct Set {
    curr_hash: u64,
}
impl Set {
    fn add<T>(&mut self, e: T)
    where
        T: Hash,
    {
        let mut hasher = DefaultHasher::new();
        e.hash(&mut hasher);
        self.curr_hash ^= hasher.finish();
    }
}
#[derive(Debug)]
struct Path {
    pts: Vec<usize>,
    len: usize,
}
impl Path {
    fn new() -> Self {
        Self {
            pts: vec![],
            len: 0,
        }
    }
    fn get_last_two(&self) -> (usize, usize) {
        let len = self.pts.len();
        return (self.pts[len - 2], self.pts[len - 1]);
    }
    fn add(&self, pt: usize) -> Self {
        let mut pts = self.pts.clone();
        pts.push(pt);
        let len = self.len + 1;
        Self { pts, len }
    }
}
fn held_karp<'a>(points: &'a Vec<Point>, check_angles: bool) -> (f64, Vec<&'a Point>) {
    let angle_list = AngleOkList::new(points);
    let poss_paths: HashMap<(usize, Set), (Vec<bool>, Vec<Path>)> = HashMap::new();
    let mut new_paths: HashMap<(usize, Set), (Vec<bool>, Vec<Path>)> = HashMap::new();
    for ((p_pt, set), (mut used_list, paths)) in poss_paths {
        for (i, pt) in points.iter().enumerate() {
            if used_list[i] {
                continue;
            }
            let mut set = set.clone();
            set.add(i);
            let mut min_path = (f64::MAX, &paths[0]);
            used_list[i] = true;
            for path in &paths {
                let last_pts = path.get_last_two();
                if !angle_list.is_ok(last_pts.0, last_pts.1, i) {
                    continue;
                }
                let len = path.len as f64 + points[last_pts.1].dist_to(pt);
                if let Some((_, paths)) = new_paths.get_mut(&(last_pts.1, set.clone())) {}
                if len < min_path.0 {
                    min_path = (len, path);
                }
            }
            // if let Some(_) = new_paths.get(&(last_pts.1, set)) {}
        }
    }
    todo!()
}
#[derive(Clone, Debug)]
struct CostList {
    data: Vec<Option<f64>>,
    size: usize,
}
impl fmt::Display for CostList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut i = 0;
        writeln!(f, "")?;
        for y in 0..self.size {
            for x in 0..self.size {
                write!(f, "{:.0}\t", self.data[i].unwrap_or(f64::NAN))?;
                i += 1;
            }
            writeln!(f, "")?;
        }
        Ok(())
    }
}
impl CostList {
    fn new(points: &Vec<Point>) -> Self {
        let size = points.len();
        let mut data = vec![None; size * size];
        let mut i = 0;
        for y in 0..size {
            for x in 0..size {
                if x != y {
                    let dist = points[x].dist_to(&points[y]);
                    data[i] = Some(dist);
                }
                i += 1;
            }
        }
        Self { data, size }
    }
    fn get_idx(&self, x: usize, y: usize) -> usize {
        self.size * y + x
    }
    fn get(&self, x: usize, y: usize) -> &Option<f64> {
        &self.data[self.get_idx(x, y)]
    }
    fn set(&mut self, x: usize, y: usize, value: Option<f64>) {
        let i = self.get_idx(x, y);
        self.data[i] = value;
    }
    fn clear_line(&mut self, n: usize, is_vertical: bool) {
        let size = self.size;
        let start = if is_vertical { n * size } else { n };
        let step = if is_vertical { 1 } else { size };
        for x in 0..size {
            self.data[start + x * step] = None;
        }
    }
    ///
    ///```
    ///assert!(false);
    ///```
    fn reduce_line(&mut self, n: usize, is_vertical: bool) -> f64 {
        let size = self.size;
        let start = if is_vertical { n * size } else { n };
        let step = if is_vertical { 1 } else { size };
        let min = (0..size)
            .filter_map(|x| self.data[start + x * step])
            .fold(f64::NAN, f64::min);
        if min.is_nan() {
            return 0.0;
        }
        for x in 0..size {
            if let Some(v) = &mut self.data[start + x * step] {
                *v -= min;
            }
        }
        min
    }
    fn reduce_lines(&mut self, is_vertical: bool) -> f64 {
        let mut sum = 0.0;
        for i in 0..self.size {
            sum += self.reduce_line(i, is_vertical);
        }
        sum
    }
    /*fn reduce(&mut self) -> f64 {
        // println!("reducing matrix, before: {}", self);
        let cost = self.reduce_lines(false) + self.reduce_lines(true);
        // println!("after: {self}, cost: {cost}");
        cost
    }*/
    /*fn add_path(&self, start: usize, end: usize) -> (f64, CostList) {
        // println!("adding path, start: {start}, end: {end}");
        let mut matrix = self.clone();
        //cost: cost from start to end + prev_cost + new reduction cost
        let i = self.get_idx(end, start);
        // let i = self.get_idx(start, end);
        // let move_cost = mem::take(&mut matrix.data[i]).expect("path wasn't available");
        let move_cost = if let Some(cost) = mem::take(&mut matrix.data[i]) {
            cost
        } else {
            println!("matrix: {}", matrix);
            panic!("path wasn't available, start: {start}, end: {end}");
        };
        //rows for start
        matrix.clear_line(start, true);
        //columns for end
        matrix.clear_line(end, false);
        //remove the other way round
        matrix.set(start, end, None);
        // let reduce_cost = matrix.reduce();
        let cost = move_cost + reduce_cost;
        (cost, matrix)
    }*/
}
// #[derive(PartialEq)]
#[derive(Debug)]
struct Branch {
    cost: f64,
    free_pts: Vec<usize>,
    path: Path,
}
impl Branch {
    fn calc_lower_bound(&self, costs: &CostList) -> f64 {
        let mut cost = 0.0;
        let mut p_pt = &self.path.pts[0];
        for pt in self.path.pts.iter().skip(1) {
            if let Some(dist) = costs.get(*p_pt, *pt) {
                cost += dist;
            }
            p_pt = pt;
        }
        for pt in &self.free_pts {
            let mut min = f64::MAX;
            for other in 0..costs.size {
                if let Some(dist) = costs.get(*pt, other) {
                    if dist < &min {
                        min = *dist;
                    }
                }
            }
            cost += min;
        }
        cost
    }
    fn explore(&self, costs: &CostList, upper_bound: &mut f64) -> Option<Path> {
        let last_pt = if let Some(pt) = self.path.pts.last() {
            pt
        } else {
            println!("returning None...");
            panic!("");
            //done
            return None;
        };
        let mut branches = self
            .free_pts
            .iter()
            .enumerate()
            .map(|(i, dest)| {
                // let (mut cost, matrix) = self.matrix.add_path(*last_pt, *dest);
                // cost += self.cost;
                let mut free_pts = self.free_pts.clone();
                free_pts.swap_remove(i);
                let path = self.path.add(*dest);
                let mut b = Branch {
                    cost: 0.0,
                    free_pts,
                    path,
                };
                let cost = b.calc_lower_bound(costs);
                b.cost = cost;
                b
            })
            .collect::<Vec<_>>();
        //https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort_by
        branches.sort_by(|a, b| a.cost.partial_cmp(&b.cost).unwrap());
        let mut min_path = None;
        // println!("branches: ");
        let mut prev_cost = branches[0].cost;
        for b in branches {
            if b.cost < prev_cost {
                panic!("häh");
            }
            prev_cost = b.cost;
            // println!("{}", b.cost);
            if b.cost > *upper_bound {
                break;
            }
            if b.free_pts.is_empty() {
                *upper_bound = b.cost;
                if b.cost == 0.0 {
                    panic!("weirf, {:#?}", b);
                }
                // println!(
                //     "returning path, self cost: {}, self: {:#?}, costs: {}",
                //     b.calc_lower_bound(costs),
                //     b,
                //     costs
                // );
                min_path = Some(b.path);
            } else {
                let result = b.explore(costs, upper_bound);
                if result.is_some() {
                    min_path = result;
                }
            };
        }

        if min_path.is_none() && upper_bound == &f64::MAX {
            panic!("error, returned");
        }

        min_path
    }
}
fn branch_and_bound<'a>(points: &'a Vec<Point>) -> Option<(f64, Vec<&'a Point>)> {
    let free_pts = (0..points.len()).collect::<Vec<_>>();
    let mut min_len = f64::MAX;
    let mut path = None;
    let mut matrix = CostList::new(points);
    // let cost = matrix.reduce();
    for i in 0..points.len() {
        let mut free_pts = free_pts.clone();
        free_pts.swap_remove(i);
        let mut root = Branch {
            cost: 0.0,
            free_pts,
            path: Path {
                pts: vec![i],
                len: 1,
            },
        };
        let cost = root.calc_lower_bound(&matrix);
        root.cost = cost;
        // println!("start, matrix: {}", root.matrix);
        if let Some(result) = root.explore(&matrix, &mut min_len) {
            path = Some(result.pts.iter().map(|i| &points[*i]).collect());
        } else if path.is_none() {
            panic!("error for pt nr. {}, upper: {min_len}", i);
        }
    }
    Some((min_len, path?))
}
fn draw_path(path: &Vec<&Point>, image: &mut RgbaImage, color: [u8; 4], offset: f64) {
    let mut pts = path.into_iter();
    let mut p_pt = pts.next().unwrap();
    for pt in pts {
        draw_line_segment_mut(
            image,
            ((p_pt.0 + offset) as f32, p_pt.1 as f32),
            ((pt.0 + offset) as f32, pt.1 as f32),
            Rgba(color),
        );
        p_pt = pt;
    }
}
fn main() {
    let start = Instant::now();
    let size = 1000.0;
    let mut rng = thread_rng();
    let points = get_points((size, size), 15, &mut rng);
    // let points = vec![
    //     Point(100.0, 200.0),
    //     Point(500.0, 200.0),
    //     Point(600.0, 300.0),
    // ];
    println!("Points: {:#?}", points);
    println!("path through permutation: ");
    // let min_path_unchecked = get_shortest_path(&points, false);
    // println!("old path len: {}", get_len(&min_path_unchecked.1));
    // let min_path_checked = get_shortest_path(&points, true);
    println!("path through branch and bound: ");
    let min_path_bnb = branch_and_bound(&points).unwrap();
    println!(
        "bnb len: {}, cost: {}",
        get_len(&min_path_bnb.1),
        min_path_bnb.0
    );
    // println!("old path len: {}", get_len(&min_path_unchecked.1));
    // println!("min_path: {:?}", min_path);
    let mut image = RgbaImage::from_fn(size as u32 * 2, size as u32, |_, _| {
        Rgba([0u8, 0u8, 0u8, 255u8])
    });
    // draw_path(
    // &min_path_unchecked.1,
    // &mut image,
    // [255u8, 0u8, 0u8, 255u8],
    // 0.0,
    // );
    let elapsed = start.elapsed();
    println!("took: {:?}", elapsed);
    draw_path(&min_path_bnb.1, &mut image, [0u8, 0u8, 255u8, 255u8], size);
    image.save("out.png").unwrap();
    println!("saved image");
}
