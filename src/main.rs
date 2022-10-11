extern crate rand;

use std::cmp::max;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::ops::Index;
use std::sync::atomic::{AtomicUsize, Ordering};

use rand::Rng;
use tracing::info;
use tracing_subscriber;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        // 设置各个模块的日志级别， 格式为sqlx=debug,tower_http=debug
        .with(tracing_subscriber::fmt::layer())
        .init();

    // let num1 = vec![1, 3];
    // let num2 = vec![2];
    //
    // let result = Solution::find_median_sorted_arrays(num1, num2);


    // let result = Solution::are_almost_equal(String::from("bank"), String::from("ankb"));
    // let bank = String::from("bank");
    // let result = &bank[2..3];

    // let result = Solution::longest_palindrome(String::from("babad"));

    let result = Solution::three_sum(vec![-1, 0, 1, 2, -1, -4]);
    // info!("{}", result);
    Ok(())
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    #[inline]
    fn new(val: i32) -> Self {
        ListNode {
            next: None,
            val,
        }
    }
}

struct Solution {}

impl Solution {
    /// `两数之和`
    /// https://leetcode.cn/problems/two-sum/?favorite=2ckc81c
    pub fn two_sum(nums: Vec<i32>, target: i32) -> Vec<i32> {
        let mut map: HashMap<i32, i32> = HashMap::new();

        for (index, data) in nums.iter().enumerate() {
            if map.contains_key(&(target - data)) {
                return vec![index as i32, map.get(&(target - data)).unwrap().clone()];
            }
            map.insert(data.clone(), index as i32);
        }
        vec![]
    }


    /// 两数相加
    /// https://leetcode.cn/problems/add-two-numbers/?favorite=2cktkvj
    pub fn add_two_numbers(l1: Option<Box<ListNode>>, l2: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
        fn carried(l1: Option<Box<ListNode>>, l2: Option<Box<ListNode>>, mut carry: i32) -> Option<Box<ListNode>> {
            if l1.is_none() && l2.is_none() && carry == 0 {
                None
            } else {
                Some(Box::new(ListNode {
                    next: carried(
                        l1.and_then(|x| {
                            carry += x.val;
                            x.next
                        }),
                        l2.and_then(|x| {
                            carry += x.val;
                            x.next
                        }),
                        carry / 10,
                    ),
                    val: carry % 10,
                }))
            }
        }
        carried(l1, l2, 0)
    }

    /// 无重复字符的最长子串
    /// https://leetcode.cn/problems/longest-substring-without-repeating-characters/?favorite=2cktkvj
    pub fn length_of_longest_substring(s: String) -> i32 {
        let charset = s.chars();
        let mut result = 0;
        let mut left = 0;
        let mut map: HashMap<char, i32> = HashMap::new();
        for (index, value) in charset.enumerate() {
            if map.contains_key(&value) {
                left = max(left, map.get(&value).unwrap() + 1)
            }
            map.insert(value, index as i32);
            result = max(result, index as i32 - left + 1)
        }
        result as i32
    }

    /// 寻找两个正序数组的中位数
    /// https://leetcode.cn/problems/median-of-two-sorted-arrays/
    pub fn find_median_sorted_arrays(nums1: Vec<i32>, nums2: Vec<i32>) -> f64 {
        // binaryHeap是最大堆的实现
        let mut min: BinaryHeap<Reverse<i32>> = BinaryHeap::new();
        let mut max: BinaryHeap<i32> = BinaryHeap::new();
        fn find_median_sorted_arrays_heap(nums: Vec<i32>, min: &mut BinaryHeap<Reverse<i32>>, max: &mut BinaryHeap<i32>) {
            for data in nums {
                if min.len() != max.len() {
                    min.push(Reverse(data));
                    max.push(min.pop().unwrap().0)
                } else {
                    max.push(data);
                    min.push(Reverse(max.pop().unwrap()))
                }
            }
        }
        find_median_sorted_arrays_heap(nums1, &mut min, &mut max);
        find_median_sorted_arrays_heap(nums2, &mut min, &mut max);
        if max.len() != min.len() {
            min.peek().unwrap().0 as f64
        } else {
            (max.peek().unwrap().clone() as f64 + min.peek().unwrap().0 as f64) / 2.0
        }
    }

    /// 仅执行一次字符串交换能否使两个字符串相等
    /// https://leetcode.cn/problems/check-if-one-string-swap-can-make-strings-equal/
    pub fn are_almost_equal(s1: String, s2: String) -> bool {
        if s1.len() != s2.len() {
            return false;
        }
        let mut a = None;
        let mut b = None;

        for i in 0..s1.len() {
            let index = i;
            if &s1[index..index + 1] == &s2[index..index + 1] {
                continue;
            } else if a.is_none() {
                a = Some(index);
            } else if b.is_none() {
                b = Some(index);
            } else {
                return false;
            }
        }
        if a == b && b.is_none() {
            return true;
        }
        if a.is_none() || b.is_none() {
            return false;
        }
        return s1[a.unwrap()..a.unwrap() + 1] == s2[b.unwrap()..b.unwrap() + 1] &&
            s1[b.unwrap()..b.unwrap() + 1] == s2[a.unwrap()..a.unwrap() + 1];
    }


    /// 最长回文子串
    /// https://leetcode.cn/problems/longest-palindromic-substring/?favorite=2cktkvj
    pub fn longest_palindrome(s: String) -> String {
        if s.len() <= 0 {
            return String::from("");
        }
        let mut start = 0;
        let mut end = 0;
        for i in 0..s.len() {
            let index = i as i32;
            let center_1 = Solution::center(&s, index, index);
            let center_2 = Solution::center(&s, index, index + 1);
            let len = max(center_1, center_2);
            if len > end - start {
                start = index - ((len - 1) / 2);
                end = index + len / 2;
            }
        }
        return String::from(&s[start as usize..(end + 1) as usize]);
    }

    fn center(s: &String, left: i32, right: i32) -> i32 {
        let mut current_left = left;
        let mut current_right = right;
        while current_left >= 0 && current_right < s.len() as i32 &&
            &s[current_left as usize..(current_left + 1) as usize] == &s[current_right as usize..(current_right + 1) as usize] {
            current_left = current_left - 1;
            current_right = current_right + 1;
        }
        current_right - current_left - 1
    }


    /// 三数之和
    /// https://leetcode.cn/problems/3sum/?favorite=2cktkvj
    pub fn three_sum(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let mut current_nums = nums;
        current_nums.sort();
        let mut result = vec![];
        for i in 0..current_nums.len() {
            if i > 0 && current_nums[i] == current_nums[i - 1] {
                continue;
            }
            let mut j = current_nums.len() - 1;
            let t = -current_nums[i];


            for k in (i + 1)..current_nums.len() {
                if k > i + 1 && current_nums[k] == current_nums[k - 1] {
                    continue;
                }
                while k < j && j < current_nums.len() && current_nums[k] + current_nums[j] > t {
                    j -= 1;
                }
                if k == j {
                    break;
                }
                if current_nums[k] + current_nums[j] == t {
                    result.push(vec![current_nums[i], current_nums[k], current_nums[j]]);
                }
            }
        }
        result
    }
}
