use std::cmp::max;
use std::collections::{BinaryHeap, HashMap};
use tracing::info;
use tracing_subscriber;
use std::cmp::Reverse;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

extern crate rand;

use rand::Rng;


fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        // 设置各个模块的日志级别， 格式为sqlx=debug,tower_http=debug
        .with(tracing_subscriber::fmt::layer())
        .init();

    let num1 = vec![1,3];
    let num2 = vec![2];

    let result = Solution::find_median_sorted_arrays(num1, num2);
    info!("{}", result);
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
    /** `两数之和`
                ```
                    https://leetcode.cn/problems/two-sum/?favorite=2ckc81c
                ```
     */
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


    /** `两数相加`
              ```
                  https://leetcode.cn/problems/add-two-numbers/?favorite=2cktkvj
              ```
     */
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
    /** `无重复字符的最长子串`
              ```
                  https://leetcode.cn/problems/longest-substring-without-repeating-characters/?favorite=2cktkvj
              ```
     */
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

    /** `寻找两个正序数组的中位数`
              ```
                  https://leetcode.cn/problems/median-of-two-sorted-arrays/
              ```
     */
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
        if max.len() != min.len(){
            min.peek().unwrap().0 as f64
        }else{
            (max.peek().unwrap().clone() as f64 + min.peek().unwrap().0 as f64) / 2.0
        }
    }
}
