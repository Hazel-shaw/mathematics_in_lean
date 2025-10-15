import MIL.Common
import Mathlib.Data.Real.Basic
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a ]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]
  --\l表示箭头
  --mul 输入时按照当前字母顺序即可，并非需要按照输出顺序

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a ]
  rw [mul_assoc b ]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]


example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw[hyp]
  rw[hyp']
  rw[mul_comm]
  rw[sub_self]--功能包含于ring（这句可以用ring）  sub_self专门用来完成a-a=0的证明。

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
--同时执行多个rw命令一起使用，用comma隔开即可，You still see the incremental progress by placing the cursor after a comma in any list of rewrites.
end
-- section和end间 variable只需要定义一遍，方便在不同section内使用相同字母表示不同含义，防止混淆！
--variable用于括号外声明变量

--可以通过将声明放在<section ... end>块中来限定其作用域。

section
--一个命令来确定表达式的类型：
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

#check mul_assoc
#check two_mul a --!
--calc和ring无法#check？

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
--mul_add： “乘法对加法的分配律”，即对于数 x、y、z，有 x * (y + z) = x * y + x * z
--add_mul： “加法对乘法的分配”（从形式上更偏向乘法对加法分配的对称表述，或者在不同结合、展开场景下的分配律应用）
--add_mul: (x+y)*z=x*z+y*z



--calc 草稿纸式  长不等式的首选，证明更清晰。
-- A = B
--   = C
--   = D
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
     rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
--calc有严格的缩进来体现区块的起止位置
--以by开头的表达式是一个calc，即证明项。
end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw[mul_add,add_mul,add_mul]
  rw[← add_assoc]--拆括号
  rw[add_assoc (a*c) (b*c) (a*d)]
  rw[add_comm (b*c) (a*d) ]
  rw[← add_assoc]


--编写calc证明的一种方法是：
--先用sorry策略概述证明以进行论证，确保Lean接受这些表达式的模运算
--然后使用策略对各个步骤进行论证。


example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw[add_mul]
  rw[mul_sub]
  rw[pow_two a]
  rw[mul_sub]
  rw[pow_two b]
  rw[mul_comm b a]
  rw[add_sub]
  ring

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- ring策略非常强大，适用于任何交换环的恒等式


example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
