
import Syntax.PreorderReasoning

%default total
plus_assoc : (n, m, p : Nat) -> (n + m) + p = n + (m + p)
plus_assoc 0 m p = Refl
plus_assoc (S k) m p = cong S (plus_assoc k m p)

plus_right_zero : (n : Nat) -> n = n + 0

plus_right_succ : (n, m : Nat) -> n + (S m) = S (n + m)

plus_comm : (m, n : Nat) -> m + n = n + m
plus_comm 0 0 = Refl
plus_comm 0 (S k) = cong S (plus_right_zero k)
plus_comm (S k) 0 = cong S (sym $ plus_right_zero k)
plus_comm (S k) (S j) = cong S (rewrite plus_right_succ k j in
                                rewrite plus_right_succ j k in cong S (plus_comm k j))

plus_rearrange : (m, n, p, q : Nat) ->  (m + n) + (p + q) = m + (n + p) + q
plus_rearrange m n p q = Calc $
                         |~ (m + n) + (p + q)
                         ~~ m + (n + (p + q)) ...(plus_assoc m n (p + q))
                         ~~ m + ((n + p) + q) ...(cong (m +) (sym $ plus_assoc n p q))
                         ~~ (m + (n + p)) + q ...(sym $ plus_assoc m (n + p) q)

swap : (n, m, p : Nat) -> m + (n + p) = n + (m + p)
swap n m p = Calc $
             |~ m + (n + p)
             ~~ (m + n) + p ...(sym $ plus_assoc m n p)
             ~~ (n + m) + p ...(cong (+ p) $ plus_comm m n)
             ~~ n + (m + p) ...(plus_assoc n m p)

distr : (m, n, p : Nat) -> (m + n) * p = m * p + n * p
distr 0 n p = Refl
distr (S k) n p = let rec = distr k n p in
                      rewrite plus_assoc p (k * p) (n * p) in
                              cong (p +) rec

mult_assoc : (m, n, p : Nat) -> (m * n) * p = m * (n * p)
mult_assoc 0 n p = Refl
mult_assoc (S k) n p = let rec = mult_assoc k n p in
                           rewrite distr n (k * n) p in
                                   cong ((n * p) + ) rec

mult_right_zero : (m : Nat) -> 0 = m * 0
mult_right_zero 0 = Refl
mult_right_zero (S k) = mult_right_zero k

mult_right_succ : (m, n: Nat) -> m * (S n) = m + (m * n)
mult_right_succ 0 n = Refl
mult_right_succ (S k) n = cong S $ rewrite mult_right_succ k n in
                                   rewrite swap n k (k * n) in
                                           Refl

mult_comm : (m, n : Nat) -> m * n = n * m
mult_comm 0 0 = Refl
mult_comm 0 (S k) = mult_right_zero k
mult_comm (S k) 0 = sym $ mult_comm 0 k
mult_comm (S k) (S j) = cong S $ rewrite mult_right_succ j k in
                                 rewrite mult_right_succ k j in
                                 rewrite swap j k (j * k) in
                                         cong (j +) $ cong (k +) $ mult_comm k j
