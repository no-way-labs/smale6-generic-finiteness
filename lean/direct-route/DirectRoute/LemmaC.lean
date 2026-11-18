import DirectRoute.LemmaB

/-!
Lemma C (T2). The proof follows the sketch of `docs/allN-direct-route-lean-task.md` §6: a cycle is two
periodic sequences `F`, `G` of pairs; the balance q = 0 comes from Lemma B; one integer potential for
each body replaces the paths; a level count gives two pairs through the lightest body at one level;
the corner estimate ends the proof. Of the trees only one fact is used: two pairs with the same node
have the same height.
-/

open Finset

/-- The potential of the sketch at the ζ-node of position `i`. -/
def potZ (a b : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => potZ a b i - a i + b i

/-- The potential at the ω-node of position `i`. -/
def potW (a b : ℕ → ℤ) (i : ℕ) : ℤ := potZ a b i - a i

theorem potZ_eq_sum (a b : ℕ → ℤ) (k : ℕ) : potZ a b k = ∑ i ∈ range k, (b i - a i) := by
  induction k with
  | zero => simp [potZ]
  | succ k ih => rw [Finset.sum_range_succ, ← ih, potZ]; ring

/-- Step 5 of the sketch: at every level there are as many `a` steps as `b` steps. -/
theorem level_count (r : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i, a i = 0 ∨ a i = 1) (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hbal : ∑ i ∈ range r, a i = ∑ i ∈ range r, b i) (c : ℤ) :
    ((range r).filter (fun i => a i = 1 ∧ potW a b i = c)).card
      = ((range r).filter (fun i => b i = 1 ∧ potW a b i = c)).card := by
  have hr : potZ a b r = 0 := by
    rw [potZ_eq_sum, Finset.sum_sub_distrib, hbal, sub_self]
  -- the indicator of the levels above `c`, along the positions
  let I : ℤ → ℤ := fun x => if c + 1 ≤ x then 1 else 0
  have tel : ∑ i ∈ range r, (I (potZ a b (i + 1)) - I (potZ a b i)) = 0 := by
    rw [Finset.sum_range_sub (fun i => I (potZ a b i)), hr]
    simp [potZ]
  have step : ∀ i, I (potZ a b (i + 1)) - I (potZ a b i)
      = (if b i = 1 ∧ potW a b i = c then (1 : ℤ) else 0)
        - (if a i = 1 ∧ potW a b i = c then (1 : ℤ) else 0) := by
    intro i
    have up : ∀ x : ℤ, I (x + 1) - I x = if x = c then 1 else 0 := by
      intro x
      simp only [I]
      split_ifs <;> omega
    have e1 : potZ a b (i + 1) = potW a b i + b i := by simp [potZ, potW]
    have e2 : potZ a b i = potW a b i + a i := by simp [potW]
    rw [e1, e2]
    generalize potW a b i = x
    have hx := up x
    rcases ha i with h | h <;> rcases hb i with h' | h' <;> simp [h, h'] <;> omega
  have key : ∑ i ∈ range r, (if a i = 1 ∧ potW a b i = c then (1 : ℤ) else 0)
      = ∑ i ∈ range r, (if b i = 1 ∧ potW a b i = c then (1 : ℤ) else 0) := by
    have : ∑ i ∈ range r, ((if b i = 1 ∧ potW a b i = c then (1 : ℤ) else 0)
        - (if a i = 1 ∧ potW a b i = c then (1 : ℤ) else 0)) = 0 := by
      have h := tel
      rw [Finset.sum_congr rfl (fun i _ => step i)] at h
      exact h
    rw [Finset.sum_sub_distrib] at this
    linarith
  have cast : ∀ p : ℕ → Prop, ∀ [DecidablePred p],
      (((range r).filter p).card : ℤ) = ∑ i ∈ range r, (if p i then (1 : ℤ) else 0) := by
    intro p _
    rw [Finset.card_filter]
    push_cast
    rfl
  have := cast (fun i => a i = 1 ∧ potW a b i = c)
  have := cast (fun i => b i = 1 ∧ potW a b i = c)
  exact_mod_cast (by linarith : (((range r).filter (fun i => a i = 1 ∧ potW a b i = c)).card : ℤ)
    = ((range r).filter (fun i => b i = 1 ∧ potW a b i = c)).card)

/-- The corner estimate (step 7 of the sketch) with the bound n + 2 on the coefficients. -/
theorem corner' (n L : ℕ) (τ : ℝ) (u : ℕ → ℝ) (v : ℕ → ℤ)
    (hu : Chamber n τ u) (hτ : (n : ℝ) ^ 2 ≤ τ) (hL2 : 2 ≤ L) (hL : L < n)
    (hsum : ∑ k ∈ range (L + 1), v k = 0) (hvL : v L ≤ -1)
    (hb : ∀ k, k < L → |(v k : ℝ)| ≤ n + 2) :
    ∑ k ∈ range (L + 1), (v k : ℝ) * u k < 0 := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hτ0 : 0 ≤ τ := le_trans (sq_nonneg _) hτ
  rw [sum_shift u v L (by omega) hsum]
  have hRL : 0 < u L - u 0 := chamber_pos hu hτ0 L (by omega) hL
  have hR' : 0 < u (L - 1) - u 0 := chamber_pos hu hτ0 (L - 1) (by omega) (by omega)
  have hstep := chamber_step hu L hL2 hL
  have hlast : (v L : ℝ) * (u L - u 0) ≤ -(u L - u 0) := by
    have : (v L : ℝ) ≤ -1 := by exact_mod_cast hvL
    nlinarith
  have hLn : (L : ℝ) ≤ n - 1 := by
    have h1 : ((L + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hL
    push_cast at h1
    linarith
  have hrest : ∑ k ∈ Ico 1 L, (v k : ℝ) * (u k - u 0)
      ≤ ((n : ℝ) + 2) * ((L : ℝ) - 1) * (u (L - 1) - u 0) := by
    have h1 := sum_bound hu hτ0 v L hL
    have h2 : (∑ k ∈ Ico 1 L, |(v k : ℝ)|) ≤ ((n : ℝ) + 2) * ((L : ℝ) - 1) := by
      calc (∑ k ∈ Ico 1 L, |(v k : ℝ)|) ≤ ∑ _k ∈ Ico 1 L, ((n : ℝ) + 2) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [Finset.mem_Ico] at hk
            exact hb k hk.2
        _ = ((n : ℝ) + 2) * ((L : ℝ) - 1) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega)]
            push_cast
            ring
    have h3 := mul_le_mul_of_nonneg_right h2 hR'.le
    have h4 := le_abs_self (∑ k ∈ Ico 1 L, (v k : ℝ) * (u k - u 0))
    linarith
  have hcoef : ((n : ℝ) + 2) * ((L : ℝ) - 1) ≤ 1 + τ := by
    have h1 : ((n : ℝ) + 2) * ((L : ℝ) - 1) ≤ ((n : ℝ) + 2) * ((n : ℝ) - 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have h5 := mul_le_mul_of_nonneg_right hcoef hR'.le
  linarith

/-- In the chamber the weights increase strictly. -/
theorem chamber_strict {n : ℕ} {τ : ℝ} {u : ℕ → ℝ} (hu : Chamber n τ u) (hτ0 : 0 ≤ τ)
    {i j : ℕ} (hij : i < j) (hj : j < n) : u i < u j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have := chamber_pos hu hτ0 j (by omega) hj
    linarith
  · have h1 := chamber_mono hu hτ0 (i + 1) j (by omega) (by omega) hj
    have h2 := hu.2 (i + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at h2
    have h3 := chamber_pos hu hτ0 i hi (by omega)
    have := mul_nonneg hτ0 h3.le
    linarith

namespace LC

/-! ### Real ultrametrics -/

theorem ultra_symm {n : ℕ} {d : ℕ → ℕ → ℝ} (h : IsUltra n fun x y => (d x y : WithTop ℝ))
    {x y : ℕ} (hx : x < n) (hy : y < n) : d x y = d y x := by
  have h1 : ((d x y : ℝ) : WithTop ℝ) = (d y x : ℝ) := h.1 x y hx hy
  exact_mod_cast h1

theorem ultra_tri {n : ℕ} {d : ℕ → ℕ → ℝ} (h : IsUltra n fun x y => (d x y : WithTop ℝ))
    {x y t : ℕ} (hx : x < n) (hy : y < n) (ht : t < n) (hxy : x ≠ y) (hyt : y ≠ t) (hxt : x ≠ t) :
    min (d x y) (d y t) ≤ d x t := by
  have h1 : min ((d x y : ℝ) : WithTop ℝ) (d y t : ℝ) ≤ (d x t : ℝ) := h.2 x y t hx hy ht hxy hyt hxt
  exact_mod_cast h1

theorem mem_node {N : ℕ} {d : ℕ → ℕ → ℝ} {e : ℕ × ℕ} {p : ℕ} :
    p ∈ node N (fun x y => (d x y : WithTop ℝ)) e ↔ p < N ∧ (p = e.1 ∨ d e.1 e.2 ≤ d e.1 p) := by
  simp [node]

/-- Two different points of a node are at least as high as the node. -/
theorem node_pair {n : ℕ} {d : ℕ → ℕ → ℝ} (h : IsUltra n fun x y => (d x y : WithTop ℝ))
    {a b p p' : ℕ} (ha : a < n) (hp : p ∈ node n (fun x y => (d x y : WithTop ℝ)) (a, b))
    (hp' : p' ∈ node n (fun x y => (d x y : WithTop ℝ)) (a, b)) (hne : p ≠ p') :
    d a b ≤ d p p' := by
  rw [mem_node] at hp hp'
  obtain ⟨hpn, hp⟩ := hp
  obtain ⟨hpn', hp'⟩ := hp'
  simp only at hp hp'
  by_cases hpa : p = a
  · subst hpa
    rcases hp' with rfl | hp'
    · exact absurd rfl hne
    · exact hp'
  · by_cases hpa' : p' = a
    · subst hpa'
      rcases hp with rfl | hp
      · exact absurd rfl hne
      · rw [ultra_symm h hpn hpn']
        exact hp
    · have h1 : d a b ≤ d a p := by
        rcases hp with rfl | hp
        · exact absurd rfl hpa
        · exact hp
      have h2 : d a b ≤ d a p' := by
        rcases hp' with rfl | hp'
        · exact absurd rfl hpa'
        · exact hp'
      have h3 := ultra_tri h hpn ha hpn' hpa (Ne.symm hpa') hne
      rw [ultra_symm h hpn ha] at h3
      exact le_trans (le_min h1 h2) h3

/-- Two pairs with the same node have the same height. -/
theorem node_height_eq {n : ℕ} {d : ℕ → ℕ → ℝ} (h : IsUltra n fun x y => (d x y : WithTop ℝ))
    {a b a' b' : ℕ} (ha : a < n) (hb : b < n) (ha' : a' < n) (hb' : b' < n) (hab : a ≠ b)
    (hab' : a' ≠ b')
    (heq : node n (fun x y => (d x y : WithTop ℝ)) (a, b) = node n (fun x y => (d x y : WithTop ℝ)) (a', b')) :
    d a b = d a' b' := by
  have m1 : a ∈ node n (fun x y => (d x y : WithTop ℝ)) (a, b) := mem_node.mpr ⟨ha, Or.inl rfl⟩
  have m2 : b ∈ node n (fun x y => (d x y : WithTop ℝ)) (a, b) := mem_node.mpr ⟨hb, Or.inr le_rfl⟩
  have m1' : a' ∈ node n (fun x y => (d x y : WithTop ℝ)) (a', b') := mem_node.mpr ⟨ha', Or.inl rfl⟩
  have m2' : b' ∈ node n (fun x y => (d x y : WithTop ℝ)) (a', b') := mem_node.mpr ⟨hb', Or.inr le_rfl⟩
  apply le_antisymm
  · rw [← heq] at m1' m2'
    exact node_pair h ha m1' m2' hab'
  · rw [heq] at m1 m2
    exact node_pair h ha' m1 m2 hab

/-! ### The indicator of a body on a pair -/

/-- 1 if the body `k` lies on the pair `e`, else 0. -/
def on (e : ℕ × ℕ) (k : ℕ) : ℤ := if e.1 = k ∨ e.2 = k then 1 else 0

theorem on_cases (e : ℕ × ℕ) (k : ℕ) : on e k = 0 ∨ on e k = 1 := by
  unfold on
  split_ifs <;> simp

theorem sum_on_mul {n : ℕ} {e : ℕ × ℕ} (h1 : e.1 < e.2) (h2 : e.2 < n) (c : ℕ → ℝ) :
    ∑ k ∈ range n, (on e k : ℝ) * c k = c e.1 + c e.2 := by
  have hne : e.1 ≠ e.2 := Nat.ne_of_lt h1
  have key : ∀ k, (on e k : ℝ) * c k
      = (if e.1 = k then c k else 0) + (if e.2 = k then c k else 0) := by
    intro k
    unfold on
    by_cases ha : e.1 = k
    · have hb : ¬e.2 = k := fun hb => hne (ha.trans hb.symm)
      simp [ha, hb]
    · by_cases hb : e.2 = k <;> simp [ha, hb]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq, mem_range]
  simp [h2, lt_trans h1 h2]

theorem sum_on {n : ℕ} {e : ℕ × ℕ} (h1 : e.1 < e.2) (h2 : e.2 < n) :
    ∑ k ∈ range n, on e k = 2 := by
  have h := sum_on_mul h1 h2 (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  have h' : ((∑ k ∈ range n, on e k : ℤ) : ℝ) = 2 := by
    push_cast
    linarith
  exact_mod_cast h'

/-- A body lies on at most n pairs of a sequence of different pairs of bodies. -/
theorem cnt_le {n r : ℕ} {F : ℕ → ℕ × ℕ} (hlt : ∀ i, (F i).1 < (F i).2 ∧ (F i).2 < n)
    (hinj : ∀ i j, i < r → j < r → F i = F j → i = j) (k : ℕ) :
    ∑ i ∈ range r, on (F i) k ≤ n := by
  have h1 : ∑ i ∈ range r, on (F i) k
      = (((range r).filter fun i => (F i).1 = k ∨ (F i).2 = k).card : ℤ) := by
    unfold on
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [h1]
  have h2 : ((range r).filter fun i => (F i).1 = k ∨ (F i).2 = k).card ≤ (range n).card := by
    apply Finset.card_le_card_of_injOn (fun i => if (F i).1 = k then (F i).2 else (F i).1)
    · intro i _
      simp only [coe_range, Set.mem_Iio]
      split_ifs
      · exact (hlt i).2
      · exact lt_trans (hlt i).1 (hlt i).2
    · intro i hi j hj hij
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      apply hinj i j hi.1 hj.1
      have hi' := hlt i
      have hj' := hlt j
      obtain ⟨_, hi2⟩ := hi
      obtain ⟨_, hj2⟩ := hj
      simp only at hij
      refine Prod.ext ?_ ?_ <;> (split_ifs at hij <;> omega)
  rw [card_range] at h2
  exact_mod_cast h2

theorem cnt_nonneg {r : ℕ} {F : ℕ → ℕ × ℕ} (k : ℕ) : 0 ≤ ∑ i ∈ range r, on (F i) k := by
  apply Finset.sum_nonneg
  intro i _
  rcases on_cases (F i) k with h | h <;> rw [h] <;> norm_num

/-! ### The cycle as two periodic sequences -/

/-- The data of a cycle of pairs with the largest Ψ: `F i` and `G i` meet in a node of ω, `G i` and
`F (i + 1)` in a node of ζ; only the heights of these nodes are kept. -/
structure Setup (n : ℕ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ) (r : ℕ) (F G : ℕ → ℕ × ℕ) (P : ℝ) : Prop where
  rpos : 1 ≤ r
  per_F : ∀ i, F (i + r) = F i
  lt_F : ∀ i, (F i).1 < (F i).2 ∧ (F i).2 < n
  lt_G : ∀ i, (G i).1 < (G i).2 ∧ (G i).2 < n
  psi_F : ∀ i, psiPair u z w (F i).1 (F i).2 = P
  psi_G : ∀ i, psiPair u z w (G i).1 (G i).2 = P
  top : ∀ a b, a < b → b < n → psiPair u z w a b ≤ P
  w_adj : ∀ i, w (F i).1 (F i).2 = w (G i).1 (G i).2
  z_adj : ∀ i, z (G i).1 (G i).2 = z (F (i + 1)).1 (F (i + 1)).2
  inj_F : ∀ i j, i < r → j < r → F i = F j → i = j
  inj_G : ∀ i j, i < r → j < r → G i = G j → i = j
  ne_FG : ∀ i j, i < r → j < r → F i ≠ G j

/-- The height of the pair at position `i`. -/
abbrev HT (d : ℕ → ℕ → ℝ) (F : ℕ → ℕ × ℕ) (i : ℕ) : ℝ := d (F i).1 (F i).2

/-- The sum of the weights of the two bodies of a pair. -/
abbrev UU (u : ℕ → ℝ) (e : ℕ × ℕ) : ℝ := u e.1 + u e.2

/-- The coefficient q_k of the cycle. -/
def qv (r : ℕ) (F G : ℕ → ℕ × ℕ) (k : ℕ) : ℤ := ∑ i ∈ range r, (on (F i) k - on (G i) k)

namespace Setup

variable {n : ℕ} {u : ℕ → ℝ} {z w : ℕ → ℕ → ℝ} {r : ℕ} {F G : ℕ → ℕ × ℕ} {P : ℝ}

theorem rel1 (S : Setup n u z w r F G P) (i : ℕ) :
    HT z F i + HT w F i = 2 * P + 2 * UU u (F i) := by
  have h := S.psi_F i
  unfold psiPair at h
  simp only [HT, UU]
  linarith

theorem rel2 (S : Setup n u z w r F G P) (i : ℕ) :
    HT z F (i + 1) + HT w F i = 2 * P + 2 * UU u (G i) := by
  have h := S.psi_G i
  have h1 := S.w_adj i
  have h2 := S.z_adj i
  unfold psiPair at h
  simp only [HT, UU]
  linarith

theorem qu (S : Setup n u z w r F G P) : ∑ k ∈ range n, (qv r F G k : ℝ) * u k = 0 := by
  have h1 : ∀ k, (qv r F G k : ℝ) * u k
      = ∑ i ∈ range r, ((on (F i) k : ℝ) * u k - (on (G i) k : ℝ) * u k) := by
    intro k
    unfold qv
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ k ∈ range n, ((on (F i) k : ℝ) * u k - (on (G i) k : ℝ) * u k)
      = (HT z F i - HT z F (i + 1)) / 2 := by
    intro i
    rw [Finset.sum_sub_distrib, sum_on_mul (S.lt_F i).1 (S.lt_F i).2,
      sum_on_mul (S.lt_G i).1 (S.lt_G i).2]
    have e1 := S.rel1 i
    have e2 := S.rel2 i
    simp only [UU] at e1 e2
    linarith
  simp only [h2]
  rw [← Finset.sum_div, Finset.sum_range_sub' (fun i => HT z F i)]
  have h3 : HT z F r = HT z F 0 := by
    have := S.per_F 0
    simp only [zero_add] at this
    simp only [HT, this]
  rw [h3]
  simp

theorem qsum (S : Setup n u z w r F G P) : ∑ k ∈ range n, qv r F G k = 0 := by
  unfold qv
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_sub_distrib, sum_on (S.lt_F i).1 (S.lt_F i).2, sum_on (S.lt_G i).1 (S.lt_G i).2]
  simp

theorem q_abs (S : Setup n u z w r F G P) (k : ℕ) : |(qv r F G k : ℝ)| ≤ n := by
  have h1 := cnt_le (r := r) S.lt_F S.inj_F k
  have h2 := cnt_le (r := r) S.lt_G S.inj_G k
  have h3 := cnt_nonneg (r := r) (F := F) k
  have h4 := cnt_nonneg (r := r) (F := G) k
  have e : qv r F G k = ∑ i ∈ range r, on (F i) k - ∑ i ∈ range r, on (G i) k := by
    unfold qv
    rw [Finset.sum_sub_distrib]
  have h5 : |qv r F G k| ≤ (n : ℤ) := by
    rw [e, abs_le]
    constructor <;> linarith
  exact_mod_cast h5

/-- The balance: q = 0 (step 2 of the sketch, (C2) of the brief). -/
theorem q_zero {τ : ℝ} (S : Setup n u z w r F G P) (hu : Chamber n τ u) (hτ : (n : ℝ) ^ 2 ≤ τ) :
    ∀ k, k < n → qv r F G k = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k0, hk0, hq0⟩ := hcon
  have hτ0 : 0 ≤ τ := le_trans (sq_nonneg _) hτ
  have hmP : qv r F G (Nat.findGreatest (fun k => qv r F G k ≠ 0) (n - 1)) ≠ 0 :=
    Nat.findGreatest_spec (P := fun k => qv r F G k ≠ 0) (by omega : k0 ≤ n - 1) hq0
  have hmle : Nat.findGreatest (fun k => qv r F G k ≠ 0) (n - 1) ≤ n - 1 := Nat.findGreatest_le _
  have hgt : ∀ k, Nat.findGreatest (fun k => qv r F G k ≠ 0) (n - 1) < k → k < n →
      qv r F G k = 0 := by
    intro k hk hkn
    by_contra h
    exact Nat.findGreatest_is_greatest hk (by omega) h
  generalize Nat.findGreatest (fun k => qv r F G k ≠ 0) (n - 1) = m at hmP hmle hgt
  have hsub : range (m + 1) ⊆ range n := by
    intro x hx
    rw [mem_range] at hx ⊢
    omega
  have hsum : ∑ j ∈ range (m + 1), qv r F G j = 0 := by
    rw [Finset.sum_subset hsub, S.qsum]
    intro x hx hx'
    rw [mem_range] at hx hx'
    exact hgt x (by omega) hx
  have hqu : ∑ j ∈ range (m + 1), (qv r F G j : ℝ) * u j = 0 := by
    rw [Finset.sum_subset hsub, S.qu]
    intro x hx hx'
    rw [mem_range] at hx hx'
    rw [hgt x (by omega) hx]
    simp
  have hqm1 : (1 : ℝ) ≤ |(qv r F G m : ℝ)| := by exact_mod_cast Int.one_le_abs hmP
  have hS : (∑ j ∈ Ico 1 m, |(qv r F G j : ℝ)|) ≤ (n : ℝ) ^ 2 := by
    calc (∑ j ∈ Ico 1 m, |(qv r F G j : ℝ)|) ≤ ∑ _j ∈ Ico 1 m, (n : ℝ) :=
          Finset.sum_le_sum fun j _ => S.q_abs j
      _ = ((m - 1 : ℕ) : ℝ) * n := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (n : ℝ) * n := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
          exact_mod_cast (by omega : m - 1 ≤ n)
      _ = (n : ℝ) ^ 2 := by ring
  have hS0 : 0 ≤ ∑ j ∈ Ico 1 m, |(qv r F G j : ℝ)| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hτ' : (∑ j ∈ Ico 1 m, |(qv r F G j : ℝ)|) / |(qv r F G m : ℝ)| - 1 ≤ τ := by
    have := div_le_self hS0 hqm1
    linarith
  exact lemmaB_proof n τ u (qv r F G) m hu hτ0 (by omega) hmP hsum hτ' hqu

/-! ### Potentials -/

theorem on_nonneg (e : ℕ × ℕ) (k : ℕ) : 0 ≤ on e k := by
  rcases on_cases e k with h | h <;> rw [h] <;> norm_num

theorem on_le_one (e : ℕ × ℕ) (k : ℕ) : on e k ≤ 1 := by
  rcases on_cases e k with h | h <;> rw [h] <;> norm_num

theorem on_eq_one_iff (e : ℕ × ℕ) (k : ℕ) : on e k = 1 ↔ e.1 = k ∨ e.2 = k := by
  unfold on
  split_ifs with h <;> simp [h]

/-- The potential of the body `k` at the ζ-node of position `i`. -/
abbrev pz (F G : ℕ → ℕ × ℕ) (k i : ℕ) : ℤ := potZ (fun i => on (F i) k) (fun i => on (G i) k) i

/-- The potential of the body `k` at the ω-node of position `i`. -/
abbrev pw (F G : ℕ → ℕ × ℕ) (k i : ℕ) : ℤ := potW (fun i => on (F i) k) (fun i => on (G i) k) i

theorem pz_sub_pw (k i : ℕ) : pz F G k i - pw F G k i = on (F i) k := by
  simp [pz, pw, potW]

theorem pz_succ (k i : ℕ) : pz F G k (i + 1) - pw F G k i = on (G i) k := by
  simp [pz, pw, potW, potZ]

/-- The height identity (step 4 of the sketch). -/
theorem height_id (S : Setup n u z w r F G P) (i j : ℕ) :
    HT z F i + HT w F j - 2 * P
      = 2 * ∑ k ∈ range n, ((pz F G k i - pw F G k j : ℤ) : ℝ) * u k := by
  have hA : ∀ i, ∑ k ∈ range n, ((pz F G k i : ℝ) - (pw F G k i : ℝ)) * u k = UU u (F i) := by
    intro i
    have h : ∀ k, ((pz F G k i : ℝ) - (pw F G k i : ℝ)) * u k = (on (F i) k : ℝ) * u k := by
      intro k
      rw [← pz_sub_pw (F := F) (G := G) k i]
      push_cast
      ring
    simp only [h]
    exact sum_on_mul (S.lt_F i).1 (S.lt_F i).2 u
  have hB : ∀ i, ∑ k ∈ range n, ((pz F G k (i + 1) : ℝ) - (pw F G k i : ℝ)) * u k = UU u (G i) := by
    intro i
    have h : ∀ k, ((pz F G k (i + 1) : ℝ) - (pw F G k i : ℝ)) * u k = (on (G i) k : ℝ) * u k := by
      intro k
      rw [← pz_succ (F := F) (G := G) k i]
      push_cast
      ring
    simp only [h]
    exact sum_on_mul (S.lt_G i).1 (S.lt_G i).2 u
  have hH : ∀ i, HT z F i - 2 * ∑ k ∈ range n, (pz F G k i : ℝ) * u k
      = HT z F 0 - 2 * ∑ k ∈ range n, (pz F G k 0 : ℝ) * u k := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih]
      have e1 := S.rel1 i
      have e2 := S.rel2 i
      have a := hA i
      have b := hB i
      simp only [sub_mul, Finset.sum_sub_distrib] at a b
      linarith
  have a := hA j
  have e1 := S.rel1 j
  have hi := hH i
  have hj := hH j
  simp only [sub_mul, Finset.sum_sub_distrib] at a
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith

/-- The coefficients of the height identity add to 2. -/
theorem sum_sigma (S : Setup n u z w r F G P) (i j : ℕ) :
    ∑ k ∈ range n, (pz F G k i - pw F G k j) = 2 := by
  have hA : ∀ i, ∑ k ∈ range n, pz F G k i - ∑ k ∈ range n, pw F G k i = 2 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    simp only [pz_sub_pw]
    exact sum_on (S.lt_F i).1 (S.lt_F i).2
  have hB : ∀ i, ∑ k ∈ range n, pz F G k (i + 1) - ∑ k ∈ range n, pw F G k i = 2 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    simp only [pz_succ]
    exact sum_on (S.lt_G i).1 (S.lt_G i).2
  have hH : ∀ i, ∑ k ∈ range n, pz F G k i = ∑ k ∈ range n, pz F G k 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih]
      have a := hA i
      have b := hB i
      linarith
  have a := hA j
  have hi := hH i
  have hj := hH j
  rw [Finset.sum_sub_distrib]
  linarith

theorem pz_diff_le (S : Setup n u z w r F G P) (k : ℕ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ r) :
    |pz F G k b - pz F G k a| ≤ (n : ℤ) := by
  have e : pz F G k b - pz F G k a = ∑ t ∈ Ico a b, (on (G t) k - on (F t) k) := by
    simp only [pz, potZ_eq_sum]
    rw [Finset.sum_Ico_eq_sub _ hab]
  have hsub : Ico a b ⊆ range r := by
    intro x hx
    rw [mem_Ico] at hx
    rw [mem_range]
    omega
  have hg : ∑ t ∈ Ico a b, on (G t) k ≤ n :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => on_nonneg _ _)
      (cnt_le S.lt_G S.inj_G k)
  have hf : ∑ t ∈ Ico a b, on (F t) k ≤ n :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => on_nonneg _ _)
      (cnt_le S.lt_F S.inj_F k)
  have hg0 : 0 ≤ ∑ t ∈ Ico a b, on (G t) k := Finset.sum_nonneg fun t _ => on_nonneg _ _
  have hf0 : 0 ≤ ∑ t ∈ Ico a b, on (F t) k := Finset.sum_nonneg fun t _ => on_nonneg _ _
  rw [e, Finset.sum_sub_distrib, abs_le]
  constructor <;> linarith

theorem sigma_abs (S : Setup n u z w r F G P) (k : ℕ) {i j : ℕ} (hi : i ≤ r) (hj : j < r) :
    |pz F G k i - pw F G k j| ≤ (n : ℤ) + 1 := by
  have e : pz F G k i - pw F G k j = (pz F G k i - pz F G k j) + on (F j) k := by
    have := pz_sub_pw (F := F) (G := G) k j
    linarith
  have h1 : |pz F G k i - pz F G k j| ≤ (n : ℤ) := by
    rcases le_total j i with h | h
    · exact S.pz_diff_le k h hi
    · rw [abs_sub_comm]
      exact S.pz_diff_le k h hj.le
  have h2 := on_nonneg (F j) k
  have h3 := on_le_one (F j) k
  rw [abs_le] at h1 ⊢
  rw [e]
  constructor <;> linarith

theorem sigma_zero (k : ℕ) {i j : ℕ} (hi : i ≤ r) (hj : j < r)
    (h : ∀ t, t < r → on (F t) k = 0 ∧ on (G t) k = 0) : pz F G k i - pw F G k j = 0 := by
  have hz : ∀ a, a ≤ r → pz F G k a = 0 := by
    intro a ha
    simp only [pz, potZ_eq_sum]
    apply Finset.sum_eq_zero
    intro t ht
    rw [mem_range] at ht
    rw [(h t (by omega)).1, (h t (by omega)).2]
    simp
  have e := pz_sub_pw (F := F) (G := G) k j
  rw [hz j hj.le, (h j hj).1] at e
  rw [hz i hi]
  linarith

/-- Step 5 of the sketch: two pairs through the body `L`, one at an odd and one at an even place, whose
ω-nodes are at the same level. -/
theorem level_pick {L : ℕ} (hq : qv r F G L = 0)
    (hon : ∃ i, i < r ∧ (on (F i) L = 1 ∨ on (G i) L = 1)) :
    ∃ i j, i < r ∧ j < r ∧ on (F i) L = 1 ∧ on (G j) L = 1 ∧ pw F G L i = pw F G L j := by
  have hbal : ∑ i ∈ range r, on (F i) L = ∑ i ∈ range r, on (G i) L := by
    unfold qv at hq
    rw [Finset.sum_sub_distrib] at hq
    linarith
  obtain ⟨i0, hi0, h | h⟩ := hon
  · have hc := level_count r (fun i => on (F i) L) (fun i => on (G i) L) (fun i => on_cases _ _)
      (fun i => on_cases _ _) hbal (pw F G L i0)
    have hmem : i0 ∈ (range r).filter
        (fun i => on (F i) L = 1 ∧ potW (fun i => on (F i) L) (fun i => on (G i) L) i = pw F G L i0) := by
      rw [mem_filter, mem_range]
      exact ⟨hi0, h, rfl⟩
    have hpos := Finset.card_pos.mpr ⟨i0, hmem⟩
    rw [hc] at hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [mem_filter, mem_range] at hj
    exact ⟨i0, j, hi0, hj.1, h, hj.2.1, hj.2.2.symm⟩
  · have hc := level_count r (fun i => on (F i) L) (fun i => on (G i) L) (fun i => on_cases _ _)
      (fun i => on_cases _ _) hbal (pw F G L i0)
    have hmem : i0 ∈ (range r).filter
        (fun i => on (G i) L = 1 ∧ potW (fun i => on (F i) L) (fun i => on (G i) L) i = pw F G L i0) := by
      rw [mem_filter, mem_range]
      exact ⟨hi0, h, rfl⟩
    have hpos := Finset.card_pos.mpr ⟨i0, hmem⟩
    rw [← hc] at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    rw [mem_filter, mem_range] at hi
    exact ⟨i, i0, hi.1, hi0, hi.2.1, h, hi.2.2⟩

/-! ### The contradiction -/

/-- No cycle exists over a chamber vector (steps 6 and 7 of the sketch). -/
theorem contra {τ : ℝ} (S : Setup n u z w r F G P) (hu : Chamber n τ u) (hτ : (n : ℝ) ^ 2 ≤ τ)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ)) :
    False := by
  classical
  have hτ0 : 0 ≤ τ := le_trans (sq_nonneg _) hτ
  have hq := S.q_zero hu hτ
  -- the lightest body on the cycle
  obtain ⟨L, hLn, hLon, hLmax⟩ : ∃ L, L < n ∧ (∃ i, i < r ∧ (on (F i) L = 1 ∨ on (G i) L = 1)) ∧
      ∀ k, k < n → (∃ i, i < r ∧ (on (F i) k = 1 ∨ on (G i) k = 1)) → k ≤ L := by
    have hT : ((range n).filter fun k => ∃ i, i < r ∧ (on (F i) k = 1 ∨ on (G i) k = 1)).Nonempty := by
      refine ⟨(F 0).1, ?_⟩
      rw [mem_filter, mem_range]
      exact ⟨lt_trans (S.lt_F 0).1 (S.lt_F 0).2, 0, S.rpos, Or.inl ((on_eq_one_iff _ _).mpr (Or.inl rfl))⟩
    have hm := Finset.max'_mem _ hT
    rw [mem_filter, mem_range] at hm
    refine ⟨_, hm.1, hm.2, fun k hk hk' => Finset.le_max' _ k ?_⟩
    rw [mem_filter, mem_range]
    exact ⟨hk, hk'⟩
  obtain ⟨i, j, hi, hj, hFi, hGj, hlev⟩ := level_pick (hq L hLn) hLon
  -- the two pairs are (x, L) and (x', L)
  have hF2 : (F i).2 = L := by
    rcases (on_eq_one_iff _ _).mp hFi with h | h
    · have h1 := (S.lt_F i).1
      have h2 := hLmax (F i).2 (S.lt_F i).2 ⟨i, hi, Or.inl ((on_eq_one_iff _ _).mpr (Or.inr rfl))⟩
      omega
    · exact h
  have hG2 : (G j).2 = L := by
    rcases (on_eq_one_iff _ _).mp hGj with h | h
    · have h1 := (S.lt_G j).1
      have h2 := hLmax (G j).2 (S.lt_G j).2 ⟨j, hj, Or.inr ((on_eq_one_iff _ _).mpr (Or.inr rfl))⟩
      omega
    · exact h
  have hxL : (F i).1 < L := hF2 ▸ (S.lt_F i).1
  have hx'L : (G j).1 < L := hG2 ▸ (S.lt_G j).1
  have hxx' : (F i).1 ≠ (G j).1 := by
    intro h
    exact S.ne_FG i j hi hj (Prod.ext h (hF2.trans hG2.symm))
  generalize hx : (F i).1 = x at hxL hxx'
  generalize hx' : (G j).1 = x' at hx'L hxx'
  have hxn : x < n := lt_trans hxL hLn
  have hx'n : x' < n := lt_trans hx'L hLn
  have hux : u x < u L := chamber_strict hu hτ0 hxL hLn
  have hux' : u x' < u L := chamber_strict hu hτ0 hx'L hLn
  -- the four heights
  have ea1 : HT z F i = z x L := by simp only [HT, hx, hF2]
  have eb1 : HT w F i = w x L := by simp only [HT, hx, hF2]
  have ea2 : HT z F (j + 1) = z x' L := by
    have := S.z_adj j
    simp only [HT, hx', hG2] at this ⊢
    exact this.symm
  have eb2 : HT w F j = w x' L := by
    have := S.w_adj j
    simp only [HT, hx', hG2] at this ⊢
    exact this
  have r1 : z x L + w x L = 2 * P + 2 * (u x + u L) := by
    have := S.rel1 i
    simp only [UU, hx, hF2] at this
    rw [ea1, eb1] at this
    exact this
  have r2 : z x' L + w x' L = 2 * P + 2 * (u x' + u L) := by
    have := S.psi_G j
    simp only [hx', hG2] at this
    unfold psiPair at this
    linarith
  -- the pair (x, x')
  have zt : min (z x L) (z x' L) ≤ z x x' := by
    have := ultra_tri hz hxn hLn hx'n (Nat.ne_of_lt hxL) (Nat.ne_of_gt hx'L) hxx'
    rwa [ultra_symm hz hLn hx'n] at this
  have wt : min (w x L) (w x' L) ≤ w x x' := by
    have := ultra_tri hw hxn hLn hx'n (Nat.ne_of_lt hxL) (Nat.ne_of_gt hx'L) hxx'
    rwa [ultra_symm hw hLn hx'n] at this
  have hpsi : (z x x' + w x x') / 2 - u x - u x' ≤ P := by
    rcases lt_or_gt_of_ne hxx' with h | h
    · exact S.top x x' h hx'n
    · have := S.top x' x h hxn
      unfold psiPair at this
      rw [ultra_symm hz hx'n hxn, ultra_symm hw hx'n hxn] at this
      linarith
  -- a corner gives a contradiction
  have corner_contra : ∀ I J, I ≤ r → J < r → pz F G L I - pw F G L J = 1 →
      ∑ k ∈ range n, ((pz F G k I - pw F G k J : ℤ) : ℝ) * u k ≤ u x + u x' → False := by
    intro I J hI hJ hσL hle
    have hL2 : 2 ≤ L := by omega
    have hsub : range (L + 1) ⊆ range n := by
      intro t ht
      rw [mem_range] at ht ⊢
      omega
    have hoff : ∀ k, k < n → L < k → pz F G k I - pw F G k J = 0 := by
      intro k hk hLk
      apply sigma_zero k hI hJ
      intro t ht
      constructor
      · rcases on_cases (F t) k with h | h
        · exact h
        · have := hLmax k hk ⟨t, ht, Or.inl h⟩
          omega
      · rcases on_cases (G t) k with h | h
        · exact h
        · have := hLmax k hk ⟨t, ht, Or.inr h⟩
          omega
    have hv0 : ∀ k, k ∈ range n → k ∉ range (L + 1) →
        ((if k = x then (1 : ℤ) else 0) + (if k = x' then 1 else 0) - (pz F G k I - pw F G k J)) = 0 := by
      intro k hk hk'
      rw [mem_range] at hk hk'
      rw [hoff k hk (by omega)]
      have h1 : k ≠ x := by omega
      have h2 : k ≠ x' := by omega
      simp [h1, h2]
    have hsum : ∑ k ∈ range (L + 1),
        ((if k = x then (1 : ℤ) else 0) + (if k = x' then 1 else 0) - (pz F G k I - pw F G k J)) = 0 := by
      rw [Finset.sum_subset hsub hv0, Finset.sum_sub_distrib, Finset.sum_add_distrib, S.sum_sigma I J]
      simp [hxn, hx'n]
    have hvL : ((if L = x then (1 : ℤ) else 0) + (if L = x' then 1 else 0)
        - (pz F G L I - pw F G L J)) ≤ -1 := by
      have h1 : L ≠ x := by omega
      have h2 : L ≠ x' := by omega
      rw [hσL]
      simp [h1, h2]
    have hb : ∀ k, k < L → |(((if k = x then (1 : ℤ) else 0) + (if k = x' then 1 else 0)
        - (pz F G k I - pw F G k J) : ℤ) : ℝ)| ≤ (n : ℝ) + 2 := by
      intro k hk
      have h1 := S.sigma_abs k hI hJ
      have h2 : |((if k = x then (1 : ℤ) else 0) + (if k = x' then 1 else 0)
          - (pz F G k I - pw F G k J))| ≤ (n : ℤ) + 2 := by
        rw [abs_le] at h1 ⊢
        constructor <;> split_ifs <;> omega
      exact_mod_cast h2
    have hc := corner' n L τ u
      (fun k => (if k = x then (1 : ℤ) else 0) + (if k = x' then 1 else 0) - (pz F G k I - pw F G k J))
      hu hτ hL2 hLn hsum hvL hb
    have hsumu : ∑ k ∈ range (L + 1),
        (((if k = x then (1 : ℤ) else 0) + (if k = x' then 1 else 0) - (pz F G k I - pw F G k J) : ℤ) : ℝ)
          * u k
        = u x + u x' - ∑ k ∈ range n, ((pz F G k I - pw F G k J : ℤ) : ℝ) * u k := by
      rw [Finset.sum_subset hsub]
      · push_cast
        simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq', mem_range, hxn, hx'n, if_true]
      · intro k hk hk'
        rw [hv0 k hk hk']
        simp
    rw [hsumu] at hc
    linarith
  have hid1 := S.height_id i j
  have hid2 := S.height_id (j + 1) i
  rw [ea1, eb2] at hid1
  rw [ea2, eb1] at hid2
  have hσ1 : pz F G L i - pw F G L j = 1 := by
    have := pz_sub_pw (F := F) (G := G) L i
    linarith
  have hσ2 : pz F G L (j + 1) - pw F G L i = 1 := by
    have := pz_succ (F := F) (G := G) L j
    linarith
  rcases le_total (z x L) (z x' L) with hA | hA <;> rcases le_total (w x L) (w x' L) with hB | hB
  · rw [min_eq_left hA] at zt
    rw [min_eq_left hB] at wt
    linarith
  · rw [min_eq_left hA] at zt
    rw [min_eq_right hB] at wt
    exact corner_contra i j hi.le hj hσ1 (by linarith)
  · rw [min_eq_right hA] at zt
    rw [min_eq_left hB] at wt
    exact corner_contra (j + 1) i (by omega) hi hσ2 (by linarith)
  · rw [min_eq_right hA] at zt
    rw [min_eq_right hB] at wt
    linarith

end Setup

end LC

/-- Lemma C (T2). -/
theorem lemmaC_proof (n : ℕ) (τ : ℝ) (u : ℕ → ℝ) (z w : ℕ → ℕ → ℝ)
    (hτ : (n : ℝ) ^ 2 ≤ τ) (hu : Chamber n τ u)
    (hz : IsUltra n fun x y => (z x y : WithTop ℝ)) (hw : IsUltra n fun x y => (w x y : WithTop ℝ)) :
    ¬ ∃ r f g, IsCycle (topPairs n u z w) (node n fun x y => (z x y : WithTop ℝ))
      (node n fun x y => (w x y : WithTop ℝ)) r f g := by
  rintro ⟨r, f, g, hc⟩
  have hr : 0 < r := hc.pos
  have hmod : ∀ i, i % r < r := fun i => Nat.mod_lt _ hr
  have memF : ∀ i, f (i % r) ∈ topPairs n u z w := fun i => hc.mem_f _ (hmod i)
  have memG : ∀ i, g (i % r) ∈ topPairs n u z w := fun i => hc.mem_g _ (hmod i)
  have h0 := hc.mem_f 0 hr
  have hP : ∀ e, e ∈ topPairs n u z w →
      psiPair u z w e.1 e.2 = psiPair u z w (f 0).1 (f 0).2 := fun e he =>
    le_antisymm (h0.2.2 e.1 e.2 he.1 he.2.1) (he.2.2 _ _ h0.1 h0.2.1)
  have S : LC.Setup n u z w r (fun i => f (i % r)) (fun i => g (i % r))
      (psiPair u z w (f 0).1 (f 0).2) := by
    refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · exact fun i => ⟨(memF i).1, (memF i).2.1⟩
    · exact fun i => ⟨(memG i).1, (memG i).2.1⟩
    · exact fun i => hP _ (memF i)
    · exact fun i => hP _ (memG i)
    · exact fun a b hab hb => h0.2.2 a b hab hb
    · intro i
      exact LC.node_height_eq hw (lt_trans (memF i).1 (memF i).2.1) (memF i).2.1
        (lt_trans (memG i).1 (memG i).2.1) (memG i).2.1 (Nat.ne_of_lt (memF i).1)
        (Nat.ne_of_lt (memG i).1) (hc.adj_w _ (hmod i))
    · intro i
      have e : (i % r + 1) % r = (i + 1) % r := Nat.mod_add_mod i r 1
      have hadj := hc.adj_z _ (hmod i)
      rw [e] at hadj
      exact LC.node_height_eq hz (lt_trans (memG i).1 (memG i).2.1) (memG i).2.1
        (lt_trans (memF (i + 1)).1 (memF (i + 1)).2.1) (memF (i + 1)).2.1 (Nat.ne_of_lt (memG i).1)
        (Nat.ne_of_lt (memF (i + 1)).1) hadj
    · intro i j hi hj h
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
      exact hc.inj_f i j hi hj h
    · intro i j hi hj h
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
      exact hc.inj_g i j hi hj h
    · intro i j hi hj
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact hc.ne_fg i j hi hj
  exact S.contra hu hτ hz hw
