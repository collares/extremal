import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

def Real.descFactorial (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (x - k) * descFactorial x k

@[simp]
theorem Real.descFactorial_eq_zero_iff_lt {n : ℕ} {k : ℕ} :
    (n : ℝ).descFactorial k = 0 ↔ n < k := by
  induction k with
  | zero => simp [Real.descFactorial]
  | succ k hind =>
      rw [descFactorial, mul_eq_zero]
      constructor
      · rintro (h | h)
        · have : (n : ℝ) = (k : ℝ) := eq_of_sub_eq_zero h
          rw [Nat.cast_inj] at this
          omega
        linarith [hind.1 h]
      · intro h
        obtain rfl | hn := eq_or_ne n k
        · simp
        · have : n < k := Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one h) hn
          exact (Or.inr <| hind.2 this)

theorem Real.descFactorial_sub_one_eq_zero {k : ℕ} (hk : 0 < k) :
    (k - 1 : ℝ).descFactorial k = 0 := by
  convert Real.descFactorial_eq_zero_iff_lt.2 (Nat.sub_one_lt_of_lt hk)
  exact (Nat.cast_pred hk).symm

theorem real_descFactorial_eq_descFactorial_of_le {n k : ℕ} (h : k ≤ n) :
    (n : ℝ).descFactorial k = n.descFactorial k := by
  induction k with
  | zero => simp [Real.descFactorial]
  | succ k hind =>
     have nkle : k ≤ n := by omega
     rw [Nat.descFactorial, Real.descFactorial, hind nkle, Nat.cast_mul,
       mul_eq_mul_right_iff, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
     exact Or.inl (by norm_cast)

theorem monotoneOn_descFactorial {k : ℕ} : MonotoneOn (Real.descFactorial · k) (Set.Ici (k-1 : ℝ)) := by
  induction k with
  | zero => simp_rw [Real.descFactorial]; exact monotoneOn_const
  | succ k ih =>
    simp only [Real.descFactorial, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    apply monotoneOn_iff_forall_lt.2
    intro a ha b hb hab
    simp_rw [Set.mem_Ici] at ha hb
    have : a.descFactorial k ≤ b.descFactorial k :=
      ih (by simp_rw [Set.mem_Ici]; linarith) (by simp_rw [Set.mem_Ici]; linarith) hab.le
    have : 0 ≤ a.descFactorial k := by
      rcases k.eq_zero_or_pos with rfl|hk
      · simp [Real.descFactorial]
      · have := ih Set.left_mem_Ici (show a ∈ Set.Ici (k - 1 : ℝ) by simp_rw [Set.mem_Ici]; linarith) (by linarith)
        simpa [Real.descFactorial_sub_one_eq_zero hk] using this
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

theorem descFactorial_nonneg {x : ℝ} {k : ℕ} (hx : k-1 ≤ x) : 0 ≤ x.descFactorial k := by
  rcases k.eq_zero_or_pos with rfl|hk
  · simp [Real.descFactorial]
  · rw [← Real.descFactorial_sub_one_eq_zero hk]
    simpa using monotoneOn_descFactorial Set.left_mem_Ici hx hx

theorem Real.descFactorial_le {x : ℝ} {k : ℕ} (hx : k-1 ≤ x) :
    x.descFactorial k ≤ x ^ k := by
  induction k with
  | zero => rw [Real.descFactorial]; rfl
  | succ k ih =>
     simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hx
     simp only [Real.descFactorial, pow_succ']
     gcongr
     · exact descFactorial_nonneg (by linarith)
     · linarith
     · linarith
     · simp_rw [ih (by linarith)]

theorem Real.le_descFactorial {x : ℝ} {k : ℕ} (hx : k-1 ≤ x) :
    (x - (k - 1))^k ≤ x.descFactorial k := by
  induction k with
  | zero => rw [Real.descFactorial]; rfl
  | succ k ih =>
     simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hx ⊢
     simp only [Real.descFactorial, pow_succ']
     gcongr
     · simp only [sub_nonneg, hx]
     · have lower : (x - k) ^ k ≤ (x - (k - 1))^k := by gcongr <;> linarith
       exact lower.trans (ih (by linarith))

theorem convexOn_descFactorial (k : ℕ) : ConvexOn ℝ (Set.Ici (k-1 : ℝ)) (Real.descFactorial · k) := by
  induction k with
  | zero => simp_rw [Real.descFactorial]; exact convexOn_const 1 (convex_Ici _)
  | succ k ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.descFactorial, ←smul_eq_mul]
    convert_to ConvexOn _ _ ((fun (x : ℝ) => (x - ↑k)) • (fun (x : ℝ) => x.descFactorial k))
    refine ConvexOn.smul' ?_ ?_ (by simp) ?_ ?_
    · exact (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn convex_univ).translate_left _).subset
       (fun _ _ => trivial) (convex_Ici _)
    · exact ih.subset (Set.Ici_subset_Ici.mpr (by linarith)) (convex_Ici _)
    · simp_rw [Set.mem_Ici]; intro x hx; exact descFactorial_nonneg (by linarith)
    · refine MonotoneOn.monovaryOn (monotoneOn_id.add_const (-k : ℝ)) (monotoneOn_descFactorial.mono ?_)
      exact Set.Ici_subset_Ici.2 (by linarith)

noncomputable def Real.choose (x : ℝ) (k : ℕ) := Real.descFactorial x k / Nat.factorial k

theorem Real.choose_one_right (x : ℝ) : choose x 1 = x := by
  simp [Real.choose, Real.descFactorial]

theorem Real.choose_two_right (x : ℝ) : choose x 2 = x * (x - 1) / 2 := by
  simp [Real.choose, Real.descFactorial, mul_comm]

theorem Real.choose_sub_one_eq_zero {k : ℕ} (hk : 0 < k) :
    (k - 1 : ℝ).choose k = 0 := by
  simp [Real.choose]
  exact Or.inl <| Real.descFactorial_sub_one_eq_zero hk

theorem realChoose_eq_choose (n k : ℕ) : (n : ℝ).choose k = n.choose k := by
  rw [Nat.choose_eq_descFactorial_div_factorial, Real.choose]
  field_simp [k.factorial_ne_zero, Nat.factorial_dvd_descFactorial]
  by_cases hnk : n < k
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hnk, Real.descFactorial_eq_zero_iff_lt.2 hnk]
    norm_cast
  · rw [not_lt] at hnk
    exact real_descFactorial_eq_descFactorial_of_le hnk

theorem realChoose_nonneg {x : ℝ} {k : ℕ} (hx : k-1 ≤ x) : 0 ≤ x.choose k := by
  simp_rw [Real.choose]
  exact div_nonneg (descFactorial_nonneg hx) (Nat.cast_nonneg _)

theorem convexOn_realChoose (k : ℕ) : ConvexOn ℝ (Set.Ici (k-1 : ℝ)) (Real.choose · k) := by
  simp_rw [Real.choose, div_eq_mul_inv, mul_comm]
  exact ConvexOn.smul (inv_nonneg_of_nonneg <| Nat.cast_nonneg _) <| convexOn_descFactorial k

-- maybe the definition should have been k-1 < x, to make
-- truncChoose_eq_zero_of_lt provable when k = 0. but it doesn't matter much.
noncomputable def Real.truncChoose (x : ℝ) (k : ℕ) :=
  if k-1 ≤ x then Real.choose x k else 0

theorem truncChoose_eq_zero_of_lt {x : ℝ} {k : ℕ} (hk : 0 < k) (hxk : x ≤ k-1)
    : x.truncChoose k = 0 := by
  rcases hxk.eq_or_lt with rfl | h
  · simp [Real.truncChoose, Real.choose_sub_one_eq_zero hk]
  · simp [Real.truncChoose]; intro; linarith

theorem truncChoose_nonneg {x : ℝ} {k : ℕ} : 0 ≤ x.truncChoose k := by
  simp_rw [Real.truncChoose]
  rcases lt_or_ge (x) (k - 1 : ℝ) with hxk | hxk
    <;> simp [not_le_of_lt, hxk, realChoose_nonneg]

theorem truncChoose_eq_realChoose_of_nat_or_gt {x : ℝ} {k : ℕ} :
    (k-1 ≤ x ∨ ∃ n : ℕ, x = n) → x.truncChoose k = x.choose k := by
  field_simp [Real.truncChoose, Real.choose]
  rintro (hkx | ⟨n, rfl⟩) h
  · linarith -- contradiction
  · refine (Real.descFactorial_eq_zero_iff_lt.2 <| Nat.lt_of_succ_lt ?_).symm
    exact_mod_cast h

-- we only use the ← direction in our proof of Kovari-Sos-Turan, but the →
-- version (currently sorried out) might be worth proving too. it follows from
-- the fact that Real.choose x k has at most k zeros since it is a polynomial
-- of degree k and the fact that 0, ..., k-1 are zeros of x.choose k (as proved
-- by the ← direction and Real.descFactorial_eq_zero_iff_lt).
--
-- theorem truncChoose_eq_realChoose_iff {x : ℝ} {k : ℕ} (hk : 0 < k) :
--     x.truncChoose k = x.choose k ↔ (k-1 ≤ x ∨ ∃ n : ℕ, x = n) := by
--   refine ⟨fun heq => ?_, truncChoose_eq_realChoose_of_nat_or_gt⟩
--   admit

theorem convexOn_truncChoose {k : ℕ} (hk : 0 < k) : ConvexOn ℝ Set.univ (Real.truncChoose · k) := by
  apply convexOn_iff_slope_mono_adjacent.2
  simp only [Set.mem_univ, true_implies]
  refine ⟨convex_univ, fun x y z hxy hyz => ?_⟩
  rcases le_or_gt (k-1 : ℝ) x with hxk | hxk
  · have hyk : k-1 ≤ y := by linarith
    have hzk : k-1 ≤ z := by linarith
    simp only [truncChoose_eq_realChoose_of_nat_or_gt (Or.inl hxk),
               truncChoose_eq_realChoose_of_nat_or_gt (Or.inl hyk),
               truncChoose_eq_realChoose_of_nat_or_gt (Or.inl hzk)]
    simpa only [Set.mem_Ici] using
      (convexOn_iff_slope_mono_adjacent.1 <| convexOn_realChoose k).2 hxk hzk hxy hyz
  simp only [truncChoose_eq_zero_of_lt hk hxk.le, sub_zero, ge_iff_le]
  rcases lt_or_ge z (k-1 : ℝ) with hzk | hzk
  · have hyk : ¬(k ≤ y+1) := by linarith
    have hzk : ¬(k ≤ z+1) := by linarith
    simp [Real.truncChoose, hyk, hzk]
  rcases le_or_gt y (k - 1 : ℝ) with hyk | hyk
  · simp only [truncChoose_eq_zero_of_lt hk hyk, zero_div, sub_zero, ge_iff_le]
    exact div_nonneg (truncChoose_nonneg) (by linarith)
  simp only [truncChoose_eq_realChoose_of_nat_or_gt (Or.inl hyk.le),
             truncChoose_eq_realChoose_of_nat_or_gt (Or.inl hzk)]
  have := (convexOn_iff_slope_mono_adjacent.1 <| convexOn_realChoose k).2 (Set.left_mem_Ici) hzk hyk hyz
  simp only [Real.choose_sub_one_eq_zero hk, sub_zero] at this
  refine trans ?_ this
  exact div_le_div_of_nonneg_left (realChoose_nonneg hyk.le) (show 0 < y - (k-1 : ℝ) by linarith) (by linarith)

namespace SimpleGraph

def Copy {α β : Type*} (H : SimpleGraph β) (G : SimpleGraph α) :=
  { H' : Subgraph G // Nonempty (H'.coe ≃g H) }

def IsContained (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ f : H →g G, Function.Injective f

scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

-- IsContained.trans comes from LeanCamCombi
lemma IsContained.trans : G ⊑ H → H ⊑ I → G ⊑ I := fun ⟨f, hf⟩ ⟨g, hg⟩ ↦ ⟨g.comp f, hg.comp hf⟩

def Kst (s t : ℕ) : SimpleGraph (Sum (Fin s) (Fin t)) :=
  completeBipartiteGraph (Fin s) (Fin t)

variable {α : Type*} [DecidableEq α] (G : SimpleGraph α)

lemma copy_Kst_iff (s t : ℕ) :
    Kst s t ⊑ G ↔ ∃ (S : Finset α) (T : Finset α), S.card = s ∧ T.card = t ∧ (∀ v ∈ S, ∀ w ∈ T, G.Adj v w) := by
  constructor
  · intro hKst
    rw [IsContained] at hKst
    obtain ⟨f, fInj⟩ := hKst
    use Finset.image (f ∘ Sum.inl) ⊤, Finset.image (f ∘ Sum.inr) ⊤
    refine ⟨?_, ?_, ?_⟩
    · simp [fInj, Sum.inl_injective, Finset.card_image_of_injective]
    · simp [fInj, Sum.inr_injective, Finset.card_image_of_injective]
    · intro v hv w hw
      obtain ⟨v', hv'⟩ := Finset.mem_image.1 hv
      obtain ⟨w', hw'⟩ := Finset.mem_image.1 hw
      rw [← hw'.2, ← hv'.2]
      apply f.map_rel'
      simp [Kst]
  · intro hST
    obtain ⟨S, T, hST'⟩ := hST
    have disjST : Disjoint S T := by
      by_contra! hd
      rw [Finset.not_disjoint_iff] at hd
      obtain ⟨a, ha⟩ := hd
      exact G.loopless a (hST'.2.2 a ha.1 a ha.2)

    rw [Kst]
    let hS : Fin s ≃ S := (finCongr hST'.1.symm).trans S.equivFin.symm
    let hT : Fin t ≃ T := (finCongr hST'.2.1.symm).trans T.equivFin.symm

    let fn : (Fin s) ⊕ (Fin t) → α := fun | Sum.inl v => hS v | Sum.inr w => hT w
    have fninj : Function.Injective fn := by
      simp_rw [fn]
      intro a₁ a₂
      cases' a₁ with b₁ <;> cases' a₂ with b₂ <;> simp only [reduceCtorEq, imp_false]
      rotate_left
      · have : ∀ a b, (hS a).val ≠ (hT b).val := fun a b =>
          Finset.disjoint_iff_ne.1 disjST _ (hS a).property _ (hT b).property
        simp_rw [this, not_false_eq_true]
      · have : ∀ a b, (hT a).val ≠ (hS b).val := fun a b =>
          Finset.disjoint_iff_ne.1 disjST.symm _ (hT a).property _ (hS b).property
        simp_rw [this, not_false_eq_true]
      all_goals
        simp only [Sum.inl.injEq, Sum.inr.injEq]
        apply (Equiv.injective_comp _ _).2
        exact Subtype.val_injective

    let f : completeBipartiteGraph (Fin s) (Fin t) →g G := {
      toFun := fn
      map_rel' := fun {a b} rel => by
        cases a <;> cases b
        · simp at rel
        · simp [fn, hST']
        · symm; simp [fn, hST']
        · simp at rel
    }
    exact ⟨f, fninj⟩

variable [Fintype α] [DecidableRel G.Adj]

def commonNeighbors' (T : Finset α) : Finset α :=
  T.inf (G.neighborFinset ·)

lemma subset_neighborFinset_iff_mem_commonNeighbors' (T : Finset α) (v : α) :
    T ⊆ G.neighborFinset v ↔ v ∈ commonNeighbors' G T := by
  simp_rw [← Finset.singleton_subset_iff, ← Finset.le_eq_subset, commonNeighbors', Finset.le_inf_iff]
  constructor
  · intro h t hT
    simp_rw [Finset.le_eq_subset, Finset.singleton_subset_iff, mem_neighborFinset]
    symm
    simpa using h hT
  · intro h t hT
    rw [mem_neighborFinset]
    symm
    simpa using h t hT

lemma subset_commonNeighbors' (S T : Finset α) :
    S ⊆ G.commonNeighbors' T → T ⊆ G.commonNeighbors' S := by
  simp_rw [commonNeighbors', ← Finset.le_eq_subset, Finset.le_inf_iff, Finset.le_eq_subset, Finset.subset_iff, mem_neighborFinset]
  intro h x xS y yT
  exact adj_symm _ (h y yT xS)

lemma adj_of_mem_commonNeighbors' (T : Finset α) (v w : α)
    (hv : v ∈ commonNeighbors' G T) (hw : w ∈ T) : G.Adj v w := by
  simpa using (subset_neighborFinset_iff_mem_commonNeighbors' G T v).2 hv hw

lemma copy_Kst_commonNeighbors' (T : Finset α) :
    Kst (commonNeighbors' G T).card T.card ⊑ G := by
  apply (copy_Kst_iff G (commonNeighbors' G T).card T.card).2
  use (commonNeighbors' G T), T
  simp_rw [true_and]
  intro v hv w hw
  exact adj_of_mem_commonNeighbors' G T v w hv hw

lemma Kst_mono {s₁ t₁ s₂ t₂ : ℕ} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : Kst s₁ t₁ ⊑ Kst s₂ t₂ :=
  let emb := Function.Embedding.sumMap (Fin.castLEEmb hs) (Fin.castLEEmb ht)
  ⟨⟨emb, by aesop_graph⟩, emb.injective⟩

-- note that the currently-stated theorem RHS might be too strong at the
-- moment, and we should replace it by whatever comes out of proving the "have
-- absurd" part.
set_option maxHeartbeats 400000 in
theorem KovariSosTuran (h : ¬ (Kst s t) ⊑ G) (hs : 2 ≤ t) (ht : t ≤ s) :
    (G.edgeFinset.card : ℝ) ≤ (s - 1 : ℝ) ^ (1 / t : ℝ) / 2 * (Fintype.card α) ^ (2 - 1 / t : ℝ) + (t - 1) / 2 * (Fintype.card α) := by
  rw [← Nat.cast_pred (show 1 ≤ s by omega)]
  let s1 := ((s - 1 : ℕ) : ℝ)
  by_contra! hEdgeCard

  set n := Fintype.card α
  set m := G.edgeFinset.card

  have tpos : 0 ≤ (t - 1 : ℝ) := by simp only [sub_nonneg, Nat.one_le_cast]; omega
  have hEdgeCardWeak : s1 ^ (1 / t : ℝ) / 2 * (n : ℝ) ^ (2 - 1 / t : ℝ) < (m : ℝ) :=
    lt_of_add_lt_of_nonneg_left hEdgeCard (by positivity)

  have : 1 ≤ s1 ^ (1 / t : ℝ) := by
    refine Real.one_le_rpow ?_ (by positivity)
    simpa [s1] using (show 1 ≤ s - 1 by omega)
  have npos : 1 ≤ (n : ℝ) := by
    obtain hn | hn := n.eq_zero_or_pos
    · have nedges : (m : ℝ) = 0 := by
        rw [Nat.cast_eq_zero, ← nonpos_iff_eq_zero, ← Nat.choose_zero_succ 1, ← hn]
        simpa [m] using G.card_edgeFinset_le_card_choose_two
      have : 0 ≤ s1 ^ (1 / t : ℝ) / 2 * (n : ℝ) ^ (2 - 1 / t : ℝ) + (t - 1) / 2 * n := by positivity
      linarith
    · exact_mod_cast hn

  have npos' : 0 < (n : ℝ) := by linarith

  let f : ℝ → ℝ := (·.choose t)
  let cherries := Finset.sigma ⊤ (Finset.powersetCard t <| G.neighborFinset ·)
  let Ts := Finset.powersetCard t (Finset.univ : Finset α)

  have : 1 ≤ t := by linarith

  have h₀ : Ts.card = f n := by
    have : Ts.card = n.choose t := by rw [Finset.card_powersetCard]; simp
    simpa [f, realChoose_eq_choose] using this

  have h₁ : cherries.card ≤ f n * s1 := by
    dsimp only [s1]
    rw [Nat.cast_pred (show 1 ≤ s by omega)]

    by_contra! h
    rw [← h₀] at h

    have h : Ts.card * (s - 1) < cherries.card := by
      rw [← Nat.cast_pred (show 1 ≤ s by omega)] at h
      norm_cast at h

    let forgetCenter : cherries → Ts :=
      fun ⟨⟨v, T⟩, hvT⟩ => ⟨T, by {
        rw [Finset.mem_powersetCard]
        simp only [Finset.top_eq_univ, Finset.mem_sigma, Finset.mem_univ, Finset.mem_powersetCard,
          true_and, Finset.subset_univ, cherries] at hvT ⊢
        exact hvT.2 }⟩

    have hcn : ∀ T, ∀ (hT : T ∈ Ts), ∀ ch ∈ Finset.univ.filter (forgetCenter · = ⟨T, hT⟩),
        ch.1.1 ∈ G.commonNeighbors' T := by
      intro T hT ch hch
      obtain ⟨⟨v, T'⟩, hvT'⟩ := ch
      simp only [Finset.top_eq_univ, Finset.mem_sigma, Finset.mem_univ, Finset.mem_powersetCard,
        true_and, cherries] at hvT'
      simp only [Subtype.mk.injEq, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
        true_and, forgetCenter] at hch
      obtain rfl := hch
      simpa using (subset_neighborFinset_iff_mem_commonNeighbors' G T' v).1 hvT'.1

    simp_rw [← Fintype.card_coe] at h
    obtain ⟨⟨T, hT⟩, hST⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card forgetCenter h
    set cherriesT := Finset.univ.filter (forgetCenter · = ⟨T, hT⟩)

    let center : cherriesT ↪ α := {
      toFun := fun x => x.1.1.1 -- almost an IP address
      inj' := by { intro; aesop }
    }

    set S := cherriesT.attach.map center
    have Ssub : S ⊆ G.commonNeighbors' T := by
      -- this is such a mess :/
      intro x hx
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Sigma.exists, S] at hx
      obtain ⟨v, T', hT', ch, hQ⟩ := hx
      simp only [Function.Embedding.coeFn_mk, center] at hQ
      obtain rfl := hQ
      have ch2 := ch
      simp only [Subtype.mk.injEq, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
        true_and, cherriesT, forgetCenter] at ch
      obtain rfl := ch
      exact hcn T' hT ⟨⟨v, T'⟩, hT'⟩ ch2

    have Scard : s ≤ S.card := by simp [S, Finset.card_map]; omega
    have : s ≤ (commonNeighbors' G T).card := Scard.trans (Finset.card_le_card Ssub)

    have hcopy : Kst (G.commonNeighbors' T).card T.card ⊑ G := copy_Kst_commonNeighbors' G T
    have : T.card = t := by simpa [Ts] using hT
    have : Kst s t ⊑ G := (Kst_mono (by omega) (by omega)).trans hcopy

    contradiction

  have h₂ : cherries.card = ∑ v : α, f (G.degree v) := by
    simp [cherries, f, realChoose_eq_choose]

  have hsn : s ≤ n := by
    by_contra! h
    have : n ≤ s1 := by simp only [Nat.cast_le, s1]; omega
    simp only [Nat.pred_eq_pred, Nat.pred_eq_sub_one] at this
    have b₁ : n ^ 2 / 2 < m := by
      exact_mod_cast calc ((n ^ 2 / 2 : ℕ) : ℝ)
                 _ ≤ n ^ 2 / 2 := by exact_mod_cast Nat.cast_div_le
                 _ = n ^ (1 / t : ℝ) * n ^ (2 - 1 / t : ℝ) / 2 := by rw [←Real.rpow_add npos']; simp
                 _ ≤ s1 ^ (1 / t : ℝ) * n ^ (2 - 1 / t : ℝ) / 2 := by gcongr
                 _ ≤ s1 ^ (1 / t : ℝ) / 2 * n ^ (2 - 1 / t : ℝ) := by linarith
                 _ < m := by linarith only [hEdgeCardWeak]
    have (x : ℝ) (_ : 0 ≤ x) : x * (x-1) ≤ x^2 := by linarith
    have b₂ : m ≤ n^2 / 2 := calc
      m ≤ n.choose 2 := by exact_mod_cast card_edgeFinset_le_card_choose_two
                      _ ≤ n*(n-1)/2 := by rw [Nat.choose_two_right];
                      _ ≤ n*n / 2 := by gcongr; exact Nat.sub_le n 1
                      _ = n^2 / 2 := by simp only [pow_two]
    exact Nat.lt_irrefl _ (b₁.trans_le b₂)

  have tpos : 0 < (t - 1 : ℝ) := by exact_mod_cast (by omega)
  have hEdgeCard' : t-1 < (2 * m / n : ℝ) := by
    calc (t-1 : ℝ) = (t-1)^1 := by exact_mod_cast (pow_one _).symm
                  _ = (t-1) ^ (1 / t : ℝ) * (t-1) ^ (1 - 1 / t : ℝ) := by rw [←Real.rpow_add tpos]; simp
                  _ ≤ s1 ^ (1 / t : ℝ) * n ^ (1 - 1 / t : ℝ) := ?_
                  _ = s1 ^ (1 / t : ℝ) * n ^ (2 - 1 / t : ℝ) / n ^ (1 : ℝ) := by { rw [mul_div_assoc, ←Real.rpow_sub npos']; congr 2; linarith }
                  _ < 2 * m / n := by { rw [Real.rpow_one]; exact div_lt_div_of_pos_right (by linarith) npos' }
    · gcongr <;> norm_cast
      · simp only [s1]; norm_cast; omega
      · field_simp; exact div_nonneg tpos.le (Nat.cast_nonneg' t)
      · omega

  -- Instead of using Jensen (convexity on ℝ), an alternative which bypasses
  -- truncChoose is to prove a discrete inequality stating that, for a fixed
  -- x_1 + ... + x_2, ∑ x_i.choose t is minimised when the x_is are as close to
  -- equal as possible.
  have h₃ : n * f (2 * m / n) ≤ ∑ v : α, f (G.degree v) := by
     let f' : ℝ → ℝ := fun x => x.truncChoose t

     have ht : 0 < t := by omega
     have trunc₀ : f (2 * m / n) = f' (2 * m / n) := by
       simp_rw [f, ← truncChoose_eq_realChoose_of_nat_or_gt (Or.inl hEdgeCard'.le)]
     have trunc₁ (n : ℕ) : f n = f' n := by
       simp_rw [f, ← truncChoose_eq_realChoose_of_nat_or_gt (Or.inr (exists_apply_eq_apply' Nat.cast n))]
     have trunc₂ : ∑ v : α, f (G.degree v) = ∑ v : α, f' (G.degree v) := by simp [trunc₁]

     rw [trunc₀, trunc₂]
     calc n * f' (2 * m / n)
          _ = n * f' ((1/n) * (2 * m)) := by field_simp
          _ = n * f' ((1/n) * ∑ v : α, G.degree v) := by simp [m, SimpleGraph.sum_degrees_eq_twice_card_edges]
          _ = n * f' (∑ v : α, (1/n) * G.degree v) := by congr; rw [Nat.cast_sum]; exact (Finset.mul_sum _ _ (1/n : ℝ))
          _ ≤ n * ∑ v : α, (1/n) * f' (G.degree v) := ?_
          _ = n * ((1/n) * ∑ v : α, f' (G.degree v)) := by congr; exact (Finset.mul_sum _ _ (1/n : ℝ)).symm
          _ = ∑ v : α, f' (G.degree v) := by field_simp [npos]
     · gcongr
       exact (convexOn_truncChoose ht : ConvexOn ℝ (Set.univ : Set ℝ) _).map_sum_le
         (w := fun _ => (1/n : ℝ)) (by simp) (by field_simp [n, npos]) (by simp)

  rw [← h₂] at h₃
  field_simp only [f, Real.choose] at h₃ h₁
  apply (div_le_div_right <| by exact_mod_cast Nat.factorial_pos _).1 ∘ (·.trans h₁) at h₃

  have absurd : (m : ℝ) ≤ s1 ^ (1 / t : ℝ) / 2 * n ^ (2 - 1 / t : ℝ) + (t - 1) / 2 * n := by
    have : (0 : ℝ) ≤ (2 * m - n * (t - 1)) / n := by
      rw [sub_div, mul_div_cancel_left₀] <;> linarith

    have step₁ := calc
       n * ((2 * m - n * (t - 1) : ℝ) / n) ^ (t : ℝ)
       _ = n * (2 * m / n - (t - 1) : ℝ) ^ (t : ℝ) := by rw [div_sub' _ _ _ npos'.ne.symm]
       _ ≤ n * (2 * m / n : ℝ).descFactorial t := by gcongr; exact_mod_cast Real.le_descFactorial hEdgeCard'.le
       _ ≤ Real.descFactorial n t * s1 := h₃
       _ ≤ (n : ℝ)^(t : ℝ) * s1 := by gcongr; exact_mod_cast @Real.descFactorial_le n t (by norm_cast; omega)

    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (show (0 : ℝ) < 1/t by positivity)).2 at step₁
    rw [one_div, Real.mul_rpow, Real.rpow_rpow_inv, Real.mul_rpow, Real.rpow_rpow_inv,
        ←le_div_iff₀', div_le_iff₀', tsub_le_iff_right, ←le_div_iff₀'] at step₁ <;> try positivity
    rw [Real.rpow_sub npos', Real.rpow_two]
    convert step₁ using 1
    ring_nf

  linarith only [hEdgeCard, absurd]

#print axioms KovariSosTuran
