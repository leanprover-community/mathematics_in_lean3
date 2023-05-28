import analysis.normed_space.banach_steinhaus
import analysis.normed_space.finite_dimension

import analysis.calculus.inverse

open set filter
open_locale topology filter

noncomputable theory

section
variables
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

open metric

example {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
  (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
  ∃ C', ∀ i, ‖g i‖ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n` -/
  let e : ℕ → set E := λ n, ⋂ i : ι, { x : E | ‖g i x‖ ≤ n },
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n),
  from λ i, is_closed_Inter (λ i, is_closed_le (g i).cont.norm continuous_const),
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = univ,
  { refine eq_univ_of_forall (λ x, _),
    cases h x with C hC,
    obtain ⟨m, hm⟩ := exists_nat_ge C,
    exact ⟨e m, mem_range_self m, mem_Inter.mpr (λ i, le_trans (hC i) hm)⟩ },
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
     `e m` contains some `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_Union_of_closed hc hU,
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := is_open_iff.mp is_open_interior x hx,
  obtain ⟨k : 𝕜, hk : 1 < ‖k‖⟩ := normed_field.exists_one_lt_norm 𝕜,
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ (z ∈ ball x ε) (i : ι), ‖g i z‖ ≤ m,
  { intros z hz i,
    replace hz := mem_Inter.mp (interior_Inter_subset _ (hε hz)) i,
    apply interior_subset hz },
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk),
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
  { exact div_nonneg (nat.cast_nonneg _) εk_pos.le },
  intros y le_y y_lt,
  calc ‖g i y‖
      = ‖g i (y + x) - g i x‖   : by rw [(g i).map_add, add_sub_cancel]
  ... ≤ ‖g i (y + x)‖ + ‖g i x‖ : norm_sub_le _ _
  ... ≤ m + m : add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
          (real_norm_le x (mem_ball_self ε_pos) i)
  ... = (m + m : ℕ) : by norm_cast
  ... ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖))
      : le_mul_of_one_le_right (nat.cast_nonneg _)
          ((one_le_div $ div_pos ε_pos (zero_lt_one.trans hk)).2 le_y)
  ... = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ : (mul_comm_div _ _ _).symm,
end

end

