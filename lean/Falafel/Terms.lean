import PathStatement
import Falafel.Start

/-!
# The terms in closed form

`term R j` of `PathStatement.lean` is the spiral number of the square at index j of lap R. The
tables `rho` and `pi` below give the ring and the position on the ring of that square. They have
the same cases as `term`, and `term = (2 rho - 1)² + pi` case by case.
-/
namespace Falafel

-- The case analyses below are long: no time limit per theorem.
set_option maxHeartbeats 0

/-- The ring at place t of the way back of lap R. -/
def backRho (R t : ℤ) : ℤ :=
  if R % 2 = 0 then
    if t % 3 = 0 then 2 * R - 2 * (t / 3) else if t % 3 = 1 then 2 * R - 2 * (t / 3) - 1 else 2 * R - 2 * (t / 3)
  else if t % 3 = 0 then 2 * R - 2 * (t / 3) - 1 else if t % 3 = 1 then 2 * R - 2 * (t / 3) else 2 * R - 2 * (t / 3) - 1

/-- The ring of the square at index j of lap R. -/
def rho (R j : ℤ) : ℤ :=
  if j < 0 then
    if R % 2 = 0 then
      if j = -R - 1 then R else if j = -R then R + 1 else 2 * R + j
    else if j = -R - 3 then R + 2 else if j = -R - 2 then R + 3
    else if j = -R - 1 then R + 1 else 2 * R + j
  else if j < 2 * R - 4 then if j % 2 = 0 then 2 * R - 2 else 2 * R - 1
  else if j < 2 * R + 2 then
    if j = 2 * R - 4 then 2 * R - 3
    else if j = 2 * R - 3 then 2 * R - 2
    else if j = 2 * R - 2 then 2 * R - 2
    else if j = 2 * R - 1 then 2 * R - 1
    else if j = 2 * R then 2 * R - 2
    else 2 * R - 1
  else if j < 6 * R - 5 then if j % 2 = 0 then 2 * R else 2 * R - 1
  else if j < 6 * R + 1 then
    if j = 6 * R - 5 then 2 * R - 2
    else if j = 6 * R - 4 then 2 * R - 1
    else if j = 6 * R - 3 then 2 * R - 1
    else if j = 6 * R - 2 then 2 * R
    else if j = 6 * R - 1 then 2 * R - 1
    else 2 * R
  else if j < 10 * R - 4 then if j % 2 = 1 then 2 * R + 1 else 2 * R
  else if j < 10 * R + 2 then
    if j = 10 * R - 4 then 2 * R - 1
    else if j = 10 * R - 3 then 2 * R
    else if j = 10 * R - 2 then 2 * R
    else if j = 10 * R - 1 then 2 * R + 1
    else if j = 10 * R then 2 * R
    else 2 * R + 1
  else if j < 11 * R + 3 then if j % 2 = 0 then 2 * R + 2 else 2 * R + 1
  else backRho R (j - (11 * R + 3))

/-- The position on its ring at place t of the way back of lap R. -/
def backPi (R t : ℤ) : ℤ :=
  if R % 2 = 0 then
    if t % 3 = 0 then 3 * R - 6 * (t / 3) - 4 else if t % 3 = 1 then 3 * R - 6 * (t / 3) - 6 else 3 * R - 6 * (t / 3) - 6
  else if t % 3 = 0 then 3 * R - 6 * (t / 3) - 5 else if t % 3 = 1 then 3 * R - 6 * (t / 3) - 5 else 3 * R - 6 * (t / 3) - 7

/-- The position on its ring of the square at index j of lap R. -/
def pi (R j : ℤ) : ℤ :=
  if j < 0 then
    if R % 2 = 0 then
      if j = -R - 1 then 8 * R else if j = -R then 2 else 14 * R + 6 * j
    else if j = -R - 3 then 6 else if j = -R - 2 then 6
    else if j = -R - 1 then 2 else 14 * R + 6 * j
  else if j < 2 * R - 4 then if j % 2 = 0 then 14 * R - j - 14 else 14 * R - j - 7
  else if j < 2 * R + 2 then
    if j = 2 * R - 4 then 12 * R - 18
    else if j = 2 * R - 3 then 12 * R - 14
    else if j = 2 * R - 2 then 12 * R - 10
    else if j = 2 * R - 1 then 12 * R - 4
    else if j = 2 * R then 12 * R - 12
    else 12 * R - 8
  else if j < 6 * R - 5 then if j % 2 = 0 then 14 * R - j - 2 else 14 * R - j - 7
  else if j < 6 * R + 1 then
    if j = 6 * R - 5 then 8 * R - 8
    else if j = 6 * R - 4 then 8 * R - 6
    else if j = 6 * R - 3 then 8 * R - 2
    else if j = 6 * R - 2 then 8 * R + 2
    else if j = 6 * R - 1 then 8 * R - 4
    else 8 * R - 2
  else if j < 10 * R - 4 then if j % 2 = 1 then 14 * R - j + 1 else 14 * R - j - 2
  else if j < 10 * R + 2 then
    if j = 10 * R - 4 then 4 * R - 2
    else if j = 10 * R - 3 then 4 * R - 2
    else if j = 10 * R - 2 then 4 * R + 2
    else if j = 10 * R - 1 then 4 * R + 4
    else if j = 10 * R then 4 * R
    else 4 * R
  else if j < 11 * R + 3 then if j % 2 = 0 then 14 * R - j + 2 else 14 * R - j + 1
  else backPi R (j - (11 * R + 3))

theorem first_eq_lo (R : ℤ) : first R = lo R := rfl

/-- The term is the spiral number made from ring and position. One case per row of the table. -/
theorem term_eq (R j : ℤ) : term R j = (2 * rho R j - 1) ^ 2 + pi R j := by
  unfold term rho pi backTerm backRho backPi
  by_cases h : j < 0
  · simp only [ite_eq_left h]
    by_cases h : R % 2 = 0
    · simp only [ite_eq_left h]
      by_cases h : j = -R - 1
      · simp only [ite_eq_left h]
      · simp only [ite_eq_right h]
        by_cases h : j = -R
        · simp only [ite_eq_left h]
          grind
        · simp only [ite_eq_right h]
          grind
    · simp only [ite_eq_right h]
      by_cases h : j = -R - 3
      · simp only [ite_eq_left h]
        grind
      · simp only [ite_eq_right h]
        by_cases h : j = -R - 2
        · simp only [ite_eq_left h]
          grind
        · simp only [ite_eq_right h]
          by_cases h : j = -R - 1
          · simp only [ite_eq_left h]
            grind
          · simp only [ite_eq_right h]
            grind
  · simp only [ite_eq_right h]
    by_cases h : j < 2 * R - 4
    · simp only [ite_eq_left h]
      by_cases h : j % 2 = 0
      · simp only [ite_eq_left h]
        grind
      · simp only [ite_eq_right h]
        grind
    · simp only [ite_eq_right h]
      by_cases h : j < 2 * R + 2
      · simp only [ite_eq_left h]
        by_cases h : j = 2 * R - 4
        · simp only [ite_eq_left h]
          grind
        · simp only [ite_eq_right h]
          by_cases h : j = 2 * R - 3
          · simp only [ite_eq_left h]
            grind
          · simp only [ite_eq_right h]
            by_cases h : j = 2 * R - 2
            · simp only [ite_eq_left h]
              grind
            · simp only [ite_eq_right h]
              by_cases h : j = 2 * R - 1
              · simp only [ite_eq_left h]
                grind
              · simp only [ite_eq_right h]
                by_cases h : j = 2 * R
                · simp only [ite_eq_left h]
                  grind
                · simp only [ite_eq_right h]
                  grind
      · simp only [ite_eq_right h]
        by_cases h : j < 6 * R - 5
        · simp only [ite_eq_left h]
          by_cases h : j % 2 = 0
          · simp only [ite_eq_left h]
            grind
          · simp only [ite_eq_right h]
            grind
        · simp only [ite_eq_right h]
          by_cases h : j < 6 * R + 1
          · simp only [ite_eq_left h]
            by_cases h : j = 6 * R - 5
            · simp only [ite_eq_left h]
              grind
            · simp only [ite_eq_right h]
              by_cases h : j = 6 * R - 4
              · simp only [ite_eq_left h]
                grind
              · simp only [ite_eq_right h]
                by_cases h : j = 6 * R - 3
                · simp only [ite_eq_left h]
                  grind
                · simp only [ite_eq_right h]
                  by_cases h : j = 6 * R - 2
                  · simp only [ite_eq_left h]
                    grind
                  · simp only [ite_eq_right h]
                    by_cases h : j = 6 * R - 1
                    · simp only [ite_eq_left h]
                      grind
                    · simp only [ite_eq_right h]
                      grind
          · simp only [ite_eq_right h]
            by_cases h : j < 10 * R - 4
            · simp only [ite_eq_left h]
              by_cases h : j % 2 = 1
              · simp only [ite_eq_left h]
                grind
              · simp only [ite_eq_right h]
                grind
            · simp only [ite_eq_right h]
              by_cases h : j < 10 * R + 2
              · simp only [ite_eq_left h]
                by_cases h : j = 10 * R - 4
                · simp only [ite_eq_left h]
                  grind
                · simp only [ite_eq_right h]
                  by_cases h : j = 10 * R - 3
                  · simp only [ite_eq_left h]
                    grind
                  · simp only [ite_eq_right h]
                    by_cases h : j = 10 * R - 2
                    · simp only [ite_eq_left h]
                      grind
                    · simp only [ite_eq_right h]
                      by_cases h : j = 10 * R - 1
                      · simp only [ite_eq_left h]
                        grind
                      · simp only [ite_eq_right h]
                        by_cases h : j = 10 * R
                        · simp only [ite_eq_left h]
                          grind
                        · simp only [ite_eq_right h]
                          grind
              · simp only [ite_eq_right h]
                by_cases h : j < 11 * R + 3
                · simp only [ite_eq_left h]
                  by_cases h : j % 2 = 0
                  · simp only [ite_eq_left h]
                    grind
                  · simp only [ite_eq_right h]
                    grind
                · simp only [ite_eq_right h]
                  by_cases h : R % 2 = 0
                  · simp only [ite_eq_left h]
                    by_cases h : (j - (11 * R + 3)) % 3 = 0
                    · simp only [ite_eq_left h]
                      grind
                    · simp only [ite_eq_right h]
                      by_cases h : (j - (11 * R + 3)) % 3 = 1
                      · simp only [ite_eq_left h]
                        grind
                      · simp only [ite_eq_right h]
                        grind
                  · simp only [ite_eq_right h]
                    by_cases h : (j - (11 * R + 3)) % 3 = 0
                    · simp only [ite_eq_left h]
                      grind
                    · simp only [ite_eq_right h]
                      by_cases h : (j - (11 * R + 3)) % 3 = 1
                      · simp only [ite_eq_left h]
                        grind
                      · simp only [ite_eq_right h]
                        grind

theorem ring_rpos_core (R j u v a b : ℤ) (hR : 4 ≤ R) (h1 : lo R ≤ j) (h2 : j < hi R) :
    squ R j = u → sqv R j = v → rho R j = a → pi R j = b → ring u v = a ∧ rpos u v = b := by
  unfold lo at h1
  unfold hi at h2
  unfold squ
  split_cases
  all_goals (intro hu; subst hu; unfold sqv; split_cases)
  all_goals (intro hv; subst hv; unfold rho backRho; split_cases)
  all_goals (intro ha; subst ha; unfold pi backPi; split_cases)
  all_goals (intro hb; subst hb; unfold ring rpos; split_omega)

/-- The spiral number of the square at index j of lap R. -/
theorem spiral_path (R j : ℤ) (hR : 4 ≤ R) (h1 : lo R ≤ j) (h2 : j < hi R) :
    spiral (squ R j + sqv R j, squ R j - sqv R j) = term R j := by
  obtain ⟨e1, e2⟩ := ring_rpos_core R j _ _ _ _ hR h1 h2 rfl rfl rfl rfl
  rw [spiral_uv, e1, e2, term_eq]

/-- **Corollary 9. The terms from step 80 on.** -/
theorem term_formula : TermFormula := by
  intro a ha R hR n h1 h2
  obtain rfl := walk_unique a ha
  have hw := walk_eq_path R hR n h1 h2
  have hs := start_succ R
  unfold walk
  rw [hw, first_eq_lo]
  exact spiral_path R _ hR (by omega) (by omega)

end Falafel
