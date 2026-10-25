import CatalanAnchor.EulerFixedPoint
import CatalanAnchor.Certificate1000

/-!
Kernel replay of the fixed-point recurrence at 1012 decimal places and 4048
terms. Every arithmetic assertion is checked by the ordinary Lean kernel.
The resulting strict endpoint margins are used by the analytic enclosure.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 5000

namespace CatalanAnchor.EulerComputed

open EulerFixedPoint

def workScale : ℕ := 10 ^ 1012
def terms : ℕ := 4048
def sumValue : ℕ := 9159655941772190150546035149323841107741493742816721342664981196217630197762547694793565129261151062485744226191961995790358988033258590594315947374811584069953320287733194605190387274781640878659090247064841521630002287276409423882599577415088163974702524820115607076448838078733704899008647751132259971343407485407553230768565335768095835260219382323950800720680355761048235733942319149829836189977069036404180862179411019175327431499782339761055122477953032487537187866582808236057022559419481809753509711315712615804242723636439850017382875977976530683700929808738874956108936597719409687268444416680462162433986483891628044828150627302274207388431172218272190472255870531908685735423498539498309919115967388464508615152499624237043745177737235177544070853846440132174839299994757244619975496197587064007474870701490937678873045869979860644874974643872062385137123927363049985035392239287879790633644032354784535851927777787270906083031994301332316712476158709792455479119092126201854803963934243495653756308

theorem state_checked :
    fixedState workScale terms = (0, 0, sumValue) := by
  decide

theorem fixedSum_value : fixedSum workScale terms = sumValue :=
  congrArg (fun s : ℕ × ℕ × ℕ => s.2.2) state_checked

theorem workScale_pos : 0 < workScale := by decide

theorem workScale_even : 2 ∣ workScale := by decide

theorem workScale_relation : workScale = Certificate1000.scale * 10 ^ 12 := by
  decide

theorem tail_checked : workScale < 2 ^ terms := by decide

theorem real_tail_checked : (workScale : ℝ) * (1 / 2 : ℝ) ^ terms < 1 := by
  have h : (workScale : ℝ) < (2 : ℝ) ^ terms := by
    exact_mod_cast tail_checked
  rw [div_pow, one_pow, mul_one_div]
  exact (div_lt_one (by positivity)).mpr h

theorem lower_margin :
    (Certificate1000.lo : ℤ) * 10 ^ 12 + 495653756308 = (sumValue : ℤ) := by
  norm_num [Certificate1000.lo, sumValue]

theorem upper_margin :
    ((sumValue + 3 * terms + 1 : ℕ) : ℤ) + 504346231547 =
      (Certificate1000.hi : ℤ) * 10 ^ 12 := by
  norm_num [Certificate1000.hi, sumValue, terms]

/-- Strict lower endpoint, already in cross-multiplied form. -/
theorem lower_checked :
    Certificate1000.lo * (workScale : ℤ) <
      (fixedSum workScale terms : ℤ) * (Certificate1000.scale : ℤ) := by
  rw [fixedSum_value]
  norm_num [Certificate1000.lo, workScale, sumValue, Certificate1000.scale]

/-- Strict upper endpoint including all rounding and tail allowances. -/
theorem upper_checked :
    ((fixedSum workScale terms + 3 * terms + 1 : ℕ) : ℤ) *
      (Certificate1000.scale : ℤ) < Certificate1000.hi * (workScale : ℤ) := by
  rw [fixedSum_value]
  norm_num [Certificate1000.hi, workScale, sumValue, Certificate1000.scale, terms]

end CatalanAnchor.EulerComputed
