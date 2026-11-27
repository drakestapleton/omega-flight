/-!
# omega-flight: Formal Discrete-Time Control Barrier Function (CBF) Safety Proof

Self-contained pure Lean 4 proof (zero external imports, zero Mathlib dependency,
zero `sorry`, zero `native_decide`, zero extra axioms).

Model-to-system link:
- Source implementation: `om/flight_core.om` (pure seeded OM-2 Q16.16 fixed-point flight core)
- Reference implementations: `ref/flight_ref.c`, `ref/flight_ref.py`
- Units: Uniform Q16.16 milli-SI (`SCALE = 65536`), 10 kHz control tick (`DT_INV = 10000`, `dt = 100 us`)
  - Positions `px, py, pz`: Q16.16 mm (`1.0 m = 65,536,000`)
  - Velocities `vx, vy, vz`: Q16.16 mm/s (`1.0 m/s = 65,536,000`)
  - Linear accelerations `ax, ay, az`: Q16.16 mm/s^2 (`1.0 m/s^2 = 65,536,000`)
  - Tilt angles `roll, pitch`: Q16.16 mrad (`1.0 rad = 65,536,000`, `0.45 rad = 29,491,200`)
  - Angular rates `wroll, wpitch`: Q16.16 mrad/s
  - Angular accelerations `ar, ap`: Q16.16 mrad/s^2
  - Electrical power `power_mw`: integer milliwatts (mW), WattCBF ceiling `P_MAX_MW = 800,000 mW` (`800 W`)
- Division semantics: `Int.tdiv` (truncation toward zero), matching Omega `div` and C11 `/`.
-/

namespace OmegaFlight

-- ============================================================
-- 1. Physical Constants (exact match to om/flight_core.om)
-- ============================================================

def Q16 : Int := 65536
def DT_INV : Int := 10000
def G_ACCEL : Int := 642908160      -- 9.81 m/s^2 in Q16.16 mm/s^2

-- Altitude geofence [0.5 m, 120.0 m], vz in [-6.0, +8.0] m/s, az in [-6.0, +12.0] m/s^2
def Z_MIN : Int := 32768000         -- 500 mm * 65536
def Z_MAX : Int := 7864320000       -- 120,000 mm * 65536
def VZ_MIN : Int := -393216000      -- -6,000 mm/s * 65536
def VZ_MAX : Int := 524288000       -- +8,000 mm/s * 65536
def AZ_MIN : Int := -393216000      -- -6,000 mm/s^2 * 65536
def AZ_MAX : Int := 786432000       -- +12,000 mm/s^2 * 65536
def TAU_Z : Int := 2
def K_Z : Int := 20001              -- DT_INV * TAU_Z + 1

-- Horizontal geofence: inscribed square |x|, |y| <= 176.776 m => x^2 + y^2 <= (250 m)^2
def R_MAX_MM : Int := 250000        -- 250.0 m in mm
def R_BOX : Int := 11585191936      -- 176,776 mm * 65536
def P_XY_MIN : Int := -11585191936
def P_XY_MAX : Int := 11585191936
def V_XY_MIN : Int := -983040000    -- -15,000 mm/s * 65536
def V_XY_MAX : Int := 983040000     -- +15,000 mm/s * 65536
def A_XY_MIN : Int := -393216000    -- -6,000 mm/s^2 * 65536
def A_XY_MAX : Int := 393216000     -- +6,000 mm/s^2 * 65536
def TAU_XY : Int := 3
def K_XY : Int := 30001             -- DT_INV * TAU_XY + 1

-- Attitude tilt geofence: |roll|, |pitch| <= 0.45 rad (~25.78 deg)
def TILT_MIN : Int := -29491200     -- -450 mrad * 65536
def TILT_MAX : Int := 29491200      -- +450 mrad * 65536
def WTILT_MIN : Int := -98304000    -- -1,500 mrad/s * 65536
def WTILT_MAX : Int := 98304000     -- +1,500 mrad/s * 65536
def ATILT_MIN : Int := -393216000   -- -6,000 mrad/s^2 * 65536
def ATILT_MAX : Int := 393216000    -- +6,000 mrad/s^2 * 65536
def TAU_TILT : Int := 1
def K_TILT : Int := 10001           -- DT_INV * TAU_TILT + 1

-- WattCBF electrical power ceiling: 800 W = 800,000 mW
def P_MAX_MW : Int := 800000

-- ============================================================
-- 2. Pure-Core Arithmetic & Truncating Division Lemmas
-- ============================================================

def clamp (x lo hi : Int) : Int :=
  if x < lo then lo else if x > hi then hi else x

def absInt (x : Int) : Int :=
  if x < 0 then -x else x

theorem clamp_ge (x lo hi : Int) (h : lo ≤ hi) : lo ≤ clamp x lo hi := by
  unfold clamp
  split
  · omega
  · split <;> omega

theorem clamp_le (x lo hi : Int) (h : lo ≤ hi) : clamp x lo hi ≤ hi := by
  unfold clamp
  split
  · omega
  · split <;> omega

theorem absInt_nonneg (x : Int) : 0 ≤ absInt x := by
  unfold absInt; split <;> omega

theorem absInt_le (x B : Int) (h1 : -B ≤ x) (h2 : x ≤ B) : absInt x ≤ B := by
  unfold absInt; split <;> omega

theorem tdiv_nonneg_eq (a b : Int) (ha : 0 ≤ a) :
    Int.tdiv a b = a / b :=
  Int.tdiv_eq_ediv_of_nonneg ha

theorem tdiv_nonpos_eq (a b : Int) (ha : a ≤ 0) :
    Int.tdiv a b = -((-a) / b) := by
  have h1 : Int.tdiv (-a) b = -Int.tdiv a b := Int.neg_tdiv a b
  have h2 : Int.tdiv (-a) b = (-a) / b := Int.tdiv_eq_ediv_of_nonneg (by omega)
  omega

theorem tdiv_mul_le_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    b * Int.tdiv a b ≤ a := by
  rw [tdiv_nonneg_eq a b ha]
  have h1 := Int.emod_add_mul_ediv a b
  have h2 := Int.emod_nonneg a (by omega : b ≠ 0)
  omega

theorem tdiv_le_mul_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    a - (b - 1) ≤ b * Int.tdiv a b := by
  rw [tdiv_nonneg_eq a b ha]
  have h1 := Int.emod_add_mul_ediv a b
  have h2 := Int.emod_lt_of_pos a hb
  omega

theorem tdiv_mul_ge_of_nonpos (a b : Int) (ha : a ≤ 0) (hb : 0 < b) :
    a ≤ b * Int.tdiv a b := by
  rw [tdiv_nonpos_eq a b ha]
  have h1 := Int.emod_add_mul_ediv (-a) b
  have h2 := Int.emod_nonneg (-a) (by omega : b ≠ 0)
  rw [Int.mul_neg]
  omega

theorem tdiv_nonneg_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ Int.tdiv a b := by
  rw [tdiv_nonneg_eq a b ha]
  exact Int.ediv_nonneg ha (by omega)

theorem tdiv_nonpos_of_nonpos (a b : Int) (ha : a ≤ 0) (hb : 0 < b) :
    Int.tdiv a b ≤ 0 := by
  rw [tdiv_nonpos_eq a b ha]
  have h := Int.ediv_nonneg (by omega : 0 ≤ -a) (by omega : 0 ≤ b)
  omega

theorem tdiv_mono (a1 a2 b : Int) (hle : a1 ≤ a2) (hb : 0 < b) :
    Int.tdiv a1 b ≤ Int.tdiv a2 b := by
  by_cases h1 : 0 ≤ a1
  · have h2 : 0 ≤ a2 := by omega
    rw [tdiv_nonneg_eq a1 b h1, tdiv_nonneg_eq a2 b h2]
    exact Int.ediv_le_ediv hb hle
  · by_cases h2 : 0 ≤ a2
    · have p1 := tdiv_nonpos_of_nonpos a1 b (by omega) hb
      have p2 := tdiv_nonneg_of_nonneg a2 b h2 hb
      omega
    · rw [tdiv_nonpos_eq a1 b (by omega), tdiv_nonpos_eq a2 b (by omega)]
      have hed := Int.ediv_le_ediv hb (by omega : -a2 ≤ -a1)
      omega

theorem tdiv_mul_cancel_pos (k b : Int) (hb : 0 < b) :
    Int.tdiv (k * b) b = k := by
  by_cases hk : 0 ≤ k
  · have hkb : 0 ≤ k * b := Int.mul_nonneg hk (by omega)
    rw [tdiv_nonneg_eq (k * b) b hkb]
    exact Int.mul_ediv_cancel k (by omega)
  · have hkb : k * b ≤ 0 := by
      have h1 : 0 ≤ (-k) * b := Int.mul_nonneg (by omega) (by omega)
      rw [Int.neg_mul] at h1
      omega
    rw [tdiv_nonpos_eq (k * b) b hkb]
    have hneg : -(k * b) = (-k) * b := (Int.neg_mul k b).symm
    rw [hneg, Int.mul_ediv_cancel (-k) (by omega)]
    omega

-- If b > 0, 0 <= a, and b * q <= a, then q <= tdiv a b
theorem le_tdiv_of_mul_le (q a b : Int) (ha : 0 ≤ a) (hb : 0 < b) (hm : b * q ≤ a) :
    q ≤ Int.tdiv a b := by
  have h1 := tdiv_le_mul_of_nonneg a b ha hb
  -- b * q <= a and a - (b - 1) <= b * tdiv a b => b * q - b * tdiv a b <= b - 1
  by_cases hlt : Int.tdiv a b < q
  · have hge : Int.tdiv a b + 1 ≤ q := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hge (by omega : 0 ≤ b)
    rw [Int.mul_add, Int.mul_one] at hmul
    omega
  · omega

theorem mul_le_mul_nonneg (a1 a2 b1 b2 : Int)
    (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    a1 * b1 ≤ a2 * b2 := by
  have h1 : a1 * b1 ≤ a2 * b1 := Int.mul_le_mul_of_nonneg_right ha hb1
  have h2 : a2 * b1 ≤ a2 * b2 := Int.mul_le_mul_of_nonneg_left hb (by omega)
  omega

theorem sq_le_of_abs_le (x B : Int) (_hB : 0 ≤ B) (h1 : -B ≤ x) (h2 : x ≤ B) :
    x * x ≤ B * B := by
  by_cases hx : 0 ≤ x
  · exact mul_le_mul_nonneg x B x B hx hx h2 h2
  · have hneg : x * x = (-x) * (-x) := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [hneg]
    exact mul_le_mul_nonneg (-x) B (-x) B (by omega) (by omega) (by omega) (by omega)

-- ============================================================
-- 3. Generic 1D Discrete-Time CBF Axis Specification & Proof
-- ============================================================

structure AxisParams where
  p_min : Int
  p_max : Int
  v_min : Int
  v_max : Int
  a_min : Int
  a_max : Int
  tau   : Int
  h_p   : p_min ≤ p_max
  h_v   : v_min ≤ 0 ∧ 0 ≤ v_max
  h_a   : a_min < 0 ∧ 0 < a_max
  h_tau : 1 ≤ tau
  h_brake_hi : v_max ≤ (-Int.tdiv a_min DT_INV) * (DT_INV * tau + 1)
  h_brake_lo : -v_min ≤ (Int.tdiv a_max DT_INV) * (DT_INV * tau + 1)

def AxisParams.K (P : AxisParams) : Int := DT_INV * P.tau + 1

def safe1d (P : AxisParams) (p v : Int) : Prop :=
  P.p_min ≤ p ∧ p ≤ P.p_max ∧
  P.v_min ≤ v ∧ v ≤ P.v_max ∧
  P.tau * v ≤ P.p_max - p ∧
  P.p_min - p ≤ P.tau * v

def step1d (p v a : Int) : Int × Int :=
  let v' := v + Int.tdiv a DT_INV
  let p' := p + Int.tdiv v' DT_INV
  (p', v')

def vCbfHi (P : AxisParams) (p : Int) : Int :=
  min P.v_max (Int.tdiv (DT_INV * (P.p_max - p)) P.K)

def vCbfLo (P : AxisParams) (p : Int) : Int :=
  max P.v_min (-Int.tdiv (DT_INV * (p - P.p_min)) P.K)

def aCbfLo (P : AxisParams) (p v : Int) : Int :=
  let vlo := vCbfLo P p
  if v + Int.tdiv P.a_min DT_INV < vlo then
    (vlo - v) * DT_INV
  else
    P.a_min

def aCbfHi (P : AxisParams) (p v : Int) : Int :=
  let vhi := vCbfHi P p
  if v + Int.tdiv P.a_max DT_INV > vhi then
    (vhi - v) * DT_INV
  else
    P.a_max

def cbfClamp1d (P : AxisParams) (p v u_des : Int) : Int :=
  clamp u_des (aCbfLo P p v) (aCbfHi P p v)

theorem K_pos (P : AxisParams) : 0 < P.K := by
  unfold AxisParams.K DT_INV
  have := P.h_tau
  omega

theorem vCbf_order (P : AxisParams) (p : Int) (hp1 : P.p_min ≤ p) (hp2 : p ≤ P.p_max) :
    vCbfLo P p ≤ 0 ∧ 0 ≤ vCbfHi P p := by
  have hK := K_pos P
  have hv := P.h_v
  have h1 : 0 ≤ Int.tdiv (DT_INV * (P.p_max - p)) P.K :=
    tdiv_nonneg_of_nonneg _ _ (by unfold DT_INV; omega) hK
  have h2 : 0 ≤ Int.tdiv (DT_INV * (p - P.p_min)) P.K :=
    tdiv_nonneg_of_nonneg _ _ (by unfold DT_INV; omega) hK
  unfold vCbfLo vCbfHi
  omega

theorem reach_intersects_vCbf (P : AxisParams) (p v : Int) (hs : safe1d P p v) :
    v + Int.tdiv P.a_min DT_INV ≤ vCbfHi P p ∧
    vCbfLo P p ≤ v + Int.tdiv P.a_max DT_INV := by
  rcases hs with ⟨hp1, hp2, hv1, hv2, hhi, hlo⟩
  have hK := K_pos P
  have hdt : (0 : Int) < DT_INV := by unfold DT_INV; omega
  have ha := P.h_a
  have hdv_min : Int.tdiv P.a_min DT_INV ≤ 0 := tdiv_nonpos_of_nonpos _ _ (by omega) hdt
  have hdv_max : 0 ≤ Int.tdiv P.a_max DT_INV := tdiv_nonneg_of_nonneg _ _ (by omega) hdt
  constructor
  · -- Prove v + tdiv a_min DT_INV <= vCbfHi P p
    have hbar_le : v + Int.tdiv P.a_min DT_INV ≤ Int.tdiv (DT_INV * (P.p_max - p)) P.K := by
      by_cases hvp : 0 ≤ v
      · -- K * v - v = DT_INV * (tau * v) <= DT_INV * (p_max - p)
        have h1 : P.K * v - v = DT_INV * (P.tau * v) := by
          unfold AxisParams.K
          rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
          omega
        have h2 : DT_INV * (P.tau * v) ≤ DT_INV * (P.p_max - p) :=
          Int.mul_le_mul_of_nonneg_left hhi (by omega)
        have h3 : v ≤ (-Int.tdiv P.a_min DT_INV) * P.K := by
          have hb := P.h_brake_hi
          unfold AxisParams.K
          omega
        have h4 : P.K * (v + Int.tdiv P.a_min DT_INV) = P.K * v - (-Int.tdiv P.a_min DT_INV) * P.K := by
          rw [Int.mul_add, Int.mul_comm P.K (Int.tdiv P.a_min DT_INV), Int.neg_mul]
          omega
        have h5 : P.K * (v + Int.tdiv P.a_min DT_INV) ≤ DT_INV * (P.p_max - p) := by omega
        exact le_tdiv_of_mul_le _ _ _ (by unfold DT_INV; omega) hK h5
      · have h0 : 0 ≤ Int.tdiv (DT_INV * (P.p_max - p)) P.K :=
          tdiv_nonneg_of_nonneg _ _ (by unfold DT_INV; omega) hK
        omega
    unfold vCbfHi
    omega
  · -- Prove vCbfLo P p <= v + tdiv a_max DT_INV
    have hbar_ge : -Int.tdiv (DT_INV * (p - P.p_min)) P.K ≤ v + Int.tdiv P.a_max DT_INV := by
      by_cases hvn : v ≤ 0
      · have h1 : P.K * (-v) - (-v) = DT_INV * (P.tau * (-v)) := by
          unfold AxisParams.K
          rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
          omega
        have hlo' : P.tau * (-v) ≤ p - P.p_min := by
          rw [Int.mul_neg]; omega
        have h2 : DT_INV * (P.tau * (-v)) ≤ DT_INV * (p - P.p_min) :=
          Int.mul_le_mul_of_nonneg_left hlo' (by omega)
        have h3 : -v ≤ Int.tdiv P.a_max DT_INV * P.K := by
          have hb := P.h_brake_lo
          unfold AxisParams.K
          omega
        have h4 : P.K * (-(v + Int.tdiv P.a_max DT_INV)) =
            P.K * (-v) - Int.tdiv P.a_max DT_INV * P.K := by
          have hs1 : -(v + Int.tdiv P.a_max DT_INV) = -v + -(Int.tdiv P.a_max DT_INV) := by omega
          have hm1 : P.K * -(Int.tdiv P.a_max DT_INV) = -(Int.tdiv P.a_max DT_INV * P.K) := by
            rw [Int.mul_neg, Int.mul_comm]
          rw [hs1, Int.mul_add, hm1]
          omega
        have h5 : P.K * (-(v + Int.tdiv P.a_max DT_INV)) ≤ DT_INV * (p - P.p_min) := by omega
        have h6 := le_tdiv_of_mul_le (-(v + Int.tdiv P.a_max DT_INV)) (DT_INV * (p - P.p_min)) P.K
          (by unfold DT_INV; omega) hK h5
        omega
      · have h0 : 0 ≤ Int.tdiv (DT_INV * (p - P.p_min)) P.K :=
          tdiv_nonneg_of_nonneg _ _ (by unfold DT_INV; omega) hK
        omega
    unfold vCbfLo
    omega

theorem aCbf_bounds_valid (P : AxisParams) (p v : Int) (hs : safe1d P p v) :
    P.a_min ≤ aCbfLo P p v ∧ aCbfLo P p v ≤ aCbfHi P p v ∧ aCbfHi P p v ≤ P.a_max := by
  have hdt : (0 : Int) < DT_INV := by unfold DT_INV; omega
  have hord := vCbf_order P p hs.1 hs.2.1
  have hreach := reach_intersects_vCbf P p v hs
  have ha := P.h_a
  have hmin_le : P.a_min ≤ DT_INV * Int.tdiv P.a_min DT_INV :=
    tdiv_mul_ge_of_nonpos P.a_min DT_INV (by omega) hdt
  have hmax_ge : DT_INV * Int.tdiv P.a_max DT_INV ≤ P.a_max :=
    tdiv_mul_le_of_nonneg P.a_max DT_INV (by omega) hdt
  unfold aCbfLo aCbfHi DT_INV at *
  dsimp only at *
  split
  · split
    · omega
    · omega
  · split
    · omega
    · omega

theorem safe1d_of_a_in_cbf_bounds (P : AxisParams) (p v a : Int)
    (hs : safe1d P p v)
    (hlo : aCbfLo P p v ≤ a) (hhi : a ≤ aCbfHi P p v) :
    safe1d P (step1d p v a).1 (step1d p v a).2 := by
  have hdt : (0 : Int) < DT_INV := by unfold DT_INV; omega
  have hK := K_pos P
  have htau := P.h_tau
  rcases hs with ⟨hp1, hp2, hv1, hv2, _, _⟩
  have hv_lo : vCbfLo P p ≤ v + Int.tdiv a DT_INV := by
    have hm := tdiv_mono (aCbfLo P p v) a DT_INV hlo hdt
    unfold aCbfLo at hm
    dsimp only at hm
    split at hm
    · rw [tdiv_mul_cancel_pos _ DT_INV hdt] at hm; omega
    · omega
  have hv_hi : v + Int.tdiv a DT_INV ≤ vCbfHi P p := by
    have hm := tdiv_mono a (aCbfHi P p v) DT_INV hhi hdt
    unfold aCbfHi at hm
    dsimp only at hm
    split at hm
    · rw [tdiv_mul_cancel_pos _ DT_INV hdt] at hm; omega
    · omega
  have h_vlo_min : P.v_min ≤ vCbfLo P p := by unfold vCbfLo; omega
  have h_vlo_bar : -Int.tdiv (DT_INV * (p - P.p_min)) P.K ≤ vCbfLo P p := by unfold vCbfLo; omega
  have h_vhi_max : vCbfHi P p ≤ P.v_max := by unfold vCbfHi; omega
  have h_vhi_bar : vCbfHi P p ≤ Int.tdiv (DT_INV * (P.p_max - p)) P.K := by unfold vCbfHi; omega
  unfold step1d safe1d
  dsimp only
  let v' := v + Int.tdiv a DT_INV
  let dp := Int.tdiv v' DT_INV
  change P.p_min ≤ p + dp ∧ p + dp ≤ P.p_max ∧ P.v_min ≤ v' ∧ v' ≤ P.v_max ∧
    P.tau * v' ≤ P.p_max - (p + dp) ∧ P.p_min - (p + dp) ≤ P.tau * v'
  have h_pmax_mul : P.K * Int.tdiv (DT_INV * (P.p_max - p)) P.K ≤ DT_INV * (P.p_max - p) :=
    tdiv_mul_le_of_nonneg _ _ (by unfold DT_INV; omega) hK
  have h_pmin_mul : P.K * Int.tdiv (DT_INV * (p - P.p_min)) P.K ≤ DT_INV * (p - P.p_min) :=
    tdiv_mul_le_of_nonneg _ _ (by unfold DT_INV; omega) hK
  -- Upper barrier helper when v' >= 0
  have h_up : 0 ≤ v' → P.tau * v' + dp ≤ P.p_max - p ∧ 0 ≤ dp := by
    intro hvp
    have hdp0 : 0 ≤ dp := tdiv_nonneg_of_nonneg v' DT_INV hvp hdt
    have hdp_le : DT_INV * dp ≤ v' := tdiv_mul_le_of_nonneg v' DT_INV hvp hdt
    have hkv : P.K * v' ≤ P.K * Int.tdiv (DT_INV * (P.p_max - p)) P.K :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hkv2 : P.K * v' ≤ DT_INV * (P.p_max - p) := by omega
    have hkv_eq : P.K * v' = DT_INV * (P.tau * v') + v' := by
      unfold AxisParams.K
      rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
    have hsum : DT_INV * (P.tau * v' + dp) ≤ DT_INV * (P.p_max - p) := by
      rw [Int.mul_add]; omega
    have hdiv : P.tau * v' + dp ≤ P.p_max - p := by
      unfold DT_INV at hsum; omega
    exact ⟨hdiv, hdp0⟩
  -- Lower barrier helper when v' <= 0
  have h_dn : v' ≤ 0 → P.tau * (-v') + (-dp) ≤ p - P.p_min ∧ dp ≤ 0 := by
    intro hvn
    have hdp0 : dp ≤ 0 := tdiv_nonpos_of_nonpos v' DT_INV hvn hdt
    have hdp_ge : v' ≤ DT_INV * dp := tdiv_mul_ge_of_nonpos v' DT_INV hvn hdt
    have hkv : P.K * (-v') ≤ P.K * Int.tdiv (DT_INV * (p - P.p_min)) P.K :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hkv2 : P.K * (-v') ≤ DT_INV * (p - P.p_min) := by omega
    have hkv_eq : P.K * (-v') = DT_INV * (P.tau * (-v')) + (-v') := by
      unfold AxisParams.K
      rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
    have hsum : DT_INV * (P.tau * (-v') + (-dp)) ≤ DT_INV * (p - P.p_min) := by
      rw [Int.mul_add, Int.mul_neg DT_INV dp]; omega
    have hdiv : P.tau * (-v') + (-dp) ≤ p - P.p_min := by
      unfold DT_INV at hsum; omega
    exact ⟨hdiv, hdp0⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- p_min <= p + dp
    by_cases hvp : 0 ≤ v'
    · have := (h_up hvp).2; omega
    · have hd := h_dn (by omega)
      have htv : 0 ≤ P.tau * (-v') := Int.mul_nonneg (by omega) (by omega)
      omega
  · -- p + dp <= p_max
    by_cases hvp : 0 ≤ v'
    · have hu := h_up hvp
      have htv : 0 ≤ P.tau * v' := Int.mul_nonneg (by omega) hvp
      omega
    · have := (h_dn (by omega)).2; omega
  · omega
  · omega
  · -- tau * v' <= p_max - (p + dp)
    by_cases hvp : 0 ≤ v'
    · have := (h_up hvp).1; omega
    · have hd := (h_dn (by omega)).2
      have htv : P.tau * v' ≤ 0 := by
        have h1 : 0 ≤ P.tau * (-v') := Int.mul_nonneg (by omega) (by omega)
        rw [Int.mul_neg] at h1; omega
      omega
  · -- p_min - (p + dp) <= tau * v'
    by_cases hvp : 0 ≤ v'
    · have hu := (h_up hvp).2
      have htv : 0 ≤ P.tau * v' := Int.mul_nonneg (by omega) hvp
      omega
    · have hd := (h_dn (by omega)).1
      rw [Int.mul_neg] at hd
      omega

-- ============================================================
-- 4. Instantiate 5 Drone Axes (X, Y, Z, Roll, Pitch)
-- ============================================================

def axisXY : AxisParams where
  p_min := P_XY_MIN; p_max := P_XY_MAX
  v_min := V_XY_MIN; v_max := V_XY_MAX
  a_min := A_XY_MIN; a_max := A_XY_MAX
  tau   := TAU_XY
  h_p   := by decide
  h_v   := by decide
  h_a   := by decide
  h_tau := by decide
  h_brake_hi := by decide
  h_brake_lo := by decide

def axisZ : AxisParams where
  p_min := Z_MIN;  p_max := Z_MAX
  v_min := VZ_MIN; v_max := VZ_MAX
  a_min := AZ_MIN; a_max := AZ_MAX
  tau   := TAU_Z
  h_p   := by decide
  h_v   := by decide
  h_a   := by decide
  h_tau := by decide
  h_brake_hi := by decide
  h_brake_lo := by decide

def axisTilt : AxisParams where
  p_min := TILT_MIN;  p_max := TILT_MAX
  v_min := WTILT_MIN; v_max := WTILT_MAX
  a_min := ATILT_MIN; a_max := ATILT_MAX
  tau   := TAU_TILT
  h_p   := by decide
  h_v   := by decide
  h_a   := by decide
  h_tau := by decide
  h_brake_hi := by decide
  h_brake_lo := by decide

-- ============================================================
-- 5. Full 10-DOF Drone State, WattCBF Power Model & Shield
-- ============================================================

structure FlightState where
  px     : Int
  py     : Int
  pz     : Int
  vx     : Int
  vy     : Int
  vz     : Int
  roll   : Int
  pitch  : Int
  wroll  : Int
  wpitch : Int

structure Cmd where
  ax : Int
  ay : Int
  az : Int
  ar : Int
  ap : Int

def safeState (s : FlightState) : Prop :=
  safe1d axisXY s.px s.vx ∧
  safe1d axisXY s.py s.vy ∧
  safe1d axisZ  s.pz s.vz ∧
  safe1d axisTilt s.roll s.wroll ∧
  safe1d axisTilt s.pitch s.wpitch

-- Euclidean horizontal geofence radius check (in mm): px_mm^2 + py_mm^2 <= 250000^2
def inRadiusGeofence (s : FlightState) : Prop :=
  let xmm := Int.tdiv s.px Q16
  let ymm := Int.tdiv s.py Q16
  xmm * xmm + ymm * ymm ≤ R_MAX_MM * R_MAX_MM

theorem safeState_implies_radius (s : FlightState) (hs : safeState s) :
    inRadiusGeofence s := by
  have hx1 : P_XY_MIN ≤ s.px := hs.1.1
  have hx2 : s.px ≤ P_XY_MAX := hs.1.2.1
  have hy1 : P_XY_MIN ≤ s.py := hs.2.1.1
  have hy2 : s.py ≤ P_XY_MAX := hs.2.1.2.1
  have hq : (0 : Int) < Q16 := by decide
  have hxlo : -176776 ≤ Int.tdiv s.px Q16 := by
    have hm := tdiv_mono P_XY_MIN s.px Q16 hx1 hq
    have hc : Int.tdiv P_XY_MIN Q16 = -176776 := by decide
    omega
  have hxhi : Int.tdiv s.px Q16 ≤ 176776 := by
    have hm := tdiv_mono s.px P_XY_MAX Q16 hx2 hq
    have hc : Int.tdiv P_XY_MAX Q16 = 176776 := by decide
    omega
  have hylo : -176776 ≤ Int.tdiv s.py Q16 := by
    have hm := tdiv_mono P_XY_MIN s.py Q16 hy1 hq
    have hc : Int.tdiv P_XY_MIN Q16 = -176776 := by decide
    omega
  have hyhi : Int.tdiv s.py Q16 ≤ 176776 := by
    have hm := tdiv_mono s.py P_XY_MAX Q16 hy2 hq
    have hc : Int.tdiv P_XY_MAX Q16 = 176776 := by decide
    omega
  have hxsq : Int.tdiv s.px Q16 * Int.tdiv s.px Q16 ≤ 176776 * 176776 :=
    sq_le_of_abs_le _ 176776 (by decide) hxlo hxhi
  have hysq : Int.tdiv s.py Q16 * Int.tdiv s.py Q16 ≤ 176776 * 176776 :=
    sq_le_of_abs_le _ 176776 (by decide) hylo hyhi
  unfold inRadiusGeofence R_MAX_MM
  dsimp only
  omega

-- WattCBF electrical power model in milliwatts (exact match to om/flight_core.om)
def powerMw (ax ay az vz : Int) : Int :=
  let tz_mms2 := Int.tdiv (G_ACCEL + az) Q16
  let tx_mms2 := Int.tdiv (absInt ax) Q16
  let ty_mms2 := Int.tdiv (absInt ay) Q16
  let vz_pos  := if 0 < vz then Int.tdiv vz Q16 else 0
  25 * (tz_mms2 + tx_mms2 + ty_mms2) + Int.tdiv (tz_mms2 * vz_pos) 375

def stepFlight (s : FlightState) (u : Cmd) : FlightState :=
  let (px', vx') := step1d s.px s.vx u.ax
  let (py', vy') := step1d s.py s.vy u.ay
  let (pz', vz') := step1d s.pz s.vz u.az
  let (r', wr')  := step1d s.roll s.wroll u.ar
  let (p', wp')  := step1d s.pitch s.wpitch u.ap
  ⟨px', py', pz', vx', vy', vz', r', p', wr', wp'⟩

def wattAzCap (ax1 ay1 az_lo vz : Int) : Int :=
  let tx1   := Int.tdiv (absInt ax1) Q16
  let ty1   := Int.tdiv (absInt ay1) Q16
  let vzp   := if 0 < vz then Int.tdiv vz Q16 else 0
  let rem_p := P_MAX_MW - 25 * (tx1 + ty1)
  if 0 < rem_p then
    Int.tdiv (rem_p * 375) (9375 + vzp) * Q16 - G_ACCEL
  else
    az_lo

-- Full 5-axis CBF + WattCBF Safety Shield (exact match to om/flight_core.om)
def cbfShield (s : FlightState) (u_ai : Cmd) : Cmd :=
  let ax_lo := aCbfLo axisXY s.px s.vx
  let ax_hi := aCbfHi axisXY s.px s.vx
  let ay_lo := aCbfLo axisXY s.py s.vy
  let ay_hi := aCbfHi axisXY s.py s.vy
  let az_lo := aCbfLo axisZ  s.pz s.vz
  let az_hi := aCbfHi axisZ  s.pz s.vz
  let ar_s  := cbfClamp1d axisTilt s.roll  s.wroll  u_ai.ar
  let ap_s  := cbfClamp1d axisTilt s.pitch s.wpitch u_ai.ap
  let ax1   := clamp u_ai.ax ax_lo ax_hi
  let ay1   := clamp u_ai.ay ay_lo ay_hi
  let az1   := clamp u_ai.az az_lo az_hi
  if powerMw ax1 ay1 az1 s.vz ≤ P_MAX_MW then
    ⟨ax1, ay1, az1, ar_s, ap_s⟩
  else
    let az_cap := wattAzCap ax1 ay1 az_lo s.vz
    let az2 := clamp az1 az_lo (max az_lo (min az_hi az_cap))
    if powerMw ax1 ay1 az2 s.vz ≤ P_MAX_MW then
      ⟨ax1, ay1, az2, ar_s, ap_s⟩
    else
      let ax_mp := clamp 0 ax_lo ax_hi
      let ay_mp := clamp 0 ay_lo ay_hi
      let az_mp := az_lo
      ⟨ax_mp, ay_mp, az_mp, ar_s, ap_s⟩

-- Prove that the minimum-power safe corner ALWAYS satisfies WattCBF <= 800 W!
theorem min_power_corner_within_watt_cbf (s : FlightState) (hs : safeState s) :
    powerMw
      (clamp 0 (aCbfLo axisXY s.px s.vx) (aCbfHi axisXY s.px s.vx))
      (clamp 0 (aCbfLo axisXY s.py s.vy) (aCbfHi axisXY s.py s.vy))
      (aCbfLo axisZ s.pz s.vz)
      s.vz ≤ P_MAX_MW := by
  have hbx := aCbf_bounds_valid axisXY s.px s.vx hs.1
  have hby := aCbf_bounds_valid axisXY s.py s.vy hs.2.1
  have hbz := aCbf_bounds_valid axisZ  s.pz s.vz hs.2.2.1
  have hq : (0 : Int) < Q16 := by decide
  let ax_mp := clamp 0 (aCbfLo axisXY s.px s.vx) (aCbfHi axisXY s.px s.vx)
  let ay_mp := clamp 0 (aCbfLo axisXY s.py s.vy) (aCbfHi axisXY s.py s.vy)
  let az_mp := aCbfLo axisZ s.pz s.vz
  change powerMw ax_mp ay_mp az_mp s.vz ≤ P_MAX_MW
  have hax_lo : A_XY_MIN ≤ ax_mp := Int.le_trans hbx.1 (clamp_ge _ _ _ hbx.2.1)
  have hax_hi : ax_mp ≤ A_XY_MAX := Int.le_trans (clamp_le _ _ _ hbx.2.1) hbx.2.2
  have hay_lo : A_XY_MIN ≤ ay_mp := Int.le_trans hby.1 (clamp_ge _ _ _ hby.2.1)
  have hay_hi : ay_mp ≤ A_XY_MAX := Int.le_trans (clamp_le _ _ _ hby.2.1) hby.2.2
  have htx : Int.tdiv (absInt ax_mp) Q16 ≤ 6000 := by
    have hab : absInt ax_mp ≤ A_XY_MAX :=
      absInt_le ax_mp A_XY_MAX (by unfold A_XY_MIN A_XY_MAX at *; omega) hax_hi
    have hm := tdiv_mono _ _ Q16 hab hq
    have hc : Int.tdiv A_XY_MAX Q16 = 6000 := by decide
    omega
  have hty : Int.tdiv (absInt ay_mp) Q16 ≤ 6000 := by
    have hab : absInt ay_mp ≤ A_XY_MAX :=
      absInt_le ay_mp A_XY_MAX (by unfold A_XY_MIN A_XY_MAX at *; omega) hay_hi
    have hm := tdiv_mono _ _ Q16 hab hq
    have hc : Int.tdiv A_XY_MAX Q16 = 6000 := by decide
    omega
  have htz_nonneg : 0 ≤ G_ACCEL + az_mp := by
    have haz_ge : AZ_MIN ≤ az_mp := hbz.1
    unfold G_ACCEL AZ_MIN at *
    omega
  unfold powerMw P_MAX_MW
  dsimp only
  by_cases hvz : 0 < s.vz
  · have hordz := vCbf_order axisZ s.pz hs.2.2.1.1 hs.2.2.1.2.1
    have haz_le0 : az_mp ≤ 0 := by
      show aCbfLo axisZ s.pz s.vz ≤ 0
      unfold aCbfLo DT_INV
      dsimp only
      split
      · have := hordz.1; omega
      · show AZ_MIN ≤ 0; decide
    have htz_le : Int.tdiv (G_ACCEL + az_mp) Q16 ≤ 9810 := by
      have hm := tdiv_mono (G_ACCEL + az_mp) G_ACCEL Q16 (by omega) hq
      have hc : Int.tdiv G_ACCEL Q16 = 9810 := by decide
      omega
    have htz0 : 0 ≤ Int.tdiv (G_ACCEL + az_mp) Q16 := tdiv_nonneg_of_nonneg _ _ htz_nonneg hq
    have hvzp_le : Int.tdiv s.vz Q16 ≤ 8000 := by
      have hv2 : s.vz ≤ VZ_MAX := hs.2.2.1.2.2.2.1
      have hm := tdiv_mono s.vz VZ_MAX Q16 hv2 hq
      have hc : Int.tdiv VZ_MAX Q16 = 8000 := by decide
      omega
    have hvzp0 : 0 ≤ Int.tdiv s.vz Q16 := tdiv_nonneg_of_nonneg _ _ (by omega) hq
    have hprod_le : Int.tdiv (G_ACCEL + az_mp) Q16 * Int.tdiv s.vz Q16 ≤ 9810 * 8000 :=
      mul_le_mul_nonneg _ 9810 _ 8000 htz0 hvzp0 htz_le hvzp_le
    have hclimb : Int.tdiv (Int.tdiv (G_ACCEL + az_mp) Q16 * Int.tdiv s.vz Q16) 375 ≤ 209280 := by
      have hm := tdiv_mono _ (9810 * 8000) 375 hprod_le (by decide)
      have hc : Int.tdiv (9810 * 8000) 375 = 209280 := by decide
      omega
    simp only [hvz, ↓reduceIte]
    omega
  · have hsz := hs.2.2.1
    rcases hsz with ⟨hz1, hz2, hvz1, hvz2, _, hzlo⟩
    have hz1' : Z_MIN ≤ s.pz := hz1
    have hvz1' : VZ_MIN ≤ s.vz := hvz1
    have hzlo' : Z_MIN - s.pz ≤ 2 * s.vz := hzlo
    have hKz : axisZ.K = 20001 := by decide
    have haz_le : az_mp ≤ 196610000 := by
      show aCbfLo axisZ s.pz s.vz ≤ 196610000
      unfold aCbfLo
      dsimp only
      split
      · have h1 : 20001 * (-s.vz - 19661) ≤ DT_INV * (s.pz - Z_MIN) - 20000 := by
          unfold VZ_MIN Z_MIN DT_INV at *
          omega
        have h4 : DT_INV * (s.pz - Z_MIN) - 20000 ≤
            20001 * Int.tdiv (DT_INV * (s.pz - Z_MIN)) 20001 :=
          tdiv_le_mul_of_nonneg _ 20001 (by unfold DT_INV Z_MIN at *; omega) (by decide)
        have h5 : -s.vz - 19661 ≤ Int.tdiv (DT_INV * (s.pz - Z_MIN)) 20001 := by omega
        have hvlo_le : vCbfLo axisZ s.pz ≤ s.vz + 19661 := by
          unfold vCbfLo
          rw [hKz]
          change max VZ_MIN (-Int.tdiv (DT_INV * (s.pz - Z_MIN)) 20001) ≤ s.vz + 19661
          unfold VZ_MIN Z_MIN at *
          omega
        unfold DT_INV at *
        omega
      · show AZ_MIN ≤ 196610000; decide
    have htz_le : Int.tdiv (G_ACCEL + az_mp) Q16 ≤ 12810 := by
      have hm := tdiv_mono (G_ACCEL + az_mp) (G_ACCEL + 196610000) Q16 (by omega) hq
      have hc : Int.tdiv (G_ACCEL + 196610000) Q16 = 12810 := by decide
      omega
    simp only [hvz, ↓reduceIte]
    have hzero : Int.tdiv (Int.tdiv (G_ACCEL + az_mp) Q16 * 0) 375 = 0 := by simp
    rw [hzero]
    omega

-- ============================================================
-- 6. Main Safety Invariance Theorems (1-Step & Inductive)
-- ============================================================

theorem cbf_step_preserves_safe (s : FlightState) (u_ai : Cmd) (hs : safeState s) :
    let u_safe := cbfShield s u_ai
    safeState (stepFlight s u_safe) ∧
    inRadiusGeofence (stepFlight s u_safe) ∧
    powerMw u_safe.ax u_safe.ay u_safe.az s.vz ≤ P_MAX_MW := by
  have hbx := aCbf_bounds_valid axisXY s.px s.vx hs.1
  have hby := aCbf_bounds_valid axisXY s.py s.vy hs.2.1
  have hbz := aCbf_bounds_valid axisZ  s.pz s.vz hs.2.2.1
  have hbr := aCbf_bounds_valid axisTilt s.roll s.wroll hs.2.2.2.1
  have hbp := aCbf_bounds_valid axisTilt s.pitch s.wpitch hs.2.2.2.2
  have hr_safe : safe1d axisTilt
      (step1d s.roll s.wroll (cbfClamp1d axisTilt s.roll s.wroll u_ai.ar)).1
      (step1d s.roll s.wroll (cbfClamp1d axisTilt s.roll s.wroll u_ai.ar)).2 :=
    safe1d_of_a_in_cbf_bounds axisTilt s.roll s.wroll _ hs.2.2.2.1
      (clamp_ge _ _ _ hbr.2.1) (clamp_le _ _ _ hbr.2.1)
  have hp_safe : safe1d axisTilt
      (step1d s.pitch s.wpitch (cbfClamp1d axisTilt s.pitch s.wpitch u_ai.ap)).1
      (step1d s.pitch s.wpitch (cbfClamp1d axisTilt s.pitch s.wpitch u_ai.ap)).2 :=
    safe1d_of_a_in_cbf_bounds axisTilt s.pitch s.wpitch _ hs.2.2.2.2
      (clamp_ge _ _ _ hbp.2.1) (clamp_le _ _ _ hbp.2.1)
  dsimp only
  unfold cbfShield
  dsimp only
  let ax_lo := aCbfLo axisXY s.px s.vx
  let ax_hi := aCbfHi axisXY s.px s.vx
  let ay_lo := aCbfLo axisXY s.py s.vy
  let ay_hi := aCbfHi axisXY s.py s.vy
  let az_lo := aCbfLo axisZ s.pz s.vz
  let az_hi := aCbfHi axisZ s.pz s.vz
  let ar_s := cbfClamp1d axisTilt s.roll s.wroll u_ai.ar
  let ap_s := cbfClamp1d axisTilt s.pitch s.wpitch u_ai.ap
  let ax1 := clamp u_ai.ax ax_lo ax_hi
  let ay1 := clamp u_ai.ay ay_lo ay_hi
  let az1 := clamp u_ai.az az_lo az_hi
  split
  · rename_i hp1
    have hsafe' : safeState (stepFlight s ⟨ax1, ay1, az1, ar_s, ap_s⟩) := by
      refine ⟨?_, ?_, ?_, hr_safe, hp_safe⟩
      · exact safe1d_of_a_in_cbf_bounds axisXY _ _ _ hs.1 (clamp_ge _ _ _ hbx.2.1) (clamp_le _ _ _ hbx.2.1)
      · exact safe1d_of_a_in_cbf_bounds axisXY _ _ _ hs.2.1 (clamp_ge _ _ _ hby.2.1) (clamp_le _ _ _ hby.2.1)
      · exact safe1d_of_a_in_cbf_bounds axisZ  _ _ _ hs.2.2.1 (clamp_ge _ _ _ hbz.2.1) (clamp_le _ _ _ hbz.2.1)
    exact ⟨hsafe', safeState_implies_radius _ hsafe', hp1⟩
  · split
    · rename_i _ hp2
      let az_cap := wattAzCap ax1 ay1 az_lo s.vz
      let az2 := clamp az1 az_lo (max az_lo (min az_hi az_cap))
      have hhi_ok : az_lo ≤ max az_lo (min az_hi az_cap) := by omega
      have hhi_le : max az_lo (min az_hi az_cap) ≤ az_hi := by
        have : az_lo ≤ az_hi := hbz.2.1; omega
      have hsafe' : safeState (stepFlight s ⟨ax1, ay1, az2, ar_s, ap_s⟩) := by
        refine ⟨?_, ?_, ?_, hr_safe, hp_safe⟩
        · exact safe1d_of_a_in_cbf_bounds axisXY _ _ _ hs.1 (clamp_ge _ _ _ hbx.2.1) (clamp_le _ _ _ hbx.2.1)
        · exact safe1d_of_a_in_cbf_bounds axisXY _ _ _ hs.2.1 (clamp_ge _ _ _ hby.2.1) (clamp_le _ _ _ hby.2.1)
        · exact safe1d_of_a_in_cbf_bounds axisZ  _ _ _ hs.2.2.1
            (clamp_ge _ _ _ hhi_ok) (Int.le_trans (clamp_le _ _ _ hhi_ok) hhi_le)
      exact ⟨hsafe', safeState_implies_radius _ hsafe', hp2⟩
    · have hsafe' : safeState (stepFlight s ⟨clamp 0 ax_lo ax_hi, clamp 0 ay_lo ay_hi, az_lo, ar_s, ap_s⟩) := by
        refine ⟨?_, ?_, ?_, hr_safe, hp_safe⟩
        · exact safe1d_of_a_in_cbf_bounds axisXY _ _ _ hs.1 (clamp_ge _ _ _ hbx.2.1) (clamp_le _ _ _ hbx.2.1)
        · exact safe1d_of_a_in_cbf_bounds axisXY _ _ _ hs.2.1 (clamp_ge _ _ _ hby.2.1) (clamp_le _ _ _ hby.2.1)
        · exact safe1d_of_a_in_cbf_bounds axisZ  _ _ _ hs.2.2.1 (Int.le_refl _) hbz.2.1
      exact ⟨hsafe', safeState_implies_radius _ hsafe', min_power_corner_within_watt_cbf s hs⟩

-- Multi-step closed-loop shielded flight execution
def runShielded (s0 : FlightState) (u_seq : Nat → Cmd) : Nat → FlightState
  | 0     => s0
  | t + 1 =>
    let st := runShielded s0 u_seq t
    stepFlight st (cbfShield st (u_seq t))

-- Inductive Safety Invariance for ALL ticks t : Nat and ANY adversarial planner sequence!
theorem cbf_inductive_safety (s0 : FlightState) (u_seq : Nat → Cmd)
    (h0 : safeState s0) :
    ∀ t : Nat,
      safeState (runShielded s0 u_seq t) ∧
      inRadiusGeofence (runShielded s0 u_seq t) := by
  intro t
  induction t with
  | zero => exact ⟨h0, safeState_implies_radius s0 h0⟩
  | succ k ih =>
    have hstep := cbf_step_preserves_safe (runShielded s0 u_seq k) (u_seq k) ih.1
    exact ⟨hstep.1, hstep.2.1⟩

-- Concrete nominal hover initial state (0, 0, 10.0 m) is provably safe
def initHover : FlightState :=
  ⟨0, 0, 655360000, 0, 0, 0, 0, 0, 0, 0⟩

theorem initHover_safe : safeState initHover := by
  unfold safeState safe1d initHover axisXY axisZ axisTilt
    P_XY_MIN P_XY_MAX V_XY_MIN V_XY_MAX TAU_XY
    Z_MIN Z_MAX VZ_MIN VZ_MAX TAU_Z
    TILT_MIN TILT_MAX WTILT_MIN WTILT_MAX TAU_TILT
  decide

-- ============================================================
-- 7. Negative Control: Unshielded Adversarial Dive Violates Safety
-- ============================================================

def floorHover : FlightState :=
  ⟨0, 0, Z_MIN, 0, 0, 0, 0, 0, 0, 0⟩

theorem floorHover_safe : safeState floorHover := by
  unfold safeState safe1d floorHover axisXY axisZ axisTilt
    P_XY_MIN P_XY_MAX V_XY_MIN V_XY_MAX TAU_XY
    Z_MIN Z_MAX VZ_MIN VZ_MAX TAU_Z
    TILT_MIN TILT_MAX WTILT_MIN WTILT_MAX TAU_TILT
  decide

-- Hostile planner commands a full-throttle dive (-999 m/s^2)
def hostileDiveCmd : Cmd :=
  ⟨0, 0, -65470464000, 0, 0⟩

-- Negative control: WITHOUT cbfShield, a single hostile dive breaches Z_MIN!
theorem unshielded_dive_violates_safety :
    ¬ safeState (stepFlight floorHover hostileDiveCmd) := by
  intro h
  have hz : Z_MIN ≤ (stepFlight floorHover hostileDiveCmd).pz := h.2.2.1.1
  have hbad : (stepFlight floorHover hostileDiveCmd).pz < Z_MIN := by decide
  omega

-- Positive counterpart: WITH cbfShield, the exact same hostile dive stays provably safe!
theorem shielded_dive_stays_safe :
    safeState (stepFlight floorHover (cbfShield floorHover hostileDiveCmd)) :=
  (cbf_step_preserves_safe floorHover hostileDiveCmd floorHover_safe).1

#print axioms cbf_step_preserves_safe
#print axioms cbf_inductive_safety
#print axioms initHover_safe
#print axioms floorHover_safe
#print axioms unshielded_dive_violates_safety
#print axioms shielded_dive_stays_safe

end OmegaFlight
