import PEqualNP.Defs.TimeAlt
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate

namespace CheckpointVerification

open PEqualNP.Library Function

-- Each of the t+1 boundary configurations occupies b bits.
def readRow (bits : List Bool) (b row : ℕ) : Fin b → Bool :=
  fun j => bits.getD (row*b+j.val) false

def encodeRows {b : ℕ} (rows : ℕ → Fin b → Bool) (count : ℕ) : List Bool :=
  List.ofFn fun i : Fin (count*b) =>
    if h : 0 < b then rows (i.val/b) ⟨i.val%b,Nat.mod_lt _ h⟩ else false

theorem readEncode {b count row : ℕ} (rows : ℕ → Fin b → Bool) (hr : row < count) :
    readRow (encodeRows rows count) b row = rows row := by
  funext j
  have hb : 0 < b := by have := j.isLt; omega
  have hi : row*b+j.val < count*b := calc
    row*b+j.val < row*b+b := Nat.add_lt_add_left j.isLt _
    _ = (row+1)*b := (Nat.succ_mul _ _).symm
    _ ≤ count*b := Nat.mul_le_mul_right b hr
  have hd : (row*b+j.val)/b=row := by
    rw [Nat.mul_comm row b,Nat.mul_add_div hb,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  simp [readRow,encodeRows,hi,hb,hd,Nat.mod_eq_of_lt j.isLt]

-- The challenge selects an interval by the number of true bits in block two.
-- Challenges beyond the final interval impose only the endpoint checks.
def accepts {b : ℕ} (step : (Fin b → Bool) → Fin b → Bool) (start finish : Fin b → Bool)
    (t d : ℕ) (bits : List Bool) : Prop :=
  let size := (t+1)*b
  let rows := readRow (bits.take size) b
  let i := ((bits.drop size).take size).count true
  rows 0 = start ∧ rows t = finish ∧ (i < t → step^[d] (rows i) = rows (i+1))

private theorem altThree {s : ℕ} {P : List Bool → Prop} :
    Alt 3 s P ↔ ∃ a : List Bool, a.length = s ∧ ∀ c : List Bool, c.length = s →
      ∃ z : List Bool, z.length = s ∧ P (a ++ c ++ z) := by
  classical
  simp [Alt,List.append_assoc]

private theorem splitBlocks {s} {a c z : List Bool} (ha : a.length=s) (hc : c.length=s) :
    (a++c++z).take s = a ∧ ((a++c++z).drop s).take s = c := by
  simp [List.append_assoc,← ha,hc]

theorem reachability_iff_altThree {b : ℕ} (hb : 0 < b)
    (step : (Fin b → Bool) → Fin b → Bool) (start finish : Fin b → Bool) (t d : ℕ) :
    step^[d*t] start = finish ↔
      Alt 3 ((t+1)*b) (accepts step start finish t d) := by
  rw [altThree]
  let size := (t+1)*b
  constructor
  · intro reaches
    let rows := fun i => step^[d*i] start
    let a := encodeRows rows (t+1)
    have ha : a.length=size := by simp [a,size,encodeRows]
    refine ⟨a,ha,?_⟩
    intro c hc
    let z := List.replicate size false
    refine ⟨z,by simp [z,size],?_⟩
    have parts := splitBlocks (z := z) ha hc
    dsimp only [size] at parts
    unfold accepts
    simp only [parts.1,parts.2]
    have row (i) (hi : i ≤ t) : readRow a b i = rows i := readEncode _ (by omega)
    refine ⟨by rw [row 0 (by omega)]; simp [rows],by rw [row t le_rfl]; exact reaches,?_⟩
    intro hi
    rw [row (c.count true) (by omega),row (c.count true+1) (by omega)]
    unfold rows
    rw [Nat.mul_succ,Nat.add_comm (d * c.count true) d, Function.iterate_add_apply]
  · rintro ⟨a,ha,all⟩
    have check (i : ℕ) (hi : i ≤ size) :
        readRow a b 0 = start ∧ readRow a b t = finish ∧
        (i < t → step^[d] (readRow a b i) = readRow a b (i+1)) := by
      let c := List.replicate i true ++ List.replicate (size-i) false
      have hc : c.length=size := by simp [c]; omega
      have cc : c.count true=i := by simp [c,List.count_replicate]
      obtain ⟨z,_,H⟩ := all c hc
      have parts := splitBlocks (z := z) ha hc
      simpa only [accepts,parts.1,parts.2,cc] using H
    have ht : t ≤ size := by
      have h := Nat.mul_le_mul_left (t+1) hb
      dsimp [size]; omega
    have row (i : ℕ) (hi : i ≤ t) : step^[d*i] start = readRow a b i := by
      induction i with
      | zero => simpa using (check 0 (by omega)).1.symm
      | succ i ih =>
        rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
        exact (check i (by omega)).2.2 (by omega)
    exact (row t le_rfl).trans (check t ht).2.1

-- In the bounded-width case, t intervals trade witness size for replay length.
-- The local transition check still needs a machine implementation for SigmaV.
theorem boundedWidth {w r n : ℕ}
    (step : (Fin (2^(w*n)) → Bool) → Fin (2^(w*n)) → Bool)
    (start finish : Fin (2^(w*n)) → Bool) :
    ∃ size ≤ 2*2^((w+r)*n),
      (step^[2^((w+2*r)*n)] start = finish ↔
        Alt 3 size (accepts step start finish (2^(r*n)) (2^((w+r)*n)))) := by
  let t := 2^(r*n)
  let b := 2^(w*n)
  let d := 2^((w+r)*n)
  have hd : b*t = d := by simp [b,t,d,Nat.add_mul,pow_add]
  have hT : d*t = 2^((w+2*r)*n) := by
    unfold d t
    rw [← pow_add,← Nat.add_mul]
    congr 2; omega
  refine ⟨(t+1)*b,?_,?_⟩
  · change (t+1)*b ≤ 2*d
    have ht : 1 ≤ t := Nat.one_le_two_pow
    have hb : b ≤ b*t := by simpa using Nat.mul_le_mul_left b ht
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm t b,← hd]
    omega
  · rw [← hT]
    exact reachability_iff_altThree Nat.one_le_two_pow step start finish t d

-- Even concatenating all three rounds cannot hold a raw full-width snapshot
-- of 2^(q*n) bits at all input lengths.
theorem fullSnapshotExceedsBudget {p q : ℕ} (hpq : p < q) (K n₀ : ℕ) :
    ∃ n ≥ n₀, 3*(K*2^(p*n)+K) < 2^(q*n) := by
  let n := n₀+6*K+1
  refine ⟨n,by dsimp [n]; omega,?_⟩
  have h : 6*K < 2^n := lt_trans (by dsimp [n]; omega) (Nat.lt_two_pow_self)
  have hpow : 1 ≤ 2^(p*n) := Nat.one_le_two_pow
  have he : p*n+n ≤ q*n := by simpa [Nat.succ_mul] using Nat.mul_le_mul_right n hpq
  calc
    3*(K*2^(p*n)+K) ≤ 6*K*2^(p*n) := by nlinarith [Nat.mul_le_mul_left K hpow]
    _ < 2^n * 2^(p*n) := Nat.mul_lt_mul_of_pos_right h hpow
    _ = 2^(p*n+n) := by rw [pow_add (2 : ℕ) (p*n) n,Nat.mul_comm]
    _ ≤ 2^(q*n) := Nat.pow_le_pow_right (by decide) he

end CheckpointVerification
