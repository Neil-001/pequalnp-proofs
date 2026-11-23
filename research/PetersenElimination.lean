import PEqualNP.MetaComplexity.L106
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

namespace PetersenElimination
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.Readers

abbrev Bound {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) :=
  ∀ s, HasCircuitSize n f s → k ≤ s

-- A child circuit sees the surviving inputs through a renumbering.
private theorem transfer {n m : ℕ} {f : (Fin n → Bool) → Bool}
    {g : (Fin m → Bool) → Bool} {k : ℕ} (π : Fin n → Fin m)
    (he : ∀ x, f (x ∘ π) = g x) (hg : Bound g k) : Bound f k := by
  intro s h
  exact hg s (funext he ▸ relabel_size π f s h)

def pin {n} (f : (Fin n → Bool) → Bool) (p : Fin n) (b : Bool) :=
  fun x => f (Function.update x p b)

private theorem one {n k} {f : (Fin (n+1) → Bool) → Bool} (p : Fin (n+1)) (b : Bool)
    (hd : Dep f p) (hn : pin f p b (fun _ => false) ≠ pin f p b (fun _ => true))
    (hchild : Bound (pin f p b) k) (hk : 0 < k) : Bound f (k+1) := by
  intro s h
  cases s with
  | zero =>
    obtain ⟨c,hok,hs,he⟩ := h
    have h1 : HasCircuitSize _ f 1 := ⟨c,hok,by omega,he⟩
    have hc := Forest.one_gate_at n f p b 0 hd ⟨_,_,hn⟩ h1
    have := hchild 0 hc
    omega
  | succ s =>
    have hc := Forest.one_gate_at n f p b s hd ⟨_,_,hn⟩ h
    exact Nat.succ_le_succ (hchild s hc)

private theorem split {n k} {f : (Fin (n+1) → Bool) → Bool} (p : Fin (n+1))
    (hd : Dep f p)
    (hn : ∀ b, pin f p b (fun _ => false) ≠ pin f p b (fun _ => true))
    (hchild : ∀ b, Bound (pin f p b) k) : Bound f (k+2) := by
  intro s h
  obtain ⟨b,t,hpay,hc⟩ := gate_elim_at n f p s hd (fun b => ⟨_,_,hn b⟩) h
  have := hchild b t hc
  omega

private def point {n : ℕ} (i : Fin (n+1)) (j : Fin n) := decide (i.val = j.val)

private theorem fan {n k} {f : (Fin (n+1) → Bool) → Bool}
    (hd : Dep f 0)
    (hn : ∀ p b, pin f p b (fun _ => false) ≠ pin f p b (fun _ => true))
    (hsep : ∀ p q : Fin (n+1), p ≠ q → ∀ a b : Bool, ∃ i : Fin (n+2),
      ¬ (f (set2 (point i) p (!a) q b) = f (set2 (point i) p a q (!b)) ∧
         f (set2 (point i) p a q (!b)) = f (set2 (point i) p (!a) q (!b))))
    (children : ∀ p, Bound (pin f p false) k) : Bound f (k+2) := by
  intro s h
  have nfun : NoFunnel f := by
    intro p q hne _ _ ⟨a,b,hf⟩
    obtain ⟨i,hi⟩ := hsep p q hne a b
    exact hi (hf (point i))
  obtain ⟨y,_,pay⟩ := fanout_step n f s ⟨0,hd⟩ (fun p _ b => ⟨_,_,hn p b⟩) nfun h
  rcases pay with ⟨⟨t,ht,hc⟩,_⟩ | ⟨⟨t,ht,hc⟩,_⟩ | ⟨⟨t,ht,hc⟩,_⟩ <;>
    have := children y t hc <;> omega


def cycleFive (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4)

theorem cycleFiveLower : Bound cycleFive 7 := by
  apply transfer (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) (g := fun x => decide (∃ i j : Fin 5, (i.val+1)%5=j.val ∧ x i=true ∧ x j=true))
  · decide
  · intro s h
    have := (L106 5 s (by decide)).mp h
    omega

def pendantCycle (x : Fin 6 → Bool) : Bool :=
  (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5)

theorem pendantCycleLower : Bound pendantCycle 8 := by
  apply one (k := 7) 0 false ⟨point 5, by decide⟩ (by decide)
  · exact transfer (![0, 0, 1, 2, 3, 4] : Fin 6 → Fin 5) (by decide) cycleFiveLower
  · decide

def eightEdgeChild (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6)

theorem eightEdgeChildLower : Bound eightEdgeChild 9 := by
  apply one (k := 8) 0 false ⟨point 1, by decide⟩ (by decide)
  · exact transfer (![0, 0, 1, 2, 3, 4, 5] : Fin 7 → Fin 6) (by decide) pendantCycleLower
  · decide

def sevenEdgeChild (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 4) || (x 2 && x 4) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6)

theorem sevenEdgeChildLower : Bound sevenEdgeChild 9 := by
  apply one (k := 8) 0 false ⟨point 4, by decide⟩ (by decide)
  · exact transfer (![0, 0, 1, 2, 3, 4, 5] : Fin 7 → Fin 6) (by decide) pendantCycleLower
  · decide

def adjacentDeletions (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)

theorem adjacentDeletionsLower : Bound adjacentDeletions 11 := by
  apply fan (k := 9) ⟨point 1, by decide⟩ (by decide) (by decide)
  intro p
  fin_cases p
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6] : Fin 8 → Fin 7) (by decide) eightEdgeChildLower
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6] : Fin 8 → Fin 7) (by decide) sevenEdgeChildLower
  · exact transfer (![0, 1, 0, 3, 4, 5, 6, 2] : Fin 8 → Fin 7) (by decide) eightEdgeChildLower
  · exact transfer (![0, 5, 3, 0, 4, 1, 2, 6] : Fin 8 → Fin 7) (by decide) eightEdgeChildLower
  · exact transfer (![3, 5, 0, 4, 0, 6, 2, 1] : Fin 8 → Fin 7) (by decide) eightEdgeChildLower
  · exact transfer (![0, 4, 2, 1, 3, 0, 6, 5] : Fin 8 → Fin 7) (by decide) sevenEdgeChildLower
  · exact transfer (![2, 5, 3, 0, 1, 4, 0, 6] : Fin 8 → Fin 7) (by decide) sevenEdgeChildLower
  · exact transfer (![2, 4, 0, 3, 1, 5, 6, 0] : Fin 8 → Fin 7) (by decide) sevenEdgeChildLower

def cycleSix (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 3 && x 5)

theorem cycleSixLower : Bound cycleSix 8 := by
  apply transfer (![0, 1, 4, 3, 5, 2] : Fin 6 → Fin 6) (g := fun x => decide (∃ i j : Fin 6, (i.val+1)%6=j.val ∧ x i=true ∧ x j=true))
  · decide
  · intro s h
    have := (L106 6 s (by decide)).mp h
    omega

def cycleOrInput (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 3) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 4 && x 6)

theorem cycleOrInputLower : Bound cycleOrInput 9 := by
  apply one (k := 8) 3 false ⟨fun _ => false, by decide⟩ (by decide)
  · exact transfer (![0, 1, 2, 0, 3, 4, 5] : Fin 7 → Fin 6) (by decide) cycleSixLower
  · decide

def nonadjacentDeletions (x : Fin 8 → Bool) : Bool :=
  (x 1 && x 2) || (x 0 && x 4) || (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)

theorem nonadjacentDeletionsLower : Bound nonadjacentDeletions 11 := by
  apply split (k := 9) 0 ⟨point 4, by decide⟩ (by decide)
  intro b
  cases b
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6] : Fin 8 → Fin 7) (by decide) eightEdgeChildLower
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6] : Fin 8 → Fin 7) (by decide) cycleOrInputLower

def oneDeletion (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) || (x 1 && x 6) || (x 4 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)

theorem oneDeletionLower : Bound oneDeletion 13 := by
  apply fan (k := 11) ⟨point 1, by decide⟩ (by decide) (by decide)
  intro p
  fin_cases p
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6, 7] : Fin 9 → Fin 8) (by decide) adjacentDeletionsLower
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6, 7] : Fin 9 → Fin 8) (by decide) nonadjacentDeletionsLower
  · exact transfer (![1, 2, 0, 0, 5, 6, 7, 3, 4] : Fin 9 → Fin 8) (by decide) nonadjacentDeletionsLower
  · exact transfer (![0, 1, 2, 0, 4, 5, 6, 7, 3] : Fin 9 → Fin 8) (by decide) adjacentDeletionsLower
  · exact transfer (![0, 1, 6, 4, 0, 5, 2, 3, 7] : Fin 9 → Fin 8) (by decide) adjacentDeletionsLower
  · exact transfer (![0, 4, 6, 1, 5, 0, 7, 3, 2] : Fin 9 → Fin 8) (by decide) nonadjacentDeletionsLower
  · exact transfer (![2, 1, 6, 3, 0, 7, 0, 4, 5] : Fin 9 → Fin 8) (by decide) nonadjacentDeletionsLower
  · exact transfer (![1, 6, 3, 5, 0, 2, 4, 0, 7] : Fin 9 → Fin 8) (by decide) nonadjacentDeletionsLower
  · exact transfer (![1, 6, 4, 0, 5, 2, 3, 7, 0] : Fin 9 → Fin 8) (by decide) nonadjacentDeletionsLower

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 5 && x 7) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 4 && x 9) || (x 6 && x 9) || (x 7 && x 9)

theorem edgeFunctionLower : Bound edgeFunction 15 := by
  apply fan (k := 13) ⟨point 1, by decide⟩ (by decide) (by decide)
  intro p
  fin_cases p
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6, 7, 8] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![0, 0, 3, 2, 1, 5, 4, 8, 7, 6] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![1, 0, 0, 3, 2, 6, 5, 4, 8, 7] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![2, 1, 0, 0, 3, 7, 6, 5, 4, 8] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![0, 1, 2, 3, 0, 5, 6, 7, 8, 4] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![0, 1, 2, 7, 5, 0, 6, 3, 4, 8] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![1, 0, 5, 8, 6, 2, 0, 7, 3, 4] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![2, 1, 0, 5, 7, 3, 6, 0, 8, 4] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![2, 7, 5, 0, 1, 3, 4, 8, 0, 6] : Fin 10 → Fin 9) (by decide) oneDeletionLower
  · exact transfer (![1, 2, 7, 5, 0, 6, 3, 4, 8, 0] : Fin 10 → Fin 9) (by decide) oneDeletionLower

private def twoFree (x : Fin 8 → Bool) : Bool :=
  x 0 || cycleOrInput (fun i => x i.succ)

private theorem twoFreeLower : Bound twoFree 10 := by
  apply one (k := 9) 0 false ⟨fun _ => false, by decide⟩ (by decide)
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6] : Fin 8 → Fin 7) (by decide) cycleOrInputLower
  · decide

private def threeFree (x : Fin 9 → Bool) : Bool :=
  x 0 || twoFree (fun i => x i.succ)

private theorem threeFreeLower : Bound threeFree 11 := by
  apply one (k := 10) 0 false ⟨fun _ => false, by decide⟩ (by decide)
  · exact transfer (![0, 0, 1, 2, 3, 4, 5, 6, 7] : Fin 9 → Fin 8) (by decide) twoFreeLower
  · decide

theorem trueRestrictionLower : Bound (pin edgeFunction 0 true) 11 := by
  exact transfer (![0, 0, 2, 3, 1, 5, 6, 7, 8, 4] : Fin 10 → Fin 9) (by decide) threeFreeLower

open PEqualNP.CircuitLowerBounds

private def gate (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩

private def trueRestrictionCircuit : Circuit := ⟨[
  gate .or 3 7, gate .and 2 10, gate .or 3 6, gate .and 8 12,
  gate .or 6 7, gate .and 9 14, gate .or 1 4, gate .or 16 5,
  gate .or 17 11, gate .or 18 13, gate .or 19 15], 20⟩

theorem trueRestrictionUpper : HasCircuitSize 10 (pin edgeFunction 0 true) 11 := by
  refine ⟨trueRestrictionCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo,trueRestrictionCircuit,gate]
  · intro x
    have xs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := rfl
    unfold Circuit.eval Circuit.wires
    rw [xs]
    simp [trueRestrictionCircuit,gate,GateOp.eval,edgeFunction, pin, Function.update,List.getD]
    revert x
    decide

private def falseRestrictionCircuit : Circuit := ⟨[
  gate .or 2 6, gate .and 1 10, gate .or 2 4, gate .or 12 8,
  gate .and 3 13, gate .or 2 5, gate .or 15 9, gate .and 7 16,
  gate .or 5 6, gate .and 8 18, gate .or 4 6, gate .and 9 20,
  gate .or 11 14, gate .or 22 17, gate .or 23 19, gate .or 24 21], 25⟩

theorem falseRestrictionUpper : HasCircuitSize 10 (pin edgeFunction 0 false) 16 := by
  refine ⟨falseRestrictionCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo,falseRestrictionCircuit,gate]
  · intro x
    have xs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := rfl
    unfold Circuit.eval Circuit.wires
    rw [xs]
    simp [falseRestrictionCircuit,gate,GateOp.eval,edgeFunction, pin, Function.update,List.getD]
    revert x
    decide

private def fullCircuit : Circuit := ⟨[
  gate .or 1 4, gate .or 10 5, gate .and 0 11, gate .or 2 6,
  gate .and 1 13, gate .or 2 4, gate .or 15 8, gate .and 3 16,
  gate .or 2 5, gate .or 18 9, gate .and 7 19, gate .or 5 6,
  gate .and 8 21, gate .or 4 6, gate .and 9 23, gate .or 12 14,
  gate .or 25 17, gate .or 26 20, gate .or 27 22, gate .or 28 24], 29⟩

theorem fullUpper : HasCircuitSize 10 (edgeFunction) 20 := by
  refine ⟨fullCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo,fullCircuit,gate]
  · intro x
    have xs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := rfl
    unfold Circuit.eval Circuit.wires
    rw [xs]
    simp [fullCircuit,gate,GateOp.eval,edgeFunction,List.getD]
    revert x
    decide

-- The existing reader lemma requires that some vertex realizes one of three
-- savings patterns. The pattern (2,4) already holds at a hypothetical size 18.
theorem fanoutConclusionAtEighteen : Pays edgeFunction 0 18 :=
  Or.inr (Or.inr ⟨⟨16, by decide, falseRestrictionUpper⟩,
                   ⟨11, by decide, trueRestrictionUpper⟩⟩)

end PetersenElimination
