import PEqualNP.MetaComplexity.Helpers.Support
import Mathlib.Data.Fintype.Pi

namespace CyclicMatchings

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

-- Number the nine cross-products by matching, then by position in the matching.
def edge (x : Fin 6 → Bool) (i : Fin 9) : Bool :=
  match i.val with
  | 0 => x 0 && x 3
  | 1 => x 1 && x 4
  | 2 => x 2 && x 5
  | 3 => x 0 && x 4
  | 4 => x 1 && x 5
  | 5 => x 2 && x 3
  | 6 => x 0 && x 5
  | 7 => x 1 && x 3
  | _ => x 2 && x 4

def target (x : Fin 6 → Bool) (i : Fin 3) : Bool :=
  match i.val with
  | 0 => edge x 0 || edge x 1 || edge x 2
  | 1 => edge x 3 || edge x 4 || edge x 5
  | _ => edge x 6 || edge x 7 || edge x 8

private def gate (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩

def construction : Circuit := ⟨[
  gate .and 0 3, gate .and 1 4, gate .and 2 5,
  gate .and 0 4, gate .and 1 5, gate .and 2 3,
  gate .and 0 5, gate .and 1 3, gate .and 2 4,
  gate .or 6 7, gate .or 15 8,
  gate .or 9 10, gate .or 17 11,
  gate .or 12 13, gate .or 19 14], 16⟩

private def outputs (i : Fin 3) := 16 + 2*i.val

theorem upperBound : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 15 ∧
    ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool,
      (C.wires (List.ofFn x)).getD o0 false = target x 0 ∧
      (C.wires (List.ofFn x)).getD o1 false = target x 1 ∧
      (C.wires (List.ofFn x)).getD o2 false = target x 2 := by
  refine ⟨construction,?_,by decide,16,18,20,?_⟩
  · simp [FanInTwo,construction,gate]
  · have eval (x : Fin 6 → Bool) (i : Fin 3) :
        (construction.wires (List.ofFn x)).getD (outputs i) false = target x i := by
      revert x i
      decide
    exact fun x => ⟨eval x 0,eval x 1,eval x 2⟩

-- A twelve-gate solution for the promise that at most one bit is set on each
-- side. Three pairs of raw inputs contribute both an AND and an OR.
def sparseConstruction : Circuit := ⟨[
  gate .and 0 3, gate .or 0 3, gate .or 2 4, gate .and 2 4,
  gate .and 1 5, gate .or 1 5, gate .and 7 8, gate .and 7 11,
  gate .and 8 11, gate .or 10 12, gate .or 9 13, gate .or 6 14],17⟩

def sparse (x : Fin 6 → Bool) : Prop :=
  (∀ i j : Fin 3, x (Fin.castAdd 3 i) = true → x (Fin.castAdd 3 j) = true → i = j) ∧
  (∀ i j : Fin 3, x (Fin.natAdd 3 i) = true → x (Fin.natAdd 3 j) = true → i = j)

theorem sparseUpper : FanInTwo sparseConstruction ∧ sparseConstruction.size = 12 ∧
    ∀ x : Fin 6 → Bool, sparse x →
      (sparseConstruction.wires (List.ofFn x)).getD 17 false = target x 0 ∧
      (sparseConstruction.wires (List.ofFn x)).getD 15 false = target x 1 ∧
      (sparseConstruction.wires (List.ofFn x)).getD 16 false = target x 2 := by
  refine ⟨by simp [FanInTwo,sparseConstruction,gate], rfl, ?_⟩
  unfold sparse
  decide

theorem sparseFailure :
    let x := fun i : Fin 6 => decide (i.val = 4 ∨ i.val = 5)
    (sparseConstruction.wires (List.ofFn x)).getD 17 false ≠ target x 0 := by decide

def sideBit (left : Bool) (x : Fin 6 → Bool) (i : Fin 3) :=
  if left then x (Fin.castAdd 3 i) else x (Fin.natAdd 3 i)

-- Compare a single active edge with an input having just its exposed endpoint.
private theorem isolateFixed : ∀ (e : Fin 9) (left : Bool),
    ∃ (x y : Fin 6 → Bool) (o : Fin 3),
      (∀ i, sideBit left x i = sideBit left y i) ∧
      target x o ≠ target y o ∧ ∀ j : Fin 9, j ≠ e → edge x j = edge y j := by
  intro e left
  let row := e.val % 3
  let col := (row + e.val/3) % 3 + 3
  let x := fun i : Fin 6 => decide (i.val = row ∨ i.val = col)
  let y := fun i : Fin 6 => decide (i.val = (if left then row else col))
  refine ⟨x,y,⟨e.val/3,by have := e.isLt; omega⟩,?_⟩
  dsimp only [x,y,col,row]
  revert e left
  decide

-- A product input is tagged by its edge. An untagged input may be ANY function
-- of the exposed side, free of charge. The postprocessing circuit is unrestricted
-- apart from fan-in and the allowed AND/OR/NOT basis.
theorem oneSideLower {m} (left : Bool) (tag : Fin m → Option (Fin 9))
    (feed : (Fin 6 → Bool) → Fin m → Bool)
    (product : ∀ j e, tag j = some e → ∀ x, feed x j = edge x e)
    (oneSide : ∀ j, tag j = none → ∀ x y, (∀ i, sideBit left x i = sideBit left y i) →
      feed x j = feed y j)
    (C : Circuit) (ok : FanInTwo C) (out : Fin 3 → ℕ)
    (correct : ∀ x i, (C.wires (List.ofFn (feed x))).getD (out i) false = target x i) :
    9 ≤ ((Finset.univ.image tag).erase none).card ∧ 6 ≤ C.size ∧
      15 ≤ ((Finset.univ.image tag).erase none).card + C.size := by
  classical
  let W := Finset.univ.image out
  let S := W.biUnion (fun j => (suppsFrom C.gates (inputSupps m)).getD j ∅)
  have usedEdge (e : Fin 9) : some e ∈ S.image tag := by
    by_contra he
    obtain ⟨x,y,i,hs,hd,rest⟩ := isolateFixed e left
    apply hd
    rw [← correct x i, ← correct y i]
    apply (agree_wiresFrom (feed x) (feed y) C.gates _ _ _ (agree_inputs _ _)).2.2
    intro j hj
    cases h : tag j with
    | none => exact oneSide j h x y hs
    | some f =>
      have hin : j ∈ S := Finset.mem_biUnion.mpr
        ⟨out i,Finset.mem_image_of_mem out (Finset.mem_univ i),hj⟩
      have hf : f ≠ e := by
        intro eq
        apply he
        exact Finset.mem_image.mpr ⟨j,hin,h.trans (congrArg some eq)⟩
      rw [product j f h x,product j f h y]
      exact rest f hf
  let allEdges := Finset.univ.image (some : Fin 9 → Option (Fin 9))
  have count : allEdges.card = 9 := by simp [allEdges,Finset.card_image_of_injective _ (Option.some_injective (Fin 9))]
  have allUsed : allEdges ⊆ S.image tag := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
    exact usedEdge e
  have allComputed : allEdges ⊆ (Finset.univ.image tag).erase none := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (usedEdge e)
    exact Finset.mem_erase.mpr ⟨by simp,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩⟩
  have bound := cnt_suppsFrom C.gates 0 (inputSupps m) ok cnt_inputs W
  have cardW : W.card ≤ 3 := Finset.card_image_le.trans (by decide)
  change S.card ≤ 0+C.size+W.card at bound
  have hused := (Finset.card_le_card allUsed).trans Finset.card_image_le
  have hcomputed := Finset.card_le_card allComputed
  omega

end CyclicMatchings
