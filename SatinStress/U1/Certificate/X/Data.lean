import SatinStress.U1.Derivative

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.X
open Radix Raw Class Derivative

def frequency := Chart.t
def b0_1 : Blade := ⟨(0, 1), by decide⟩
def b0_2 : Blade := ⟨(0, 2), by decide⟩
def b0_3 : Blade := ⟨(0, 3), by decide⟩
def b1_2 : Blade := ⟨(1, 2), by decide⟩
def b1_3 : Blade := ⟨(1, 3), by decide⟩
def b2_3 : Blade := ⟨(2, 3), by decide⟩

def tRow : List (XPol × Sy) :=
  ([0,1] : List XPol).flatMap (fun i => TT.en.map (fun k => (i,k)))
theorem tRow_all (x : XPol × Sy) : x ∈ tRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : XPol, i ∈ ([0,1] : List XPol) from by
           intro i; fin_cases i <;> decide) x.1, List.mem_map.mpr ⟨_, TT.all x.2,rfl⟩⟩

def wRow : List (XPol × Axis) :=
  ([0,1] : List XPol).flatMap (fun i => W.en.map (fun k => (i,k)))
theorem wRow_all (x : XPol × Axis) : x ∈ wRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : XPol, i ∈ ([0,1] : List XPol) from by
           intro i; fin_cases i <;> decide) x.1, List.mem_map.mpr ⟨_, W.all x.2,rfl⟩⟩

def vRow : List (XPol × VSy) :=
  ([0,1] : List XPol).flatMap (fun i => V.en.map (fun k => (i,k)))
theorem vRow_all (x : XPol × VSy) : x ∈ vRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : XPol, i ∈ ([0,1] : List XPol) from by
           intro i; fin_cases i <;> decide) x.1, List.mem_map.mpr ⟨_, V.all x.2,rfl⟩⟩

def doubleRow : List (XPol × Axis × Axis) :=
  ([0,1] : List XPol).flatMap (fun i => (Schedule.vector.prod Schedule.vector 4).en.map (fun k => (i,k)))
theorem doubleRow_all (x : XPol × Axis × Axis) : x ∈ doubleRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : XPol, i ∈ ([0,1] : List XPol) from by
           intro i; fin_cases i <;> decide) x.1, List.mem_map.mpr ⟨_, (Schedule.vector.prod Schedule.vector 4).all x.2,rfl⟩⟩

def traceRow : List (XPol × Unit) :=
  ([0,1] : List XPol).flatMap (fun i => Schedule.unit.en.map (fun k => (i,k)))
theorem traceRow_all (x : XPol × Unit) : x ∈ traceRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : XPol, i ∈ ([0,1] : List XPol) from by
           intro i; fin_cases i <;> decide) x.1, List.mem_map.mpr ⟨_, Schedule.unit.all x.2,rfl⟩⟩

def colsTID : List (Empty × Sy) :=
  []
def colsT : List (Raw (XPol × Sy)) :=
  []
lemma mapped_T : colsTID.map (mixed4.column TT)=colsT := rfl

def w1Source : X5 × Axis := ((0,b0_1),1)
def w1 := mixed.column W w1Source

def colsWID : List (X5 × Axis) :=
  [w1Source]
def colsW : List (Raw (XPol × Axis)) :=
  [w1]
lemma mapped_W : colsWID.map (mixed.column W)=colsW := rfl

def v1Source : X5 × VSy := ((0,b0_1),(0,Duo.sym 0 1))
def v1 := mixed.column V v1Source

def v2Source : X5 × VSy := ((0,b0_1),(1,Duo.sym 0 0))
def v2 := mixed.column V v2Source

def v3Source : X5 × VSy := ((0,b0_1),(1,Duo.sym 1 1))
def v3 := mixed.column V v3Source

def v4Source : X5 × VSy := ((0,b0_1),(1,Duo.sym 2 2))
def v4 := mixed.column V v4Source

def v5Source : X5 × VSy := ((0,b0_1),(2,Duo.sym 1 2))
def v5 := mixed.column V v5Source

def v6Source : X5 × VSy := ((0,b1_2),(1,Duo.sym 0 2))
def v6 := mixed.column V v6Source

def colsVID : List (X5 × VSy) :=
  [v1Source, v2Source, v3Source, v4Source, v5Source, v6Source]
def colsV : List (Raw (XPol × VSy)) :=
  [v1, v2, v3, v4, v5, v6]
lemma mapped_V : colsVID.map (mixed.column V)=colsV := rfl
def colsTPiv : List ℕ :=
  []
lemma pick_T :
    pick colsTPiv 1 colsT = [] := rfl
def colsWPiv : List ℕ :=
  [1]
lemma pick_W :
    pick colsWPiv 1 colsW = [w1] := rfl
def colsVPiv : List ℕ :=
  [1, 2, 3, 4, 5, 6]
lemma pick_V :
    pick colsVPiv 1 colsV = [v1, v2, v3, v4, v5, v6] := rfl

def colsTrace : List (Raw (XPol × Unit)) :=
  []
def colsTracePiv : List ℕ :=
  []
lemma pick_trace :
    pick colsTracePiv 1 colsTrace = [] := rfl

def colsD : List (Raw (XPol × Axis)) :=
  []
def colsDPiv : List ℕ :=
  []
lemma pick_D :
    pick colsDPiv 1 colsD = [] := rfl
def double1 := rawW frequency w1
def double2 := rawV frequency v1
def double3 := rawV frequency v2
def double4 := rawV frequency v3
def double5 := rawV frequency v4
def double6 := rawV frequency v5
def double7 := rawV frequency v6

def colsDouble : List (Raw (XPol × Axis × Axis)) :=
  [double1, double2, double3, double4, double5, double6, double7]
def colsDoublePiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7]
lemma pick_double :
    pick colsDoublePiv 1 colsDouble = [double1, double2, double3, double4, double5, double6, double7] := rfl
def lands1 := w1

def colsLands : List (Raw (XPol × Axis)) :=
  [lands1]
def colsLandsPiv : List ℕ :=
  [1]
lemma pick_lands :
    pick colsLandsPiv 1 colsLands = [lands1] := rfl
def grad1 := v1
def grad2 := v2
def grad3 := v3
def grad4 := v4
def grad5 := v5
def grad6 := v6

def colsGrad : List (Raw (XPol × VSy)) :=
  [grad1, grad2, grad3, grad4, grad5, grad6]
def colsGradPiv : List ℕ :=
  [1, 2, 3, 4, 5, 6]
lemma pick_grad :
    pick colsGradPiv 1 colsGrad = [grad1, grad2, grad3, grad4, grad5, grad6] := rfl

end SatinStress.U1.Certificate.X
