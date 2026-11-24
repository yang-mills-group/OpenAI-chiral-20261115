import SatinStress.U1.Derivative

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

def frequency := Chart.s

def tRow : List (FPol × Sy) :=
  ([()] : List FPol).flatMap (fun i => TT.en.map (fun k => (i,k)))
theorem tRow_all (x : FPol × Sy) : x ∈ tRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : FPol, i ∈ ([()] : List FPol) from by
           intro i; cases i; simp) x.1, List.mem_map.mpr ⟨_, TT.all x.2,rfl⟩⟩

def wRow : List (FPol × Axis) :=
  ([()] : List FPol).flatMap (fun i => W.en.map (fun k => (i,k)))
theorem wRow_all (x : FPol × Axis) : x ∈ wRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : FPol, i ∈ ([()] : List FPol) from by
           intro i; cases i; simp) x.1, List.mem_map.mpr ⟨_, W.all x.2,rfl⟩⟩

def vRow : List (FPol × VSy) :=
  ([()] : List FPol).flatMap (fun i => V.en.map (fun k => (i,k)))
theorem vRow_all (x : FPol × VSy) : x ∈ vRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : FPol, i ∈ ([()] : List FPol) from by
           intro i; cases i; simp) x.1, List.mem_map.mpr ⟨_, V.all x.2,rfl⟩⟩

def doubleRow : List (FPol × Axis × Axis) :=
  ([()] : List FPol).flatMap (fun i => (Schedule.vector.prod Schedule.vector 4).en.map (fun k => (i,k)))
theorem doubleRow_all (x : FPol × Axis × Axis) : x ∈ doubleRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : FPol, i ∈ ([()] : List FPol) from by
           intro i; cases i; simp) x.1, List.mem_map.mpr ⟨_, (Schedule.vector.prod Schedule.vector 4).all x.2,rfl⟩⟩

def traceRow : List (FPol × Unit) :=
  ([()] : List FPol).flatMap (fun i => Schedule.unit.en.map (fun k => (i,k)))
theorem traceRow_all (x : FPol × Unit) : x ∈ traceRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : FPol, i ∈ ([()] : List FPol) from by
           intro i; cases i; simp) x.1, List.mem_map.mpr ⟨_, Schedule.unit.all x.2,rfl⟩⟩

def t1Source : F4 × Sy := ((0,.inl 0),Duo.sym 0 0)
def t1 := ph4.column TT t1Source

def t2Source : F4 × Sy := ((0,.inl 0),Duo.sym 1 1)
def t2 := ph4.column TT t2Source

def t3Source : F4 × Sy := ((0,.inl 1),Duo.sym 0 1)
def t3 := ph4.column TT t3Source

def colsTID : List (F4 × Sy) :=
  [t1Source, t2Source, t3Source]
def colsT : List (Raw (FPol × Sy)) :=
  [t1, t2, t3]
lemma mapped_T : colsTID.map (ph4.column TT)=colsT := rfl

def w1Source : F5 × Axis := ((0,.inr (.inl (0,0))),0)
def w1 := ph5.column W w1Source

def w2Source : F5 × Axis := ((0,.inr (.inl (0,1))),1)
def w2 := ph5.column W w2Source

def w3Source : F5 × Axis := ((0,.inr (.inl (1,0))),1)
def w3 := ph5.column W w3Source

def w4Source : F5 × Axis := ((0,.inr (.inl (1,1))),0)
def w4 := ph5.column W w4Source

def colsWID : List (F5 × Axis) :=
  [w1Source, w2Source, w3Source, w4Source]
def colsW : List (Raw (FPol × Axis)) :=
  [w1, w2, w3, w4]
lemma mapped_W : colsWID.map (ph5.column W)=colsW := rfl

def v1Source : F5 × VSy := ((0,.inl (Duo.sym 0 1)),(2,Duo.sym 0 3))
def v1 := ph5.column V v1Source

def v2Source : F5 × VSy := ((0,.inl (Duo.sym 1 1)),(2,Duo.sym 1 3))
def v2 := ph5.column V v2Source

def v3Source : F5 × VSy := ((0,.inl (Duo.sym 1 2)),(1,Duo.sym 1 3))
def v3 := ph5.column V v3Source

def v4Source : F5 × VSy := ((0,.inl (Duo.sym 1 2)),(3,Duo.sym 1 1))
def v4 := ph5.column V v4Source

def v5Source : F5 × VSy := ((0,.inr (.inl (0,0))),(0,Duo.sym 0 0))
def v5 := ph5.column V v5Source

def v6Source : F5 × VSy := ((0,.inr (.inl (0,0))),(0,Duo.sym 1 1))
def v6 := ph5.column V v6Source

def v7Source : F5 × VSy := ((0,.inr (.inl (0,0))),(1,Duo.sym 0 1))
def v7 := ph5.column V v7Source

def v8Source : F5 × VSy := ((0,.inr (.inl (0,1))),(0,Duo.sym 0 1))
def v8 := ph5.column V v8Source

def v9Source : F5 × VSy := ((0,.inr (.inl (0,1))),(1,Duo.sym 0 0))
def v9 := ph5.column V v9Source

def v10Source : F5 × VSy := ((0,.inr (.inl (0,1))),(1,Duo.sym 1 1))
def v10 := ph5.column V v10Source

def v11Source : F5 × VSy := ((0,.inr (.inl (0,1))),(1,Duo.sym 2 2))
def v11 := ph5.column V v11Source

def v12Source : F5 × VSy := ((0,.inr (.inl (0,1))),(2,Duo.sym 1 2))
def v12 := ph5.column V v12Source

def v13Source : F5 × VSy := ((0,.inr (.inr (Duo.sym 0 1))),(2,Duo.sym 0 3))
def v13 := ph5.column V v13Source

def v14Source : F5 × VSy := ((0,.inr (.inl (1,0))),(0,Duo.sym 0 1))
def v14 := ph5.column V v14Source

def v15Source : F5 × VSy := ((0,.inr (.inl (1,0))),(1,Duo.sym 0 0))
def v15 := ph5.column V v15Source

def v16Source : F5 × VSy := ((0,.inr (.inl (1,0))),(1,Duo.sym 1 1))
def v16 := ph5.column V v16Source

def v17Source : F5 × VSy := ((0,.inr (.inl (1,0))),(1,Duo.sym 2 2))
def v17 := ph5.column V v17Source

def v18Source : F5 × VSy := ((0,.inr (.inl (1,0))),(2,Duo.sym 1 2))
def v18 := ph5.column V v18Source

def v19Source : F5 × VSy := ((0,.inr (.inl (1,1))),(0,Duo.sym 0 0))
def v19 := ph5.column V v19Source

def v20Source : F5 × VSy := ((0,.inr (.inl (1,1))),(0,Duo.sym 1 1))
def v20 := ph5.column V v20Source

def v21Source : F5 × VSy := ((0,.inr (.inl (1,1))),(0,Duo.sym 2 2))
def v21 := ph5.column V v21Source

def v22Source : F5 × VSy := ((0,.inr (.inl (1,1))),(1,Duo.sym 0 1))
def v22 := ph5.column V v22Source

def v23Source : F5 × VSy := ((0,.inr (.inl (1,1))),(2,Duo.sym 0 2))
def v23 := ph5.column V v23Source

def v24Source : F5 × VSy := ((0,.inr (.inl (1,2))),(0,Duo.sym 1 2))
def v24 := ph5.column V v24Source

def v25Source : F5 × VSy := ((0,.inr (.inl (1,2))),(1,Duo.sym 0 2))
def v25 := ph5.column V v25Source

def v26Source : F5 × VSy := ((0,.inr (.inl (1,2))),(2,Duo.sym 0 1))
def v26 := ph5.column V v26Source

def v27Source : F5 × VSy := ((0,.inr (.inr (Duo.sym 1 1))),(2,Duo.sym 1 3))
def v27 := ph5.column V v27Source

def v28Source : F5 × VSy := ((0,.inr (.inr (Duo.sym 1 2))),(1,Duo.sym 1 3))
def v28 := ph5.column V v28Source

def v29Source : F5 × VSy := ((0,.inr (.inr (Duo.sym 1 2))),(3,Duo.sym 1 1))
def v29 := ph5.column V v29Source

def colsVID : List (F5 × VSy) :=
  [v1Source, v2Source, v3Source, v4Source, v5Source, v6Source, v7Source, v8Source, v9Source, v10Source, v11Source, v12Source, v13Source, v14Source, v15Source, v16Source, v17Source, v18Source, v19Source, v20Source, v21Source, v22Source, v23Source, v24Source, v25Source, v26Source, v27Source, v28Source, v29Source]
def colsV : List (Raw (FPol × VSy)) :=
  [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29]
lemma mapped_V : colsVID.map (ph5.column V)=colsV := rfl
def colsTPiv : List ℕ :=
  [1, 3]
lemma pick_T :
    pick colsTPiv 1 colsT = [t1, t3] := rfl
def colsWPiv : List ℕ :=
  [1]
lemma pick_W :
    pick colsWPiv 1 colsW = [w1] := rfl
def colsVPiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 24, 26]
lemma pick_V :
    pick colsVPiv 1 colsV = [v1, v2, v3, v4, v5, v6, v7, v8, v9, v13, v14, v15, v24, v26] := rfl
def trace1 := rawTrace t1
def trace2 := rawTrace t3

def colsTrace : List (Raw (FPol × Unit)) :=
  [trace1, trace2]
def colsTracePiv : List ℕ :=
  []
lemma pick_trace :
    pick colsTracePiv 1 colsTrace = [] := rfl
def d1 := rawDiv frequency t1
def d2 := rawDiv frequency t3

def colsD : List (Raw (FPol × Axis)) :=
  [d1, d2]
def colsDPiv : List ℕ :=
  [1]
lemma pick_D :
    pick colsDPiv 1 colsD = [d1] := rfl
def double1 := rawW frequency w1
def double2 := rawV frequency v1
def double3 := rawV frequency v2
def double4 := rawV frequency v3
def double5 := rawV frequency v4
def double6 := rawV frequency v5
def double7 := rawV frequency v6
def double8 := rawV frequency v7
def double9 := rawV frequency v8
def double10 := rawV frequency v9
def double11 := rawV frequency v13
def double12 := rawV frequency v14
def double13 := rawV frequency v15
def double14 := rawV frequency v24
def double15 := rawV frequency v26

def colsDouble : List (Raw (FPol × Axis × Axis)) :=
  [double1, double2, double3, double4, double5, double6, double7, double8, double9, double10, double11, double12, double13, double14, double15]
def colsDoublePiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15]
lemma pick_double :
    pick colsDoublePiv 1 colsDouble = [double1, double2, double3, double4, double5, double6, double7, double8, double9, double10, double11, double12, double15] := rfl
def lands1 := w1
def lands2 := d1
def lands3 := d2

def colsLands : List (Raw (FPol × Axis)) :=
  [lands1, lands2, lands3]
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
def grad7 := v7
def grad8 := v8
def grad9 := v9
def grad10 := v13
def grad11 := v14
def grad12 := v15
def grad13 := v24
def grad14 := v26
def grad15 := rawT frequency t1
def grad16 := rawT frequency t3

def colsGrad : List (Raw (FPol × VSy)) :=
  [grad1, grad2, grad3, grad4, grad5, grad6, grad7, grad8, grad9, grad10, grad11, grad12, grad13, grad14, grad15, grad16]
def colsGradPiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
lemma pick_grad :
    pick colsGradPiv 1 colsGrad = [grad1, grad2, grad3, grad4, grad5, grad6, grad7, grad8, grad9, grad10, grad11, grad12, grad13, grad14] := rfl

end SatinStress.U1.Certificate.F
