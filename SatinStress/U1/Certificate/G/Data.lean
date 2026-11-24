import SatinStress.U1.Derivative

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

def frequency := Chart.s
def b0_1 : Blade := ⟨(0, 1), by decide⟩
def b0_2 : Blade := ⟨(0, 2), by decide⟩
def b0_3 : Blade := ⟨(0, 3), by decide⟩
def b1_2 : Blade := ⟨(1, 2), by decide⟩
def b1_3 : Blade := ⟨(1, 3), by decide⟩
def b2_3 : Blade := ⟨(2, 3), by decide⟩

def tRow : List (GPol × Sy) :=
  ([(0,0),(0,1),(1,0),(1,1)] : List GPol).flatMap (fun i => TT.en.map (fun k => (i,k)))
theorem tRow_all (x : GPol × Sy) : x ∈ tRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : GPol, i ∈ ([(0,0),(0,1),(1,0),(1,1)] : List GPol) from by
           intro i; rcases i with ⟨p,q⟩; fin_cases p <;> fin_cases q <;> decide) x.1, List.mem_map.mpr ⟨_, TT.all x.2,rfl⟩⟩

def wRow : List (GPol × Axis) :=
  ([(0,0),(0,1),(1,0),(1,1)] : List GPol).flatMap (fun i => W.en.map (fun k => (i,k)))
theorem wRow_all (x : GPol × Axis) : x ∈ wRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : GPol, i ∈ ([(0,0),(0,1),(1,0),(1,1)] : List GPol) from by
           intro i; rcases i with ⟨p,q⟩; fin_cases p <;> fin_cases q <;> decide) x.1, List.mem_map.mpr ⟨_, W.all x.2,rfl⟩⟩

def vRow : List (GPol × VSy) :=
  ([(0,0),(0,1),(1,0),(1,1)] : List GPol).flatMap (fun i => V.en.map (fun k => (i,k)))
theorem vRow_all (x : GPol × VSy) : x ∈ vRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : GPol, i ∈ ([(0,0),(0,1),(1,0),(1,1)] : List GPol) from by
           intro i; rcases i with ⟨p,q⟩; fin_cases p <;> fin_cases q <;> decide) x.1, List.mem_map.mpr ⟨_, V.all x.2,rfl⟩⟩

def doubleRow : List (GPol × Axis × Axis) :=
  ([(0,0),(0,1),(1,0),(1,1)] : List GPol).flatMap (fun i => (Schedule.vector.prod Schedule.vector 4).en.map (fun k => (i,k)))
theorem doubleRow_all (x : GPol × Axis × Axis) : x ∈ doubleRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : GPol, i ∈ ([(0,0),(0,1),(1,0),(1,1)] : List GPol) from by
           intro i; rcases i with ⟨p,q⟩; fin_cases p <;> fin_cases q <;> decide) x.1, List.mem_map.mpr ⟨_, (Schedule.vector.prod Schedule.vector 4).all x.2,rfl⟩⟩

def traceRow : List (GPol × Unit) :=
  ([(0,0),(0,1),(1,0),(1,1)] : List GPol).flatMap (fun i => Schedule.unit.en.map (fun k => (i,k)))
theorem traceRow_all (x : GPol × Unit) : x ∈ traceRow :=
  List.mem_flatMap.mpr
    ⟨_, (show ∀ i : GPol, i ∈ ([(0,0),(0,1),(1,0),(1,1)] : List GPol) from by
           intro i; rcases i with ⟨p,q⟩; fin_cases p <;> fin_cases q <;> decide) x.1, List.mem_map.mpr ⟨_, Schedule.unit.all x.2,rfl⟩⟩

def t1Source : G4 × Sy := (Duo.sym b0_1 b0_1,Duo.sym 0 0)
def t1 := ge4.column TT t1Source

def t2Source : G4 × Sy := (Duo.sym b0_1 b0_1,Duo.sym 2 2)
def t2 := ge4.column TT t2Source

def t3Source : G4 × Sy := (Duo.sym b0_1 b0_2,Duo.sym 1 2)
def t3 := ge4.column TT t3Source

def colsTID : List (G4 × Sy) :=
  [t1Source, t2Source, t3Source]
def colsT : List (Raw (GPol × Sy)) :=
  [t1, t2, t3]
lemma mapped_T : colsTID.map (ge4.column TT)=colsT := rfl

def w1Source : G5 × Axis := ((b0_1,b0_1,0),0)
def w1 := ge5.column W w1Source

def w2Source : G5 × Axis := ((b0_1,b0_1,2),2)
def w2 := ge5.column W w2Source

def w3Source : G5 × Axis := ((b0_1,b0_2,1),2)
def w3 := ge5.column W w3Source

def w4Source : G5 × Axis := ((b0_1,b0_2,2),1)
def w4 := ge5.column W w4Source

def colsWID : List (G5 × Axis) :=
  [w1Source, w2Source, w3Source, w4Source]
def colsW : List (Raw (GPol × Axis)) :=
  [w1, w2, w3, w4]
lemma mapped_W : colsWID.map (ge5.column W)=colsW := rfl

def v1Source : G5 × VSy := ((b0_1,b0_1,0),(0,Duo.sym 0 0))
def v1 := ge5.column V v1Source

def v2Source : G5 × VSy := ((b0_1,b0_1,0),(0,Duo.sym 1 1))
def v2 := ge5.column V v2Source

def v3Source : G5 × VSy := ((b0_1,b0_1,0),(0,Duo.sym 2 2))
def v3 := ge5.column V v3Source

def v4Source : G5 × VSy := ((b0_1,b0_1,0),(1,Duo.sym 0 1))
def v4 := ge5.column V v4Source

def v5Source : G5 × VSy := ((b0_1,b0_1,0),(2,Duo.sym 0 2))
def v5 := ge5.column V v5Source

def v6Source : G5 × VSy := ((b0_1,b0_1,2),(0,Duo.sym 0 2))
def v6 := ge5.column V v6Source

def v7Source : G5 × VSy := ((b0_1,b0_1,2),(2,Duo.sym 0 0))
def v7 := ge5.column V v7Source

def v8Source : G5 × VSy := ((b0_1,b0_1,2),(2,Duo.sym 2 2))
def v8 := ge5.column V v8Source

def v9Source : G5 × VSy := ((b0_1,b0_1,2),(2,Duo.sym 3 3))
def v9 := ge5.column V v9Source

def v10Source : G5 × VSy := ((b0_1,b0_1,2),(3,Duo.sym 2 3))
def v10 := ge5.column V v10Source

def v11Source : G5 × VSy := ((b0_1,b0_2,0),(0,Duo.sym 1 2))
def v11 := ge5.column V v11Source

def v12Source : G5 × VSy := ((b0_1,b0_2,0),(1,Duo.sym 0 2))
def v12 := ge5.column V v12Source

def v13Source : G5 × VSy := ((b0_1,b0_2,0),(2,Duo.sym 0 1))
def v13 := ge5.column V v13Source

def v14Source : G5 × VSy := ((b0_1,b0_2,1),(0,Duo.sym 0 2))
def v14 := ge5.column V v14Source

def v15Source : G5 × VSy := ((b0_1,b0_2,1),(1,Duo.sym 1 2))
def v15 := ge5.column V v15Source

def v16Source : G5 × VSy := ((b0_1,b0_2,1),(2,Duo.sym 0 0))
def v16 := ge5.column V v16Source

def v17Source : G5 × VSy := ((b0_1,b0_2,1),(2,Duo.sym 1 1))
def v17 := ge5.column V v17Source

def v18Source : G5 × VSy := ((b0_1,b0_2,1),(2,Duo.sym 2 2))
def v18 := ge5.column V v18Source

def v19Source : G5 × VSy := ((b0_1,b0_2,1),(2,Duo.sym 3 3))
def v19 := ge5.column V v19Source

def v20Source : G5 × VSy := ((b0_1,b0_2,1),(3,Duo.sym 2 3))
def v20 := ge5.column V v20Source

def v21Source : G5 × VSy := ((b0_1,b0_2,2),(0,Duo.sym 0 1))
def v21 := ge5.column V v21Source

def v22Source : G5 × VSy := ((b0_1,b0_2,2),(1,Duo.sym 0 0))
def v22 := ge5.column V v22Source

def v23Source : G5 × VSy := ((b0_1,b0_2,2),(1,Duo.sym 1 1))
def v23 := ge5.column V v23Source

def v24Source : G5 × VSy := ((b0_1,b0_2,2),(1,Duo.sym 2 2))
def v24 := ge5.column V v24Source

def v25Source : G5 × VSy := ((b0_1,b0_2,2),(1,Duo.sym 3 3))
def v25 := ge5.column V v25Source

def v26Source : G5 × VSy := ((b0_1,b0_2,2),(2,Duo.sym 1 2))
def v26 := ge5.column V v26Source

def v27Source : G5 × VSy := ((b0_1,b0_2,2),(3,Duo.sym 1 3))
def v27 := ge5.column V v27Source

def v28Source : G5 × VSy := ((b0_1,b0_2,3),(1,Duo.sym 2 3))
def v28 := ge5.column V v28Source

def v29Source : G5 × VSy := ((b0_1,b0_2,3),(2,Duo.sym 1 3))
def v29 := ge5.column V v29Source

def v30Source : G5 × VSy := ((b0_1,b0_2,3),(3,Duo.sym 1 2))
def v30 := ge5.column V v30Source

def v31Source : G5 × VSy := ((b0_1,b2_3,0),(2,Duo.sym 1 3))
def v31 := ge5.column V v31Source

def v32Source : G5 × VSy := ((b0_1,b2_3,2),(0,Duo.sym 1 3))
def v32 := ge5.column V v32Source

def colsVID : List (G5 × VSy) :=
  [v1Source, v2Source, v3Source, v4Source, v5Source, v6Source, v7Source, v8Source, v9Source, v10Source, v11Source, v12Source, v13Source, v14Source, v15Source, v16Source, v17Source, v18Source, v19Source, v20Source, v21Source, v22Source, v23Source, v24Source, v25Source, v26Source, v27Source, v28Source, v29Source, v30Source, v31Source, v32Source]
def colsV : List (Raw (GPol × VSy)) :=
  [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32]
lemma mapped_V : colsVID.map (ge5.column V)=colsV := rfl
def colsTPiv : List ℕ :=
  [1, 2, 3]
lemma pick_T :
    pick colsTPiv 1 colsT = [t1, t2, t3] := rfl
def colsWPiv : List ℕ :=
  [1, 2]
lemma pick_W :
    pick colsWPiv 1 colsW = [w1, w2] := rfl
def colsVPiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 24, 26, 28, 29, 30]
lemma pick_V :
    pick colsVPiv 1 colsV = [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v16, v24, v26, v28, v29, v30] := rfl
def trace1 := rawTrace t1
def trace2 := rawTrace t2
def trace3 := rawTrace t3

def colsTrace : List (Raw (GPol × Unit)) :=
  [trace1, trace2, trace3]
def colsTracePiv : List ℕ :=
  [1]
lemma pick_trace :
    pick colsTracePiv 1 colsTrace = [trace1] := rfl
def d1 := rawDiv frequency t1
def d2 := rawDiv frequency t2
def d3 := rawDiv frequency t3

def colsD : List (Raw (GPol × Axis)) :=
  [d1, d2, d3]
def colsDPiv : List ℕ :=
  [1, 2]
lemma pick_D :
    pick colsDPiv 1 colsD = [d1, d2] := rfl
def double1 := rawW frequency w1
def double2 := rawW frequency w2
def double3 := rawV frequency v1
def double4 := rawV frequency v2
def double5 := rawV frequency v3
def double6 := rawV frequency v4
def double7 := rawV frequency v5
def double8 := rawV frequency v6
def double9 := rawV frequency v7
def double10 := rawV frequency v8
def double11 := rawV frequency v9
def double12 := rawV frequency v10
def double13 := rawV frequency v11
def double14 := rawV frequency v12
def double15 := rawV frequency v13
def double16 := rawV frequency v14
def double17 := rawV frequency v16
def double18 := rawV frequency v24
def double19 := rawV frequency v26
def double20 := rawV frequency v28
def double21 := rawV frequency v29
def double22 := rawV frequency v30

def colsDouble : List (Raw (GPol × Axis × Axis)) :=
  [double1, double2, double3, double4, double5, double6, double7, double8, double9, double10, double11, double12, double13, double14, double15, double16, double17, double18, double19, double20, double21, double22]
def colsDoublePiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
lemma pick_double :
    pick colsDoublePiv 1 colsDouble = [double1, double2, double3, double4, double5, double6, double7, double8, double10, double12, double13, double14, double15, double16, double17, double18, double19, double20, double21] := rfl
def lands1 := w1
def lands2 := w2
def lands3 := d1
def lands4 := d2
def lands5 := d3

def colsLands : List (Raw (GPol × Axis)) :=
  [lands1, lands2, lands3, lands4, lands5]
def colsLandsPiv : List ℕ :=
  [1, 2]
lemma pick_lands :
    pick colsLandsPiv 1 colsLands = [lands1, lands2] := rfl
def grad1 := v1
def grad2 := v2
def grad3 := v3
def grad4 := v4
def grad5 := v5
def grad6 := v6
def grad7 := v7
def grad8 := v8
def grad9 := v9
def grad10 := v10
def grad11 := v11
def grad12 := v12
def grad13 := v13
def grad14 := v14
def grad15 := v16
def grad16 := v24
def grad17 := v26
def grad18 := v28
def grad19 := v29
def grad20 := v30
def grad21 := rawT frequency t1
def grad22 := rawT frequency t2
def grad23 := rawT frequency t3

def colsGrad : List (Raw (GPol × VSy)) :=
  [grad1, grad2, grad3, grad4, grad5, grad6, grad7, grad8, grad9, grad10, grad11, grad12, grad13, grad14, grad15, grad16, grad17, grad18, grad19, grad20, grad21, grad22, grad23]
def colsGradPiv : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
lemma pick_grad :
    pick colsGradPiv 1 colsGrad = [grad1, grad2, grad3, grad4, grad5, grad6, grad7, grad8, grad9, grad10, grad11, grad12, grad13, grad14, grad15, grad16, grad17, grad18, grad19, grad20] := rfl

end SatinStress.U1.Certificate.G
