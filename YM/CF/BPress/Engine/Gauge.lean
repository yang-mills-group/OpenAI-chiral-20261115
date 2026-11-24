import YM.CF.BPress.Engine.Entry
import Mathlib.Analysis.Complex.CoveringMap
/-! Regular gauge scaling path. Keep chosen branch! Global only. For matrices primary need pose incl U.K.H velocities on all t, not just H last). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Engine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Spin.Stride Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story
open Scroll Spark Cube Lat SU Spin.Paint Skye Girt Scree Tulip Tenant Pf.RealBook RG Chalk Lily DoughBag Shot Till Store
open scoped Topology Matrix Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}{P:Form N D} [TopologicalSpace D] {A:Actor N D}{W:Pledge}{F:GramM N}{μ h ε r g q:ℝ}{U:Till P F}
namespace Actor
structure bodyG (V:Mach (More N))(A:Actor N D)(x y:D):Prop where
 s:A.seat x=A.seat y
 a: A.A y=twist (tradew N V) (A.A x)
 k:A.KG y = rotateC V (A.KG x)
 t:A.M y= twist (tradew N V) (A.M x)
end Actor
namespace Store
variable (G:Store P A W F h ε r g q μ U) (x y:D) (u:Pane N) (V:Mach (More N)) {α:ℝ}
lemma holdCov (X:Support N) (A: Paint (More N)): holdα X (rotateC V A)= acts (quant (tradew N V).val) (holdα X A):=by
 unfold holdα braC; rw [coupe_gauge, show pairWave (Fock.congrC (tradew N V) (coupling A))=_ from (pair_cov (tradew N V).val (coupling A)).symm,← act_mul,←act_mul]; let P:= tradew N V; have he(i:Bool): Commute P.val (cutM (Locks X i)):= (Bias.twist_C P|>.1 (Hole.terra_l i V)).symm; rw [← (Arrival.coexist (outage X) (he true) (he false)).eq] -- tune
include G
lemma regPad (s:ℝ) : paintR false false (tradew N V) (exp (weft (s:ℂ) (office F u)))= exp (weft (s:ℂ) (office F (gauge V u))):=by
 have he(i:Bool)(k:Scree.Hub N):∃ a v, PressB F.p k (βReg F i k) a v:= ⟨h,G.rit.p (i,k)⟩; let p:=tradew N V
 letI : NormedAlgebra ℚ (Cipher N):=NormedAlgebra.restrictScalars ℚ ℝ (Cipher N); rw [map_exp _ (spinM p),weft_r (x:=s),weft_r (x:=s),map_smul, office, office,map_add, traces _ F.F (he false), traces _ F.slip (he true)]
lemma regCompo (v : A.bodyG V x y)(t: ‖α‖ ≤1) :
 Complex.exp (∑ i:Support (More N), RegGas U A (α:ℂ) y (gauge V u) i) = Complex.exp (∑ i:Support (More N), RegGas U A (α:ℂ) x u i):=by
 have hv:=G.key x; have ht:= hv.drum.gap; obtain ⟨ω,h⟩:= Frame.pick ht.a; let p:=tradew N V; have hu: mood (A.A y) (A.M y)=twist p (mood (A.A x) (A.M x)):=by rw [v.a,v.t]; exact rotate_tilt hv.proj hv.she 1 p
 have he:=Frame.static p h; let L:= A.A; have hM:= (G.key x).proj; have hY:= (G.key y).proj; have ht: ‖(α:ℂ)‖ ≤1:= by simpa using t
 rw [← G.reg_expected x _ u ht ω h, ←G.reg_expected y _ (gauge V u) ht _ (hu.symm ▸ he)]
 let t:= exp (weft (α:ℂ) (office F u)); rw [←v.s,v.k, holdCov]; rw [←regPad G u V α,tank_eq (h:=hY), tank_eq (h:=hM), ←appleT hM hY false false p v.a.symm t]; exact Frame.bill_wick p _ -- tune v and Scroll
abbrev Sat_α:= ↥(Set.Icc (0:ℝ) 1)
lemma gaugeG (v:A.bodyG V x y) : (∑ i:Support (More N), RegGas U A 1 y (gauge V u) i) = ∑ i:Support (More N),RegGas U A 1 x u i := by
 let B(i:Sat_α):ℂ:= i.val; let f(x:D)(u:Pane N)(i:Sat_α) := ∑ s:Support (More N),RegGas U A (B i) x u s; have he (i:Sat_α):‖i.val‖≤1:=by rw [Real.norm_of_nonneg i.property.1]; exact i.property.2
 have ht (u:Pane N)(x) : Continuous (f x u):= continuous_finsetSum _ (fun j (_: _)=>G.νcont (clearF u) x (Complex.continuous_ofReal.comp continuous_subtype_val) (fun i=> (Complex.norm_real _).le.trans (he i)) (readyF u g G.Tclock.he) j)
 letI : PreconnectedSpace Sat_α:= isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
 let S(α:ℂ): {x:ℂ//x≠0}:= ⟨_, Complex.exp_ne_zero α⟩; have hp:S ∘ f y (gauge V u)=S ∘ f x u:= funext fun i=> Subtype.ext (G.regCompo x y u V v (he i))
 let J:Sat_α:=⟨0,by simp⟩; have hz (x u): f x u J=0:= by apply sum_eq_zero; intro i h; unfold B; simp only [J, Complex.ofReal_zero]; exact cold_base ..
 have hv:=Complex.isCoveringMap_exp.eq_of_comp_eq (ht (gauge V u) y) (ht u x) hp J ((hz ..).trans (hz ..).symm); let F:Sat_α:=⟨1,by simp⟩; rw [← (show B F= 1 from by simp [B,F])]; exact congrFun hv F
end Store
end YM.CF.BPress.Engine
