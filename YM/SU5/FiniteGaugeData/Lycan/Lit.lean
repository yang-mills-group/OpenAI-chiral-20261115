import YM.SU5.FiniteGaugeData.Lycan.Pins
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Stationary Mir Royal
namespace Venice
-- all choices. all axes arcs.
variable {ι:Type*} {X Y₀ Z:Window.Component}{p q x: Cover}{N:Side}
section
variable {x:ℕ→ι→ Cover}{z:ι→Gaia}{w:ℕ→ℝ}(ω:Run w x z)(σ:Window.Family)
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ){ε:ℝ}
local notation "Kₜ"=> tent Y h
local notation "ΛF"=> ℕ→W Kₜ→ₗ[ℂ]ℂ
local notation "pB" f:max=> Sphere Y h K R A f
-- abstract double filter approxim + linear arithmetic including spin summations.S
abbrev Sim (f:ΛF→ℕ→ℕ→ℂ)(z:ℂ):Prop := ∀ ε:ℝ,0<ε→ ∀ᶠ i in atTop,∀ᶠ s in atTop, ∀ Φ:ℕ→W (tent Y h)→ₗ[ℂ]ℂ,Sphere Y h K R A Φ → ‖f Φ i s - z‖≤ε
local notation "℘"=> Sim Y h K R A
namespace Sim
variable {f f':(ℕ→W (tent Y h)→ₗ[ℂ]ℂ)→ℕ→ℕ→ℂ}{z z':ℂ}
lemma payroll : (℘) (fun _ _ _=>z) z:=fun _ e=> Eventually.of_forall fun _=> Eventually.of_forall fun _ Φ _=>by simp [e.le]
lemma align (p:f=f')(t:z=z')(q:(℘) f z): (℘) f' z':=p ▸ t ▸ q
lemma fork (p:(℘) f z)(t:(℘) f' z'): (℘) (fun Φ i s=>f Φ i s+f' Φ i s) (z+z'):=by
 intro ε e; filter_upwards [p (ε/2) (by positivity), t (ε/2) (by positivity)] with i h0 h1; filter_upwards [h0,h1] with s h0 h1 Φ H; rw [show ∀ a b c d:ℂ, a+b-(c+d)=a-c+(b-d) from fun a b c d=>by ring]; exact (norm_add_le ..).trans ((add_le_add (h0 Φ H) (h1 Φ H)).trans_eq (by ring))
lemma fund (p:(℘) f z)(c:ℂ): (℘) (fun Φ i s=> c*f Φ i s) (c*z):=by
 by_cases ho:c=0; · subst c; simp only [zero_mul]; exact payroll Y h K R A
 intro ε e; refine (p (ε/‖c‖) (by positivity)).mono ?_; intro i t; filter_upwards [t] with s h0 Φ H; rw [←_root_.mul_sub,norm_mul]; exact (mul_le_mul_of_nonneg_left (h0 Φ H) (norm_nonneg _)).trans_eq (by field_simp)
lemma fin {u':Type*} (V:Finset u')(x:u'→(ΛF)→ℕ→ℕ→ℂ)(y:u'→ℂ)(p:∀ i∈V,(℘) (x i) (y i)): (℘) (fun a b c=> ∑ i∈V,x i a b c) (∑ i∈V,y i):=by
 classical
 induction V using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact payroll Y h K R A
 | insert i V w ih=>simp only [sum_insert w]; exact fork Y h K R A (p i (mem_insert_self ..)) (ih fun j v=> p j (mem_insert_of_mem v))
-- support forecast for change scales.S.Controller.B.Em.A.
end Sim
local notation "γ" i:max=> earthV (w i)
abbrev curlK(t:ℝ)(x:Cover)(K:Calibration)(a:Window.Component): W K:= earthV t • coupleK a x K
lemma locale_r(K:Calibration)(t:ℝ)(x:Cover)(a:Window.Component): Locator K (curlK t x K a) {(nodeC x)}:= locate_scale _ _ _ (locale K)
abbrev τOrder(t:ℕ)(f:ℕ→ι→ Cover)(K:Calibration)(r:ℝ)(X:List (Focal (ι:=ι))): W K:= (X.map (fun a=>curlK r (f t a.1) K a.2)).prod
lemma τOrigin(t:ℕ)(f:ℕ→ι→ Cover)(K:Calibration)(r:ℝ)(X:List (Focal (ι:=ι))) (U:Finset Cover)(p:∀ i∈X,nodeC (f t i.1)∈ U): Locator K (τOrder t f K r X) U:=by
 induction X with
 | nil => exact locate_one ..
 | cons a X ih=> exact locate_join K U (locate_sub K (locale_r ..) (singleton_subset_iff.mpr (p a List.mem_cons_self))) (ih (fun i t=> p i (List.mem_cons_of_mem _ t)))
private lemma τbasis(t:ℕ)(f:ℕ→ι→ Cover)(K:Calibration)(r:ℝ)(X:List (Focal (ι:=ι))) : τOrder t f K r X=earthV r^X.length • courtI (OvO f t) K X:=by
 induction X with
 | nil=> simp only [τOrder,courtI,List.map_nil,List.prod_nil,List.length_nil,pow_zero,one_smul]
 | cons a X ih=>
    let y:= OvO f t a; let Y:= bookFee K y; change ((earthV r • Y)* τOrder t f K r X)=_•(Y* courtI (OvO f t) K X); rw [ih,List.length_cons,pow_succ',Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,mul_comm (earthV r)]
-- genuine all ordinary W multipoints of exactly those on-site currents. Detect sign.
include S' P' K R A ω
lemma Fortune (X:List (Focal (ι:=ι))): Sim Y h K R A (fun Φ i s=> Φ s (τOrder i x Kₜ (w i) X)) (forte z X):=by
 intro ε e; have he:= furnace Y (X:=X) (stoneC ω) h K R A S' P' (fun i=> tribes (OvO x i) Kₜ X) (fun _ _=>rfl) e
 refine he.mono (fun i p=> ?_); filter_upwards [p] with s v Φ H; rw [τbasis,map_smul]; exact v.2 Φ H
variable (a b c:ι)
omit K R A ω S' P'
-- assemble real chart.S using one-site vector current with upper-right block α. Full W mark. Compare repeated signs. -/
abbrev γLift (x:Cover)(a:Axis)(t:ℝ)(K:Calibration): W K := ∑ i:Fin 2,∑ j:Fin 2,(Window.alpha a i j) • curlK t x K (Window.index σ i j)
lemma loco_s(x:Cover)(K:Calibration)(r:ℝ)(a:Axis): Locator K (γLift σ x a r K) {(nodeC x)} := by
 let A(i j:Fin 2):= curlK r x K (Window.index σ i j); let B(i j:Fin 2):=Window.alpha a i j • A i j
 let S:Finset Cover:={nodeC x}; have hx(i j:Fin 2):Locator K (B i j) S:=locate_scale _ _ _ (locale_r ..)
 have he {ι':Type}(T:Finset ι')(F:ι'→ W K)(p:∀ i∈T,Locator K (F i) S): Locator K (∑ i∈T,F i) S:=by
    classical
    induction T using Finset.induction_on with
    | empty=> rw [sum_empty]; exact locate_zero ..
    | insert i T t ih=> rw [sum_insert t]; exact locate_sum K _ (p i (mem_insert_self ..)) (ih fun j v=> p j (mem_insert_of_mem v))
 exact he (Finset.univ: Finset (Fin 2)) (fun i=> ∑ j:Fin 2,B i j) (fun i _=> he univ (B i) fun j _=> hx i j)
include K R A ω S' P'
set_option maxHeartbeats 540000 in
lemma Fortune₃ (D G H: Axis): Sim Y h K R A (fun Φ i s=>Φ s (γLift σ (x i a) D (w i) Kₜ*γLift σ (x i b) G (w i) Kₜ * γLift σ (x i c) H (w i) Kₜ)) (Window.wedgeThree D G H σ (fun u v w'=>(dimf σ:ℂ)* Window.sixM (z a) (z b) (z c) u v w')):=by
 let a₀:=fun i s p=>curlK s (x i a) Kₜ p; let b₀:=fun i s p=> curlK s (x i b) Kₜ p; let c₀:=fun i s p=>curlK s (x i c) Kₜ p; let τ:= @Window.index σ
 let μ:=Window.wedgeThree D G H σ; let W':ℂ:= (dimf σ:ℂ); let d(u v t):= W'*Window.sixM (z a) (z b) (z c) u v t
 let V (Φ:ΛF) i s j k t:= (Φ s: W Kₜ →ₗ[ℂ] ℂ) (a₀ i (w i) j*b₀ i (w i) k*c₀ i (w i) t)
 have hx(i j k l p q:Fin 2):Sim Y h K R A (fun Φ a b=> V Φ a b (τ i j) (τ k l) (τ p q)) (d (τ i j) (τ k l) (τ p q)):=by
    let U:List (Focal (ι:=ι)):= [(a,τ i j),(b,τ k l),(c,τ p q)]; let P:= Fortune Y ω h K R A S' P' U; have he:forte z U=d (τ i j) (τ k l) (τ p q):=(forte_3 (X:=τ i j) (Y₀:=τ k l) (Z:=τ p q) rfl rfl a b c); refine Sim.align (f:=fun Φ i s=>Φ s (τOrder i x Kₜ (w i) U)) Y h K R A (show _ = _ from ?_) he P
    funext Φ z s; unfold U τOrder V; simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_assoc,mul_one]; rfl
 suffices H': (℘) (fun Φ i s=> Window.wedgeThree D G H σ (V Φ i s)) (Window.wedgeThree D G H σ d) by
    refine Sim.align Y h K R A (funext fun Φ=> funext fun i=>funext fun s=>?_ ) rfl H'; unfold Window.wedgeThree γLift V; simp_rw [mul_assoc, sum_mul, mul_sum, map_sum]; -- order of sums? simp_rw expands; commute grouping may wrong
    refine sum_congr rfl fun j _=>sum_congr rfl fun k _=> sum_congr rfl fun l _=>sum_congr rfl fun p _=>sum_congr rfl fun q _=>sum_congr rfl fun u _=>?_ ; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,map_smul,smul_eq_mul]; unfold a₀ b₀ c₀ curlK; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,map_smul,smul_eq_mul]; ring
 unfold Window.wedgeThree; refine Sim.fin Y h K R A _ _ _ fun i _=>Sim.fin Y h K R A _ _ _ fun j _=>Sim.fin Y h K R A _ _ _ fun k _=>Sim.fin Y h K R A _ _ _ fun l _=>Sim.fin Y h K R A _ _ _ fun p _=>Sim.fin Y h K R A _ _ _ fun q _=>Sim.fund Y h K R A (hx i j k l p q) _
end
#print axioms Fortune₃
end Venice
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
