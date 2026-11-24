import YM.SatinExist.Paxis
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 340000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open _root_.YM.SatinExist Lancet
namespace Spine
open Six Xara Aria Casting
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)(s:ℕ)
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Λ"=> P.par
local notation "R"=> P.par.R.L.val
local notation "Z"=> reserve P.par P.width
open CF.Velvet Ballad Casting
-- all laws same lift; forbid actual consistency on raw reading comparison
abbrev stampX (n:ℕ)(b:Bool):P.Test:= sheen P.calibration (P.myroof n b) quartz
structure HavenQ (u:ℝ)(F G:P.Test)(S T:Finset Cover):Prop where
 occupied : F∈bay P.calibration S true ∧ G∈bay P.calibration T true ∧ F∈ enclave P.calibration ∧ G∈enclave P.calibration ∧ PureMatter P.calibration F ∧ PureMatter P.calibration G
 next : P.hostX s (F*G)=P.duoMask s F G
 fence : P.pinFoot s S ⊆ {x | ∀ i:Axis,x i< -u} ∧ P.pinFoot s T⊆ {x|∀ i:Axis,u<x i}
 detection : ∀ U V:P.Test→ₗ[ℂ]ℂ,Comparison P.calibration (P.singleState 3 s x) U→ Comparison P.calibration (P.singleState 3 (s+1) x) V → V (P.hostX s (F*G))≠ U (F*G) ∧ U (F*G)≠0
abbrev Forbidden := ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ p:ℝ,∃ L L', P.HavenQ x s p (P.clothesM L (P.stampX n false)) (P.clothesM L' (P.stampX n true)) (P.zoneCost (P.clay n false) L) (P.zoneCost (P.clay n true) L')
def Eminent (b:ℕ):Prop:= Recommend*βX*Real.sqrt (RedD+3) ≤ Spine.μ*b^6 -- b^6 cast tune
lemma marketsGood : ∃ b:ℕ,0<b∧∀ l:ℕ,b≤l→ Eminent l:=by
 let M:=Recommend*βX*Real.sqrt (RedD+3)
 obtain ⟨d,h⟩:= exists_nat_gt (M/Spine.μ)
 refine ⟨d+1,by omega,fun l e=>?_⟩
 have hL: (l:ℝ)≥1:= by exact_mod_cast (show 1≤l from (by omega))
 have hx:M≤ Spine.μ*l:= (le_of_lt ((div_lt_iff₀ mu_p).mp (h.trans_le (by exact_mod_cast (show d≤l by omega))))).trans_eq (mul_comm ..)
 refine hx.trans (mul_le_mul_of_nonneg_left ?_ mu_p.le); simpa only [pow_one] using pow_le_pow_right₀ hL (by decide :(1:ℕ)≤6)
-- existence milestone
variable (Rho:P.Register)(A:Supplier)(a d L:ℝ)(B:uniform P Rho A a d)(q:P.NightCop)(u:P.Lax L)(e:Eminent P.par.R.L.val)
include B q u e
open Hierarchy
-- far stage as prescribed.$μ.
private lemma preScore : ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ D:P.Test→ₗ[ℂ]ℂ,Comparison P.calibration (P.singleState 3 (s+1) x) D→ P.Inordinate x s D (P.stampX n false) (P.stampX n true):=by
 filter_upwards [P.heft a d A Rho B q,P.expensive a d A Rho B q,eventually_gt_atTop 0] with n t p o
 let S:=P.walls n false; let T:=P.walls n true; have hx:= P.liberal 3 L q u (S∪T)
 filter_upwards [t,tendsto_add_atTop_nat 1|>.eventually p,tendsto_add_atTop_nat 1|>.eventually hx,Navy.stable Y] with s w p hτ hL D Δ
 let f:=P.stampX n false; let g:=P.stampX n true; let X:=P.singleState 3 (s+1) x
 let l:ℕ:= R; let d0:= Recommend; have hu:0<βX:=by unfold βX; exact add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun _ _=>norm_nonneg _)
 let b:= βX/(↑(R*n:ℕ):ℝ)^6; have hb:0<b:=by unfold b; have h:0 < P.par.R.L.val:=P.par.R.L.property; positivity
 obtain ⟨Yb,Ub⟩:= P.unitsWing _ (show 0 ≤ ruler (P.calibration.B) from (by have h:= ruler_gene (P.calibration.B); omega)) (P.westP n) (P.eastP n)
 have hg:Disjoint S T:= Finset.disjoint_left.mpr (by intro z v y; have a:=Yb z y (3:Axis); have b:=Ub z v (3:Axis); simp only [ite_true,Bool.false_eq_true, ite_false, add_zero,Finset.notMem_empty,neg_zero] at a b; omega)
 have ht: ‖D (P.duoMask s f g)‖ ≤ d0*b*Real.sqrt (RedD+3):= P.liberty (P.clay n false) (P.clay n true) s X (P.singles_pure_ward (s+1) x).2 _ _ _ _ b (mem_singleton_self ..) (mem_singleton_self ..) hL hg hb (by intro x' u w g A B; exact p x x' u w g A B) x rfl (hτ x) D Δ -- syntax ordering, s binder; h p uses 1+s vs s+1.
 have hw:Spine.μ/(n:ℝ)^6 < ‖P.singleState 3 s x (f*g)‖ :=w x
 refine ⟨(fun t=>hw.not_ge ((congrArg norm t).symm.le.trans (ht.trans ?_))), norm_pos_iff.mp ((div_pos mu_p (by positivity)).trans hw)⟩
 unfold b; push_cast; have hi:0<(R:ℝ)^6:=by positivity
 calc
   _ = ((d0*βX*Real.sqrt (RedD+3))/(R:ℝ)^6)/(n:ℝ)^6:=by ring
   _ ≤ _ := div_le_div_of_nonneg_right ((div_le_iff₀ hi).mpr e) (by positivity)
theorem refused : P.Forbidden x := by
 filter_upwards [P.preScore x Rho A a d L B q u e] with n t
 filter_upwards [t] with s a L
 let S:= P.clay n false; let T:=P.clay n true; let f:=P.stampX n false; let g:=P.stampX n true
 obtain ⟨D,X,b,V⟩:= P.comparator (s+1) x
 let Zr:= Selected.gaugeMesh P.par s; obtain ⟨k,h'⟩:= exists_nat_gt (L/Zr)
 have hr: L < (↑(k:ℤ):ℝ)*Selected.gaugeMesh P.par s:=by push_cast; exact (div_lt_iff₀ (Selected.gaugeMesh_pos ..)).mp h'
 have p: f∈bay P.calibration S true:= shine_local _ _ _ _ (mem_singleton_self ..) -- tune
 have w: g∈bay P.calibration T true:= shine_local _ _ _ _ (mem_singleton_self ..)
 have H':Punctus (P:=P) false ∅ k S:=by intro i u j; have t:= P.westP n i u j; have z:= ruler_gene (P.calibration.B); simp only [notMem_empty, ite_false, Bool.false_eq_true, neg_zero] at *; rw [if_pos (mem_univ ..)] at t; omega
 have G':Punctus (P:=P) true ∅ k T:=by intro i u j; have t:= P.eastP n i u j; have z:= ruler_gene (P.calibration.B); simp only [notMem_empty, ite_false, ite_true] at *; rw [if_pos (mem_univ ..)] at t; omega
 obtain ⟨N,M,R',T0,T1⟩:= P.transplant x s D X S T f g _ p w (by positivity) (a _ X) H' G'
 let A:=P.clothesM N f; let B:=P.clothesM M g; let V:=P.paperC S N f p; let W:=P.paperC T M g w
 have ha:PureMatter K A:=P.pureCloth f N (shine_mat P.calibration _ quartz); have hb:PureMatter K B:=P.pureCloth g M (shine_mat P.calibration _ quartz)
 have hh:= P.through_past 3 s A B _ V W (by positivity) T1 T0
 refine ⟨N,M,⟨V,W,P.cloth_enc f N (P.shine_kept _ _),P.cloth_enc g M (P.shine_kept _ _),ha,hb⟩,hh,⟨P.neg_funds s L _ _ hr T1,P.length_funds s L _ _ hr T0⟩,fun U Ve α η=>?_⟩
 change Ve (P.hostX s (A*B)) ≠ U (A*B) ∧ U (A*B)≠0; rw [α.matter _ (matterPure_mul K ha hb),Comparison.unique K _ η X,hh]; exact R'
#print axioms refused
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
