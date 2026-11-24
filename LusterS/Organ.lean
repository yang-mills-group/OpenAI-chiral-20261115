import LusterS.Gates
import Refrain.Shrift
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
abbrev advent (B:Z.Bounds q η C S)(P:Attached H Z) (r:Ratio c n)(D:Finset (Cell n))(A:Support c)(m:ℕ)(V:fieldDir G n 1): Altar G n:= WithLp.toLp 2 fun i=> if zenith r D A m i.1 then (tiler B P V) i else 0
include B P
lemma tiler_color2 (X:fieldDir G n 1) : ∀ (b:Cell n), (∑ i:Bool×G.ColorIndex, (tiler B P X (b,i))^2)= 2*research Z q b X:=by
 intro b; let f(i:Bool)(j:G.ColorIndex):=(tiler B P X (b,i,j))^2
 change ∑ i:Bool×G.ColorIndex, f i.1 i.2=_
 rw [Fintype.sum_prod_type,Fintype.sum_bool] -- true then false?
 let y:=faceCurl b X; have he : ∑ j,f false j=q.direct * ‖y‖^2:=by
    simp_rw [show ∀ j : G.ColorIndex, f false j=q.direct * (y j)^2 from fun j=> by unfold f; change (Real.sqrt q.direct * y j)^2=_; rw [mul_pow,Real.sq_sqrt q.quadratic_pos.le]]
    rw [← mul_sum,EuclideanSpace.real_norm_sq_eq]
 let w':=ellLine Z b X; have hp:∑ j,f true j= ‖w'‖^2:= by rw [EuclideanSpace.real_norm_sq_eq]; rfl
 rw [he,hp]; unfold research; unfold y w'; ring
lemma tiler_read (X V:fieldDir G n 1)(D:Finset (Cell n))(A:Support c) : ∑ b:Cell n,flash Z q r D A m b X V= ‖tiler B P X + advent B P r D A m V‖^2/2:=by
 let Φ:= tiler (n:=n) B P; let W:= advent B P r D A m V
 conv_rhs=> rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type, Finset.sum_div] -- orientation sum_div
 apply Finset.sum_congr rfl; intro i _; unfold flash; split
 next h=>
    have he(j:Bool × G.ColorIndex): (Φ X+W) (i,j)= Φ (X+V) (i,j):=by rw [map_add]; change Φ X (i,j)+(if zenith r D A m i then _ else _) = Φ X (i,j)+tiler B P V (i,j); rw [if_pos h]
    change research Z q i _=_; change _=(∑ j:Bool × G.ColorIndex, ((Φ X+W) (i,j))^2)/2; simp_rw [he]; rw [show ∑ j:Bool× G.ColorIndex,_=_ from tiler_color2 B P (X+V) i]; ring
 next h=>
    have he(j:Bool×G.ColorIndex): (Φ X+W) (i,j)= Φ X (i,j):=by change Φ X (i,j)+(if zenith r D A m i then (tiler B P V (i,j)) else 0)=_; rw [if_neg h,add_zero]
    change _=(∑ j:Bool × G.ColorIndex, ((Φ X+W) (i,j))^2)/2; simp_rw [he]; rw [show ∑ j:Bool × G.ColorIndex,_=_ from tiler_color2 B P X i]; ring
def scintillate (Z:PathData G)(q:Clip)(T:Forest r)(F:Finset T.Free)(D:Finset (Cell n))(A:Support c)(m:ℕ)(Y:fieldDir G n 1)(β:ℝ)(x:LogArray G F):= Real.exp (-β*∑ b:Cell n,flash Z q r D A m b (stock T F x) Y)
include L
lemma gleaming (Y:fieldDir G n 1)(h:(cellM T F H).PosDef)(p:0<β) : let f:=scintillate Z q T F D A m Y β; let K:=chartCost (prism T F H G)⁻¹ (coupling β); Integrable f volume ∧ (∫ x,f x) ≤ K:=by
 let Ψ:= (prism T F H G); let σ:= coupling β
 let Φ:= tiler (n:=n) B P; let Vx:= advent B P r D A m Y; let O:= LinearMap.comp Φ (stockLine T F); let W:= O.comp (colors (G:=G) (ι:=↥F)).toLinearMap
 have hf: Ψ.PosDef:= h.kronecker PosDef.one; let X:= LinearMap.range W; let g:= coupling_pos p
 obtain ⟨a,ha,b,hb,he⟩:= X.exists_add_mem_mem_orthogonal Vx
 obtain ⟨x,hx⟩:= ha; let c':= - x; have hE: Vx=a+b:=by first| exact he|exact he.symm
 intro f K
 obtain ⟨hq,ht⟩:= at_price Ψ⁻¹ hf.inv g c' f; let V:=cloud Ψ⁻¹
 let L':=Real.exp (-β* (‖b‖^2/2))
 let F'(x:Prices G F):=Real.exp (force Ψ⁻¹ x/2) • f (displaced c' σ x)
 have he' : F'=fun _=>L':=by
    funext y; unfold F' f scintillate L'; rw [tiler_read B P]; let t:=displaced c' σ y
    have h : Φ (stock T F t)+Vx= σ • W y+b:=by
       rw [hE,←hx]; change W (-x+σ • y)+(W x+b)=_; rw [map_add,map_neg,map_smul]; abel
    rw [show (tiler B P) _ + _=_ from h,norm_add_sq_real (σ • W y) b,show inner ℝ (σ • W y) b=0 from ?_,mul_zero,add_zero]
    · rw [norm_smul,Real.norm_of_nonneg g.le,mul_pow]; let Y:=qpay Ψ y; have hv : ‖W y‖^2=Y:=Tape_price B P L y
      rw [hv,show force Ψ⁻¹ y=Y from (?_),smul_eq_mul, ← Real.exp_add]; swap; · unfold force; rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hf.isUnit)]; rfl
      have hw:β*σ^2=1:=coupling_inter _ p; congr 1; linarith only [show β*σ^2 * Y =Y by rw [hw,one_mul]]
    exact (Submodule.mem_orthogonal _ b).1 hb _ (X.smul_mem _ ⟨y,rfl⟩)
 let J:=integrable_const (μ:=V) L'; rw [← he'] at J; have hu: (∫ x,F' x ∂V)≤1:=by rw [he',integral_const]; simp only [probReal_univ, one_smul]; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.le) (by positivity)
 refine ⟨hq.2 J,ht.trans_le ?_⟩; change K • _ ≤ K; rw [smul_eq_mul]; exact mul_le_of_le_one_right (chartCost_pos _ hf.inv g).le hu

end YM.Gleam.Luster
