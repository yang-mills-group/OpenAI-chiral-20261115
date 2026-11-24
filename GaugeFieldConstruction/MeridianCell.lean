import GaugeFieldConstruction.Tidings
import YM.Work.A16
/-!
# Wick L1 spins on compact ingredients. Use this Lorentz group (proper vacuum-covariance), actual District
 Preformed unit calibration keeps Wick temporal factors and metric signs posted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Cauchy Row Phys Mink Function Set Filter Matrix Complex
open scoped Matrix Matrix.Norms.Frobenius Kronecker BigOperators Topology ContDiff
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
abbrev C4L (α : Type*) := Matrix α α ℂ
lemma parkAxisL (A : Ortho)(hp:Lorentz.spatialTurn A): A.val.det=1:= by
 have h : LinearMap.det (Matrix.toEuclideanLin A.val)=1:= hp.1
 rwa [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin] at h
abbrev parkLorL (A:Ortho)(hp:Lorentz.spatialTurn A): SO:=⟨A,(covers_all A).2 (parkAxisL A hp)⟩
namespace Cell
variable (P : Cell α)
structure Meridian where
 sheet:Lorentz→* C4L α
 tilts(i j):Continuous (fun a=>sheet a i j)
 park (K:Ortho)(h:Lorentz.spatialTurn K)(i j): sheet (Lorentz.room K h) i j= ↑(P.active K i j)
 spark (k: SpaceAxis)(i j): HasDerivAt (fun t=>sheet ((Ray.fromAxis k).boost t) i j) (-I * (↑(P.pin (Ortho.plane timeAxis k.castSucc) i j):ℂ)) 0

def stayL (α:Type*)[Fintype α][DecidableEq α]:Meridian (Still α) where
 sheet:=1; tilts i j:= continuous_const
 park K h i j:=by by_cases p:i=j<;> simp [Still,p, Matrix.one_apply]
 spark k i j:=by simp only [Still,LinearMap.zero_apply,Matrix.zero_apply, ofReal_zero,mul_zero]; exact hasDerivAt_const _ _
private def βBook (K:Lorentz): M4:= Matrix.of fun i j=> K.act (basis j) i
lemma budgetL (K:Lorentz)(x:E4)(i): K.act x i= ∑ j,(βBook K) i j*x j:=by
 have h:x=∑ j:Axis,x j • basis j:=by ext i; simp [basis_eq]
 calc _=(K.act (∑ j:Axis,x j • basis j)) i:=congrArg (fun X:E4=> K.act X i) h
      _ = ∑ j,(βBook K) i j*x j:=by rw[map_sum]; simp only [map_smul]; simp [βBook,mul_comm]
def Wickγ (i:Axis):ℂ:= if i=timeAxis then -I else 1
lemma wickLiveL(i): Wickγ i ≠ 0:=by unfold Wickγ; split_ifs with h <;> simp
noncomputable def σVecL: Lorentz→* C4L Axis where
 toFun K:= Matrix.of fun i j=>Wickγ i* ↑(βBook K i j) *(Wickγ j)⁻¹
 map_one':=by
    ext i j; simp only [of_apply,βBook, Lorentz.act_one,basis_eq]
    rw [Matrix.one_apply]; split_ifs with h; · rw [h]; simp [wickLiveL]
    simp
 map_mul' K U:=by
    ext i j; simp only [of_apply,Matrix.mul_apply,βBook,Lorentz.act_mul]
    rw [budgetL]; push_cast; simp_rw [Finset.mul_sum,Finset.sum_mul]; refine Finset.sum_congr rfl fun a _=>?_
    simp only [βBook,of_apply]; field_simp [wickLiveL a,wickLiveL j] <;> ring

lemma βroomL (K:Ortho)(h:Lorentz.spatialTurn K) i j: βBook (Lorentz.room K h) i j= K.val i j:=M4.move_basis K.val _ _
lemma park_timeL (K:Ortho)(h:Lorentz.spatialTurn K)(x:Axis): K.val timeAxis x=if x=timeAxis then 1 else 0:=by
 rw [←M4.move_basis K.val timeAxis x]
 have hv:=h.2 (basis x)
 simp only[time,Ortho.move,basis_eq] at hv; simpa [eq_comm] using hv
lemma park_crossL (K:Ortho)(h:Lorentz.spatialTurn K)(x:Axis):K.val x timeAxis= if x=timeAxis then 1 else 0:=by
 have h':Lorentz.spatialTurn K⁻¹:=by
    constructor
    · have hz:= parkAxisL K h; change LinearMap.det (Matrix.toEuclideanLin _)=1; rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]; change Matrix.det (star K.val) = 1; rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,hz]; rfl
    intro a; exact (by simpa using (h.2 (Ortho.move K⁻¹ a)).symm)
 exact park_timeL K⁻¹ h' _

abbrev pVecΩL (a:SpaceAxis) :Ortho.Skew:=Ortho.plane timeAxis a.castSucc
abbrev LogPriceL (g:Lorentz) (i j:Axis):ℝ:= βBook g i j
-- Taylor price compatibility with Wick-Eu extension
lemma tickVecL (k:SpaceAxis)(i j): -I * (↑((pVecΩL k).val i j):ℂ)= Wickγ i * (↑((Ray.fromAxis k).crossT (basis j) i):ℂ) * (Wickγ j)⁻¹ := by
 -- finite in axes
 refine Fin.lastCases ?_ (fun a=>?_) i
 · change -I * (↑((pVecΩL k).val timeAxis j):ℂ)= Wickγ timeAxis * ↑(time (_)) * _
   rw [Ray.time_gen, basis_eq]; by_cases h:j=k.castSucc
   · simp [pVecΩL,Ortho.plane,Matrix.single, Wickγ,h]
   simp [pVecΩL,Ortho.plane,Matrix.single,Wickγ,h, Ne.symm h]
 change -I * (↑((pVecΩL k).val a.castSucc j):ℂ)= Wickγ a.castSucc * (↑(spatial ((Ray.fromAxis k).crossT (basis j)) a):ℂ) * _; rw [Ray.space_gen]
 by_cases p:a=k<;> by_cases q:j=timeAxis<;> simp [pVecΩL,Ortho.plane,Matrix.single,Wickγ,p,q, basis_eq,eq_comm] <;> simp_all [eq_comm]

def PilotCellL : Meridian UnitV where
 sheet:=σVecL
 park K h i j:=by
    change _ * ↑((βBook (Lorentz.room K h)) i j) *_= (↑(K.val i j):ℂ)
    rw[βroomL K h]
    by_cases p:i=timeAxis
    · subst i; rw [park_timeL K h j]; by_cases hi:j=timeAxis <;> simp [hi,wickLiveL]
    by_cases q:j=timeAxis
    · subst j; rw [park_crossL K h]; simp [p]
    simp [Wickγ,p,q]
 tilts i j:=by
    change Continuous fun a:Lorentz=> Wickγ i* (↑(a.act (basis j) i):ℂ)* (Wickγ j)⁻¹
    fun_prop
 spark k i j:=by
    let L:E4 →L[ℝ] ℝ:= PiLp.proj 2 (fun _:Axis=>ℝ) i
    let G:=Ray.fromAxis k; have hu: HasDerivAt (fun t=>(G.boost t).act (basis j)) (G.crossT (basis j)) 0:= (ContinuousLinearMap.apply ℝ E4 (basis j)).hasFDerivAt.comp_hasDerivAt _ (G.generator)
    have h : HasDerivAt (fun t=> L ((G.boost t).act (basis j))) (L (G.crossT (basis j))) 0:= L.hasFDerivAt.comp_hasDerivAt _ hu
    change HasDerivAt _ (-I * (↑((pVecΩL k).val i j):ℂ)) _; rw [tickVecL]
    exact (((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h).const_mul (Wickγ i)).mul_const _)
variable {P}{Q:Cell β}
namespace Meridian
variable (Z:Meridian P)(V:Meridian Q)
def sail : Meridian (Cell.sum P Q) where
 sheet:= { toFun u:= Matrix.fromBlocks (Z.sheet u) 0 0 (V.sheet u)
           map_one':=by simp
           map_mul' u v:=by simp [Matrix.fromBlocks_multiply] }
 tilts i j:= by cases i <;> cases j <;> first|exact Z.tilts _ _|exact V.tilts _ _|exact continuous_const
 park K h i j:=by cases i <;> cases j <;> first|exact Z.park K h _ _|exact V.park K h _ _|exact (by change 0=(↑(0:ℝ):ℂ); simp)
 spark k i j:=by cases i <;> cases j <;> first|exact Z.spark k _ _|exact V.spark k _ _|exact (by change HasDerivAt (fun _:ℝ=>0) (-I * (↑(0:ℝ):ℂ)) _; rw [ofReal_zero,mul_zero]; exact hasDerivAt_const _ _)

def spar : Meridian (wings P Q) where
 sheet:= { toFun u:= (Z.sheet u) ⊗ₖ (V.sheet u)
           map_one':=by simp
           map_mul' u v:= by rw [map_mul,map_mul,mul_kronecker_mul] }
 tilts i j:= (Z.tilts i.1 j.1).mul (V.tilts i.2 j.2)
 park K h i j:= by dsimp only[MonoidHom.coe_mk,OneHom.coe_mk]; rw[Matrix.kronecker_apply,Z.park _ h,V.park _ h]; change _ * _= (↑(_*_:ℝ):ℂ); push_cast; rfl
 spark k i j:=by
    refine ((Z.spark k i.1 j.1).mul (V.spark k i.2 j.2)).congr_deriv ?_
    -- derivative outgoing one
    rw [Ray.boost_start,map_one,map_one]; change _ = -I* (↑( (P.pin (pVecΩL k) ⊗ₖ (1:R4 β) + (1:R4 α) ⊗ₖ Q.pin (pVecΩL k)) i j):ℂ)
    simp only [Matrix.add_apply,Matrix.kronecker_apply]; by_cases p:i.1=j.1<;>by_cases q:i.2=j.2<;>simp [p,q,Matrix.one_apply]<;> ring
end Meridian
#print axioms PilotCellL
#print axioms Meridian.sail
#print axioms Meridian.spar
end Cell
end YM.GaugeFieldConstruction.Stage
