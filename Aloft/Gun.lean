import Aloft.Slope
import Ridgetop.Angles
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Ridgetop
local notation "R" d:max=> girder P d
local notation "r" d:max=> ((girder P d):ℝ)
local notation "A₀" => (pollN P)
local notation "g₀"=> ((pollN P:ℕ):ℝ)
local notation "Y*"=> ‖Ridgetop.visible‖
local notation "χ" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
local notation "Θ"=> ((Fintype.card SU.group.ColorIndex):ℝ)
variable (m:ℕ)(e:1 ≤ m) (l d:ℕ)(w:Cover)
lemma ocore_up (i:ℕ)(h:enoughR P s i): ocore P s i ≤ 16*Θ:=by
 let x:=hat P.par.R.L P.par.x s
 let q:= √x * Next.SectorChange.coupling (gram P.run s (P.period (P.projection.rows i)) (P.cutoff (P.projection.columns i))).beta
 have hv:0<x:= ((Real.exp_pos 1).trans_le P.large).trans_le (Vale.crown P.par.R.L P.par.x s)
 obtain ⟨_,_,_,b0,W⟩:= prices_plot P.run s (P.period (P.projection.rows i)) (P.cutoff (P.projection.columns i)) h
 have hp:Set.Icc (1/2:ℝ) 2 q:= Regis.Head.Etch.railB b0.1 b0.2 hv
 have hq:0 ≤ q:=le_trans (by norm_num: (0:ℝ)≤ 1/2) hp.1
 change q^4*Θ/2 ≤ _; have hd:q^(4:ℕ) ≤16:=(pow_le_pow_left₀ hq hp.2 4).trans (by norm_num)
 have ht:1 ≤ Θ:=color₁
 nlinarith only [mul_le_mul_of_nonneg_right hd (zero_le_one.trans ht),ht]
-- use constants 1/64,+.
noncomputable abbrev quoteC(l d:ℕ)(w:Cover):ℝ:= (pilot P (stackW d) (drive l (8*l+6)) (blazeF P m d w) true).price
local notation "L" d:max w:max=> led P m d w
private lemma dollars {x z U b t k v:ℝ}(v0:0 < v)(t0:0 ≤ t)(p:1/32 ≤z)(hq:z≤b)(B:|U| *t^8 ≥ v/2)(C: |U| *t^8≤2*v)(V:|x-z*U| *t^8 ≤ v/128):
 v/128 ≤ |x| *t^8 ∧ |x| *t^8 ≤ (2*b+1)*v:=by
 have hz:0<z:=lt_of_lt_of_le (by norm_num) p
 have e:= abs_sub_abs_le_abs_sub (z*U) x; rw [abs_sub_comm,abs_mul,abs_of_pos hz] at e
 have f:= abs_sub_abs_le_abs_sub x (z*U); rw [abs_mul,abs_of_pos hz] at f
 obtain ⟨h1,h2⟩: v/64 ≤ z*|U| *t^8 ∧ z*|U| *t^8 ≤ b*2*v:=by
    have hu:= mul_le_mul p B (show 0 ≤ v/2 from by positivity) hz.le; have ht:= mul_le_mul hq C (mul_nonneg (abs_nonneg _) (by positivity)) (hz.le.trans hq); constructor <;> linarith only [hu,ht]
 constructor <;> linarith only [V,h1,h2,v0,mul_le_mul_of_nonneg_right e (show 0 ≤ t^8 by positivity),mul_le_mul_of_nonneg_right f (show 0 ≤ t^8 by positivity)]
-- l need power authorization to bound scaled price error
include e
lemma sides (h:∀ᶠ d:ℕ in atTop, (r d) ≤ (χ d)^l): ∀ᶠ d in atTop,∀ w:Cover,Enrolled P d (stairW d) w→ Y*/128 ≤ |quoteC P m l d w| * (L d w)^8 ∧ |quoteC P m l d w| * (L d w)^8 ≤ (32*Θ+1)*Y*:=by
 let x(d):=χ d; let a:=(g₀)*4*m+2
 have hv:0< Y*:= norm_pos_iff.mpr Ridgetop.visibility
 let b:= mudF P*64*a^8
 have he:Tendsto (fun d=> b*(x d)⁻¹) atTop (𝓝 0):=by simpa only [Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp (stages_q P)).const_mul b
 filter_upwards [ranged P m e,h,he.eventually (ge_mem_nhds (show 0 < Y*/128 from (by positivity)))] with d h g f w p
 let s:=stackW d; let y:= x d; let z:w=w:=rfl; let u:= blazeF P m d w; let κ:= L d w; have ht:0 ≤ r d:=Nat.cast_nonneg _
 let A:=drive l (8*l+6); let Z:=pilot P s A u true
 have hk :0≤κ:=ht.trans (ledG P m d w p e)
 let c(i:ℕ):=boarding P s A u true i
 let kzμ(i):= ocore P s i
 have hl:Tendsto (fun i=> |c (Z.station i)| *κ^8) atTop (𝓝 (|quoteC P m l d w| *κ^8)):= ((Z.market.abs.mul_const (κ^8)))
 have hm:∀ᶠ i:ℕ in atTop,Y*/128 ≤ |c i| * κ^8 ∧ |c i| *κ^8 ≤ (32*Θ+1)*Y*:=by
    filter_upwards [h w p,prospects P s] with i k hw
    dsimp only at k; rw [← sweep_cast P _ _ _,Complex.norm_real,Real.norm_eq_abs] at k
    obtain ⟨v0,v1⟩:=ration P s A u i hw
    let K:=adage P s i u
    change Y*/2 ≤ |K| *κ^8 ∧ |K| *κ^8 ≤ 2*Y* at k
    have hz:|c i-kzμ i *K| *κ^ (8:ℕ) ≤ Y*/128:=by
       have hp:=artFactor (summitT _) ht g
       have hu:=mandate P m d w p e; change _ ∧ κ ≤ a*(r d) at hu
       let H:=mudF P*64; have hH:0 ≤ H:=by unfold H; have he:=mud_pos P; positivity
       have hy:0 ≤ (x d)⁻¹^(2*heightH A):=by have hq:0 ≤ x d:= zero_le_one.trans (summitT _); positivity
       change |c i-_*K| ≤ H*(x d)⁻¹^(2*heightH A) at v1
       calc _ ≤ H*(x d)⁻¹^ (2*heightH A)*(a*(r d))^8:=mul_le_mul v1 (pow_le_pow_left₀ hk hu.2 8) (by positivity) (by positivity)
            _ = b*((x d)⁻¹^ (2*heightH A)*(r d)^8):=by unfold b H; ring
            _ ≤ _ := (mul_le_mul_of_nonneg_left hp (by unfold b; have := mud_pos P; positivity)).trans f
    rw [show (32:ℝ)*Θ=2*(16*Θ) from (by ring)]
    exact dollars (k:=0) hv hk v0 (ocore_up P s i hw) k.1 k.2 hz
 have hz:=Z.trans.tendsto_atTop.eventually hm
 exact ⟨ge_of_tendsto hl (hz.mono fun i t=> t.1),le_of_tendsto hl (hz.mono fun i t=> t.2)⟩
#print axioms sides
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
