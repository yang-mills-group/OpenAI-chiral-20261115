import YM.SU5.FiniteGaugeData.Tower.Central
import YM.SU5.Assay.Panel
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace Etch
variable (K:Calibration)(w:ℤ)(σ:Cover)
variable (j:Axis)(f:Family K)(he:σ j=0)
local notation "p"=>parting K w σ
local notation "l" v:max=>pet 0 j v
local notation "h" v:max=>pet 1 j v
local notation "P"=>Panel K w σ f

include he
lemma weathervane (n:ℕ): Located K w σ f 0 (toward K j w f n):=by
 induction n with
 | zero=>exact Located.start
 | succ n ih=>
    rw [toward_step]
    have ht:p j 1=gaugeT K w:=by unfold parting; rw [he,mul_zero,mul_one,zero_add]
    have hT:bent j 1 0=0:=by
       unfold bent; convert petID 0 j using 2; rw [Pi.zero_apply]; norm_num
    exact hT ▸ ht ▸ Located.reflect j 1 ih -- rewriting syntax

lemma fanPanel (n:ℕ): P (l 0) (h (n:ℤ)) n (lace K j w f 1 n):=by
 induction n with
 | zero=>exact Panel.blank _ _ _
 | succ n ih=>
    have ht:Inbox (l 0) (h 1) 0:=by intro i; simp [pet]
    have h₁:=Panel.single K w σ ht (weathervane K w σ j f he n)
    have h₂:=Panel.forward K w σ j 1 ih; rw [zero_add,mul_one] at h₂
    have hg:=Panel.glue K w σ j (by omega) (by omega) h₁ h₂
    rw [lacing,Nat.cast_succ]; rw [Nat.add_comm 1 n] at hg; exact hg

lemma duoPanel (n:ℕ)(a:ℤ): P (l (a-n)) (h (a+n)) (2*n) (chambers j w (w*a) f 1 n):=by
 let x:=fanPanel K w σ j f he n
 have h₁:=Panel.turn K w σ j 0 x
 have ht:p j 0=0:=by unfold parting; rw [he,mul_zero,mul_zero,add_zero,gaugeT_zero]
 rw [sub_self,ht] at h₁
 have hh:=(Panel.glue _ _ _ j (by omega) (by omega) h₁ x).forward _ _ _ j a
 rw [add_comm ((0:ℤ)-_),←add_sub_assoc,add_zero,add_comm (↑n:ℤ),←two_mul] at hh
 exact hh

lemma marquee (n:ℕ)(a:ℤ): P (l (a-3*n)) (h (a+n)) (4*n) (banner j w (w*a) n f):=by
 let x:=duoPanel K w σ j f he n a
 have h₁:=Panel.turn K w σ j (2*(a-n)) x
 have ht:p j (2*(a-n))=gaugeT K (cliff w (w*a) n):=by unfold parting cliff; rw [he]; congr 1; ring
 rw [ht,show 2*(a-(n:ℤ))-(a+n)=a-3*n from by ring,show 2*(a-(n:ℤ))-(a-n)=a-n from by ring] at h₁
 rw [show 4*n=2*n+2*n from by ring]
 exact Panel.glue K w σ j (by omega) (by omega) h₁ x
end Etch
end YM.CF.Buffered.Afterglow.Tower.SlabMark
