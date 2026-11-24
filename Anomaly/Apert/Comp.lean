import Anomaly.Apert.Employee
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
variable {n : Side}


namespace LocalLimit
namespace Preparation
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Pitching Focus Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (k0:ℕ)(Γ:ℝ) (Γ0:Taxi.DayT 6 Γ) (g0:0≤Γ)
local notation "p0"=> Y.meter.a 0
local notation "L"=> P.R.L
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
variable (s i k:ℕ)
local notation "xF"=>hat P.R.L P.x s
local notation "N"=> P.Ctor (Y.ir i) s
local notation "Ty"=> (Y.voyage i).CapeT s
local notation "P'"=> RootBook Y i k s
variable (H F:ℝ→ℝ){z z':ℝ}(p:s<Y.uv k)
    (he:ThresholdPool (radiusB (hat P.R.L P.x s)) (BScale.runway (hat P.R.L P.x s)) (inkScatter k0 (radiusB (hat P.R.L P.x s)) |Xs Y F (hat P.R.L P.x s)|) z (inkScatter k0 (radiusB (hat P.R.L P.x s)) |Xs Y H (hat P.R.L P.x s)|) z')
    (HB:HavenL (P.Ctor (Y.ir i) s) (RootBook Y i k s).p P.R.L.val)

include Y p
lemma contourB : (p0).order=6 ∧ (p0).power=2 ∧ (p0).supportExponent=1 := by obtain ⟨_,_,u,w,v⟩:=Y.meter.boot 0; exact ⟨v,w,u⟩

local notation "Z'"=> pulseZ  -- remove
variable (ζ:1≤k0)
variable (U K:ℝ→ℝ)
local notation "Pq"=> (p0).order
local notation "△"=>stageΛ Y Γ H xF
local notation "Ω°"=> rootRim
variable (R:FlagWidth (RootBook Y i k s).p (RootBook Y i k s).K (cipherK P.J.n) )
    (Hf:Mew.SanB (RootBook Y i k s).K (giftK (RootBook Y i k s).p ((RootBook Y i k s).p.supportExponent+1/2)) (RootBook Y i k s).p P.h (fun _=>K (hat P.R.L P.x s)))
variable (FΔx:∀ s':Sweep (P.Ctor (Y.ir i) s), passingF (P.Ctor (Y.ir i) s) s' (RootBook Y i k s).K (RootBook Y i k s).K)
    (FΔy:∀ s':Sweep (P.Ctor (Y.ir i) s), passingR (P.Ctor (Y.ir i) s) s' (RootBook Y i k s).F (RootBook Y i k s).F)

structure poolMark (k:ℕ)(x γ t:ℝ) : Prop where
    hush: γ+Real.exp 1*(γ*(1-degreePrice (radiusB x) γ (BScale.runway x))⁻¹+t)≤ 100*γ
    pledge: t+γ*(1-degreePrice (radiusB x) γ (BScale.runway x))⁻¹≤1
    spine: (27:ℝ)*k ≤ BScale.runway x*(radiusB x:ℝ)^2

-- detector prices at arbitrary F,H schedules respecting this one Loading Bench, raw Mark supported on root price ℓ (not tied to Pose Stamp). pass more pieces later
variable (o: Site (P.Ctor (Y.ir i) s))
    (V:Mark (P.Ctor (Y.ir i) s))(Y':phy (P.Ctor (Y.ir i) s))(r0:ℕ)(pay:ℝ)
    (v:WindowTag V o r0 pay) (u:Contact ((Y.voyage i).CapeT s) (offsetMask r0 o) V Y') (Q:Sour.Bag (P.Ctor (Y.ir i) s))
    (rW: nestLink P.U (RootBook Y i k s) ((Y.voyage i).CapeT s) Q Y')
    (t:Barrage (RootBook Y i k s).p P.J.n (offsetMask r0 o) P.h Q ((RootBook Y i k s).p.supportExponent+8/((RootBook Y i k s).p.B:ℝ)) (F (hat P.R.L P.x s)) (H (hat P.R.L P.x s)))
    (W: (RootBook Y i k s).slip=0)

include flag p HB Γ0 g0 he FΔx FΔy R Hf v u rW t W ζ
lemma jointCore (hg: Gala 2 6 100 (hat P.R.L P.x s) 3)(hX:20<(More (P.Ctor (Y.ir i) s)).val)(hN: 3≤ (P.Ctor (Y.ir i) s).val)
    (hK: poolMark k0 xF (U xF) ((k0:ℝ)*(αPℓ*stageC Y Γ H xF)))
    (h_:z= estim_X K (hat P.R.L P.x s)) (h':z'=U xF): ∃ E G T φ, Plot (RootBook Y i k s) P.U ((Y.voyage i).CapeT s) o (offsetMask r0 o) r0 V Y' E G T φ L k0 P.h (chargeC Y Γ k0 H U xF) (wakeK k0 U xF) (stageΛ Y Γ H xF) (fees Y H xF) pay (2*peka_H (p0).power*fees Y H xF):=by
 subst z z'
 obtain ⟨x,hz,g,h,q⟩:=p_meters Y i k s p; let p':=(P').p; let X:=hat P.R.L P.x s
 obtain ⟨a,b,w⟩:= contourB Y s k p
 obtain ⟨r,R',e,t'⟩:=rent_old _ _ _ _ _ _ R Hf (zero_le_one.trans P.height) -- tune
 have inp:ThresholdPool p'.B (p'.B:ℝ)⁻¹ (inkScatter k0 p'.B |Xs Y F xF|) (estim_X K X) (inkScatter k0 p'.B |Xs Y H xF|) (U X):=by unfold p'; rw [x]; exact he
 let θ:= thresholdOcclus inp
 have hU:0≤ fees Y H X:=by unfold fees putTip reserveT coin_n stilK BScale.runway; positivity
 let e':Ids N:=Classical.arbitrary _
 let hx':=(Y.voyage i).ownership s
 have hk:Roof N P.J.k P.d P.J.n Ty:={ hx'.paid with paid:=fun i=> (hx'.paid.paid i).shrink P.J.hr.le }
 let f:= orbitalInterest Y flag s i k p
 have ho:p'.order=Pq:=g.trans a.symm; have hW:Δv p' Γ=Δv p0 Γ:= Ves p0 p' ho (h.trans b.symm) (q.trans w.symm) _
 have hW': Extr_h P.R.L.val p' Γ=Extr_h P.R.L.val p0 Γ:= μφ_c p0 p' ho (h.trans b.symm) (q.trans w.symm) _ _
 have hb: θ.η=BScale.runway X:=by change (p'.B:ℝ)⁻¹= _; rw [show p'.B=_ from x]; rfl
 have hgX:θ.γ= U X:=rfl
 have he(r0:ℕ)(x:Aura N): True:=by trivial
 obtain ⟨E,T,F',μ,H'⟩:= pricePlot v u inp r R' (fun i=>by
      unfold estim_X; change _≤ chi_f _*_ ; have hv:= t' i; rw [g] at hv; exact hv) t (bonus_r (p0) F X).1 (bonus_r (p0) H X).1 (by rw [g,←a]; exact (bonus_r _ F X).2) (by rw [g,←a]; exact (bonus_r _ H X).2) (show Taxi.DayT _ _ from (g.symm ▸ Γ0)) g0 (by rw [g,h]; exact hg) hz ((by rw [←x]; exact Nat.le_trans (by norm_num) HB.pay)) hX hN P.W.pearl P.V.note f.leanJ.1 f.ready hk (P.J.gran.trans hx'.size) (by rw [P.kJ]; norm_num) rW W HB (halo_subset _ _ (mem_singleton_self _)) P.height FΔx FΔy e' (by rw [g,h]; exact le_max_left ..) (by rw [g]; exact le_max_right ..) costPos hU (by rw [g,h,x]; exact le_refl _) ζ  (by change (k0:ℝ)*_ + θ.γ* (1-degreePrice _ θ.γ θ.η)⁻¹≤ _; rw [hW',hb,hgX,x]; exact hK.pledge) (by change θ.γ+Real.exp 1*(θ.γ*(1-degreePrice _ θ.γ θ.η)⁻¹+_)≤ 100*θ.γ; rw [hW',hb,hgX,x]; exact hK.hush) (by change (27:ℝ)*_ ≤ θ.η*_; rw [x,hb]; exact hK.spine)
 -- parentheses let's fill using term obtain via specialization tactic. 
 have hp:yσE p' θ= wakeE U X:= by
    unfold wakeE yσE dollarT; change reserveT p'.power p'.order p'.B θ.η*( U X*(1-degreePrice _ _ θ.η)⁻¹)=_
    unfold p'; rw [g,h,x,hb,pow_zero,mul_one]; rfl
 have he: Real.exp (3*(k0:ℝ))* yσF p' θ=wakeK k0 U X:= by
    unfold wakeK yσF; rw [hgX,hb]; unfold p'; rw [g,h,x]; rw [show θ.κ=1 from rfl, inv_one,one_mul]
 refine ⟨E,T,F',μ,?_⟩
 rw [hW,h.trans b.symm,he,hp,hb,x] at H'; exact H'
end Preparation
end LocalLimit
end YM.CF.Py.Rate
