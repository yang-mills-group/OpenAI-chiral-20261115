import YM.SU5.FiniteGaugeData.Mist.RidgeX
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
section time
open scoped NNReal ENNReal
lemma trackT (Λ:Preparation)(s d:ℕ): ((thetaX Λ s d):ℝ)=spinT Λ.R.L s d:=by simp [thetaX,spinT,tassel]
lemma timeTour (Λ:Preparation)(s t d:ℕ): (spinT Λ.R.L (s+t) (energyS Λ d t))= spinT Λ.R.L s d:=by unfold energyS; push_cast; exact slot_more ..
-- track cost bridge.Coordinate integer lag.
variable (t:Four ℤ)
variable (X:Engine Y h W' R a H)(φ: W (tent Y h))(u':Plan Y h a d φ)(p:0<d)
local notation "P'"=> X.val
local notation "F"=> bitOp Y h s W' R A S' a d H u' p
local notation "G"=> regular Y h W' R a H X
include X S'

local notation "q"=> spinT L₁ s (d:ℤ)
-- Formula ORDERED exact, f is to the left, x future. Output bought at s+n
lemma appointment (p0:spinT Λ.R.L s (d:ℤ) ≤ spinT Λ.R.L (s+n) (t a)) : ∃ y:Decko Y h a, (F) ((G) ((spinT Λ.R.L (s+n) (t a)- spinT Λ.R.L s d).toNNReal) ((spireT X.val (reportQ (s+n) t)) (H.leaf (s+n) x)))=H.leaf (s+n) y ∧ y.val = (ascended Y h s W' R n φ)*orbitW Kₜ t x.val:=by
 let m:=energyS Λ d n; have he: (m:ℤ) ≤ t a:= (slot_le L₁ _ _ _).1 ((timeTour Λ s n d).symm ▸ p0)
 let ℓ:ℕ:= (t a-m).toNat
 have hq:t a=(m+ℓ:ℕ):=by unfold ℓ; omega
 obtain ⟨y,hp,v⟩:= warmth Y h (s+n) W' R a H x Terrace.scheduleL t X -- binder?
 let y':=hoist Y h a a (ℓ:ℤ) (fun _=>Nat.cast_nonneg' _) y; let w:= appointed Y h s a d n W' R u' y'
 refine ⟨w,?_,?_⟩
 · have ht : spinT L₁ (s+n) (t a)- (q)= (thetaX Λ (s+n) ℓ : ℝ):=by rw [hq,Nat.cast_add,slot_add,show m=energyS Λ d n from rfl,timeTour,add_comm,add_sub_cancel_right,trackT]
   let b:= (spinT L₁ (s+n) (t a) - q).toNNReal; have he: b=thetaX Λ (s+n) ℓ:= (congrArg Real.toNNReal ht).trans (Real.toNNReal_coe ..)
   have hz: (G) b (H.leaf (s+n) y)=H.leaf (s+n) y':=by rw [he,atemporal Y h (s+n) W' R A S' a H X ℓ]; exact X.property ..
   have hζ:(G) b (spireT X.val (reportQ (s+n) t) (H.leaf (s+n) x))=H.leaf (s+n) y':=Eq.trans (congrArg ((G) b) hp) hz; exact Eq.trans (congrArg F hζ) (bitPlus Y h s W' R A S' a d n H _ u' p)
 let t':=Function.update t a (0:ℤ)
 unfold w; rw [appointed_val,Swing]; refine congrArg (fun x=>(ascended Y h s W' R n φ)*x) ?_; unfold y'; rw [hoist_val,clock_add]; rw [←hourS_single a Kₜ, v]; -- argument order?
 change orbitW Kₜ (Pi.single a ((m:ℤ)+ℓ)) (orbitW Kₜ t' x.val)= _
 rw [orbitW_add, show Pi.single a ((m:ℤ)+ℓ)+t'=t from ?_]
 funext i; by_cases hi:i=a; · subst i; simp only [t', Function.update_self,Pi.add_apply,Pi.single_eq_same,add_zero]; omega
 unfold t'; simp [hi]
end time
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
