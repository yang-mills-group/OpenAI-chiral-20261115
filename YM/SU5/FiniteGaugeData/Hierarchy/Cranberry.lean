import YM.SU5.FiniteGaugeData.Hierarchy.Pause
/-! # Also allow moving support AND moving horizon, with volume clocks depending on both -/
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
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Charm
namespace Playlist
namespace Show
local notation "U" => W (tent Y h)
local notation "M" => Motif (tent Y h)
local notation "H₁"=> Theater (tent Y h)

variable (Z:ℕ→ Finset Cover)
local notation "Hᵣ" i:max => folio Λ l Z i
local notation "Wᵣ" i:max => GridStep Λ l (folio Λ l Z i)
local notation "Dₛ" i:max => salary Y h (folio Λ l Z i) i

-- ANY native cost/fit for upcoming conservation claims also allowed
structure Concerted (s : ℕ)(i:ℕ)(ε:ℝ) : Prop where
  within (j:ℕ)(p:j≤ s) : Roomy (folio Λ l Z j) (side Y (u i) j)
  inner (x:Theater (tent Y h))(a:Contract Y h Z x) : Arrive Y h x s→ ‖inPrice Y h s (u i) (J:=J) K Z x a - chorusRead Y h K R x‖ ≤ ε * playTime Y h s Z x a
  paths (k:ℕ) : legacy Y (u i) (v k)→ Works Y Z (u i) (v k) s ∧ ∀ (x:Theater (tent Y h))(a:Contract Y h Z x),Arrive Y h x s → ‖readout Y h s (u i) (v k) x- chorusRead Y h K R x‖ ≤ ε*playTime Y h s Z x a

lemma crimson_h (ε:ℝ)(v:0<ε) : ∀ᶠ i:ℕ in atTop, Concerted Y h K R Z s i ε:=by
  have he (j:ℕ) : ∀ᶠ i:ℕ in atTop, Roomy (folio Λ l Z j) (side Y (u i) j):= by
    filter_upwards [((momentum Y j).comp K.pick.grow_i.tendsto_atTop).eventually (roomy_sides (folio Λ l Z j) Kₜ)] with i t; rw [show side Y (u i) j= (tent Y h).c (momentm Y (u i) j) from (terrain Y h _ _).symm]; exact t
  filter_upwards [(eventually_all (ι:=Fin (s+1))).mpr fun i=>he i.val,earnings Y h s K R Z ε v] with i g x; exact ⟨fun j t=>g ⟨j,t.trans_lt (Nat.lt_succ_self _)⟩,x.1,x.2⟩
-- one IR thinning qualifying these out-of-band readings too. countable many requests (maybe different rules at each stage) by grouping to a new encompassing bound instead of running new diagonal Yuk. keep earlier sizes as well.
lemma HeadCount (Z:ℕ→ℕ→ Finset Cover)(s:ℕ→ℕ)(ε:ℕ→ℝ)(h':∀ i,0<ε i)(Fee:ℕ→ℕ→Prop)(p:∀i,∀ᶠ j in atTop,Fee i j):
    ∃ q:ℕ→ℕ,StrictMono q ∧ Universal Y h (u∘q) v I E ∧ Rolled Y h (u∘q) v J P ∧ ∀ i, Fee i (q i) ∧ ∀ j≤ i, ∀ k≥ q i, Concerted Y h K R (Z j) (s j) k (ε i):=by
  have hv(i t:ℕ):∃ k:ℕ,t<k ∧ Fee i k ∧ ∀ v ≤ i, ∀ j≥k,Concerted Y h K R (Z v) (s v) j (ε i):=by
    obtain ⟨k,hk⟩:= eventually_atTop.mp ((eventually_all_finset (Iic i)).mpr fun j _=> crimson_h Y h (s j) K R (Z j) (ε i) (h' i)); obtain ⟨n,hN,y,g⟩:= ((eventually_gt_atTop t).and ((eventually_ge_atTop k).and (p i))).exists
    exact ⟨n,hN,g,fun v h j t=> hk j (y.trans t) v (mem_Iic.mpr h)⟩
  choose g f F H using hv; let q:= Nat.rec (motive:=fun _=>ℕ) (g 0 0) fun i t=> g (i+1) t; let u':StrictMono q:= strictMono_nat_of_lt_succ fun i=> f (i+1) (q i); refine ⟨q,u', uni_roll Y h u' strictMono_id K, roll_thin Y h u' strictMono_id K R,fun i=>?_⟩; cases i with
   | zero=> exact ⟨F ..,H 0 0⟩
   | succ i=> exact ⟨F ..,H (i+1) (q i)⟩
#print axioms HeadCount
end Show
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
