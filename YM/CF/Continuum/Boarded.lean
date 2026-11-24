import YM.CF.Continuum.Cadenza
/-!
# Quantifiers on conditioned fees: depth and period predictable schedule
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Finset Lattice Laurent Wilson Analysis Pressure MeasureTheory Mint Mint.Roe Graph Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {N : ℕ→Side} {a b c w η r e K b' v C' l s' L' H0 μ y h C L0 γ vA r₀ C₀:ℝ}{J B m:Side}{O:Odd J.val}{j k n₀:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P} {x L L1 : ℕ→ℝ}
namespace Pastures
local notation "NP" => (fun i=> mid (N i) B)
local notation "M" => More ∘ NP
local notation "n" => eur NP
local notation "N'" => eur (More∘NP)
variable {I : ∀ i,GramM (mid (N i) B)} (D:Pic.Span hP K b' v C' l s' k)
    (Z: Pastures B N x h C r μ L' w γ L0 L I)
set_option quotPrecheck false
local notation "β'" => (fun i=>(I i).beta)
local notation "t_u" i:max => compassRate (NP i) (hemp x i)
local notation "billY" i:max => Real.exp (-stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0)
local notation "yield" i:max => gainS (M i) (hemp x i)*billY i
local notation "hest" i:max => horn (NP i) s'
local notation "Yt" i:max => yieldAngle (I i) (t_u i)
local notation "A_ψ" i:max => Kea.angel (N i) P (I i).J.M
local notation "ηΩ" i:max => ‖normalizedTilt P (t_u i) (I i)‖
local notation "shotW" i:max => compass (NP i) (t_u i)
variable (X:∀ i,Loom (mid (N i) B))(u:∀ᶠ i in atTop,SkinT (I i) (X i) e)(H:Port D a y C₀ vA r₀ n₀)(h₀:C₀≤h)(U:∀ᶠ i in atTop, Tableau (N i) (I i) (X i) P (soaked (x i)) H0)

def rawPaid(m B:Side)(L0 L γ k ζ:ℝ):=gainS (More (mid m B)) (hemp (fun _=>ζ) 0)*Real.exp (-stoutY (More (mid m B)) ζ (4*hemp (fun _=>ζ) 0) γ (temp ζ) L L0)*horn (mid m B) k
include Z D
lemma tilt_kin (f:ℝ)(w':ℕ) (bf:0<f)
   (hr:∀ m:Side,k ≤ (mid m B).val →∀ F:Jill.Male, f*( (mid m B).val:ℝ)^(-(w':ℤ))*Kea.angel m P F≤ ‖Kea.AMP m P (needles (mid m B)) F‖ ): ∀ᶠ i in atTop, 0< rawPaid (N i) B L0 L' γ s' (x i)/2 ∧ f/(n i^w')*(rawPaid (N i) B L0 L' γ s' (x i)/2) ≤ ηΩ i := by
 filter_upwards [yields_ω D Z, Z.tend.eventually_ge_atTop k] with i ⟨pz,z⟩ h
 rw [show rawPaid (N i) B L0 L' γ s' (x i)=yield i*hest i from (by dsimp only; rw [Z.beta]; rfl)]; refine ⟨by positivity,?_⟩; let p:= Yt i; have hl:k ≤ (NP i).val:=Nat.cast_le.mp h; obtain ⟨a,b⟩:=D.plan _ hl; have ht:0 < A_ψ i:=Kea.angel_p hP D.stmt a D.p D.eP _ b; let y:=A_ψ i; let Q:=yield i*hest i; have hp:0<p:=by nlinarith only [z,pz,ht ]
 have hc:n i>0:=nPos _; have he :f/(n i^w')*A_ψ i ≤ ‖Kea.AMP (N i) P (needles (NP i)) (I i).J.M‖:=by have hh:= hr (N i) hl (I i).J.M; rw [zpow_neg, zpow_natCast] at hh; exact hh
 unfold normalizedTilt; rw [norm_smul,Real.norm_of_nonneg hp.le]; calc
   _ ≤ f/(n i^w')*(p * y):=mul_le_mul_of_nonneg_left (by change Q/2≤ _; linarith) (by positivity)
   _ ≤ _ :=by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left he hp.le

def fees(m B:Side)(L0 L γ k ζ α H0:ℝ)(d:ℕ):= ((α/((mid m B).val:ℝ)^d)* (rawPaid m B L0 L γ k ζ/2) /2) / Real.exp (massMeter (mid m B)*(3*strengthLog (soaked ζ)+H0))

include D H h₀ U u
lemma detects_rates (f v':ℝ)(d:ℕ)(bf:0<f)(bp:0 < v')(hr:∀ m:Side,k ≤ (mid m B).val →∀ F:Jill.Male, f*( (mid m B).val:ℝ)^(-(d:ℤ))*Kea.angel m P F ≤ ‖Kea.AMP m P (needles (mid m B)) F‖ ) : ∀ᶠ i in atTop, 0< fees (N i) B L0 L' γ s' (x i) f H0 d ∧ Tango (N i) B (finiteForm Y P (I i) (X i)) (compassRate (mid (N i) B) (hemp x i)) (fees (N i) B L0 L' γ s' (x i) f H0 d) v':=by
 obtain ⟨g,h,h'⟩:= income D Z X u H h₀; obtain ⟨k',v⟩:= has_beat j D.p (2*v'+1) (by positivity)
 filter_upwards [U,(tilt_kin D Z f d bf hr),h',Z.tend.eventually_ge_atTop k,Z.tend.eventually_ge_atTop k', h.shrinks.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with i u ⟨a,V⟩ ⟨b,H⟩ he hk F
 let Y:=rawPaid (N i) B L0 L' γ s' (x i)/2; let y':=(f/(n i^d))*Y; have ha:0<y':=mul_pos (by have h:n i>0:=nPos _; positivity) a
 refine ⟨(show 0 < y'/2/Real.exp (budgetCharge (I i) (soaked (x i)) H0) from (by positivity)), tango_cost D (I i) (X i) u V (fun i s=>?_) (v _ (Nat.cast_le.mp hk) ((D.plan _ (Nat.cast_le.mp he)).2.1)) (Nat.cast_le.mp he) bp ha.le⟩; exact (H _ s).trans (mul_le_mul_of_nonneg_right F b.le)
end Pastures
end YM.CF.Window
