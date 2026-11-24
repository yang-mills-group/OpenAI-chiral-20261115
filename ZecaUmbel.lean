import ZecaCosi
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)

local notation "ξ"=> P.advocate 3 x j
local notation "EH"=>P.physicalEnergy j ξ
local notation "M"=> P.ColorHil j ξ
local notation "Ω"=> P.colorZero j ξ
local notation "Μ"=> timeMesh P.par



local notation "G"=>P.ManyF j ξ


local notation "Nm"=> (2:ℝ)
section preprice
private lemma power_fit (i d:ℕ) (u:ℝ)(p:0<u)(t:u≤1):
 ∃ n:ℕ, i≤n ∧ 1/Nm^n≤u ∧ (Nm^n)^d ≤ (Nm^(i+1))^d /u^d:=by
 have he:Tendsto (fun n:ℕ=>1/Nm^n) atTop (𝓝 0):=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
 obtain ⟨n,g,h⟩:= ((eventually_ge_atTop i).and (he.eventually (gt_mem_nhds p))).exists
 have hz:∃ n:ℕ,i≤n∧1/Nm^n≤u:=⟨n,g,(show 1/Nm^n<u from h).le⟩
 classical
 let a:=Nat.find hz
 have p₀:i≤a ∧ 1/Nm^a≤u:=Nat.find_spec hz
 refine ⟨a,p₀.1,p₀.2,(le_div_iff₀ (pow_pos p d)).mpr ?_⟩
 rw [←mul_pow]
 apply pow_le_pow_left₀ (by positivity)

 have d₀:1<Nm:=by norm_num
 rcases p₀.1.eq_or_lt with h'|h'
 · rw [← h',pow_succ]; gcongr; exact t.trans d₀.le
 obtain ⟨m,j₀⟩:=Nat.exists_eq_succ_of_ne_zero (show a≠0 from by omega)
 have mp:i≤ m:=by omega
 have :u < 1/Nm^m:=lt_of_not_ge (fun c=>Nat.find_min hz (show m<a from by omega) ⟨mp,c⟩)
 have h'':1≤ Nm^i:=one_le_pow₀ d₀.le
 rw [j₀,pow_succ,pow_succ]
 have hq:Nm^m*u≤1:=(mul_comm ..).trans_le ((lt_div_iff₀ (pow_pos (by norm_num) _)).mp this).le
 linarith
end preprice

def AllFares (f k s:ℕ)(u:ℝ):Prop:=k≤ s ∧ ∀ j:Axis,
  P.rosePad j s≤ u ∧ ∀ l, Odessa j (P.roseRoot f s l) s (P.roseWide j s) P

lemma all_earns : ∀ᶠ n:ℕ in atTop,P.AllFares f k (2*n) (1/Nm^n):=by
 have h:Tendsto (fun n:ℕ=>2*n) atTop atTop:=tendsto_atTop_mono
   (f:=fun n:ℕ=>n) (fun n=> by omega) tendsto_id
 apply (h.eventually (eventually_ge_atTop k)).and
 rw [eventually_all]
 intro j
 filter_upwards [h.eventually (P.rose_license j),
       (P.rose_rapid j).eventually (gt_mem_nhds zero_lt_one)] with n ht u
 exact ⟨(le_div_iff₀ (by positivity)).mpr ((mul_comm ..).trans_le u.le), ht f⟩

lemma all_affords(c:ℝ) :∃ (B:ℝ)(d:ℕ),0<B ∧ ∀ t:ℝ,0<t→t≤1→
  ∃ s,P.AllFares f k s t ∧ orbitRent c P (s+1) ≤ B/t^d:=by
 obtain ⟨n,ht⟩:=eventually_atTop.mp (P.all_earns (f:=f) (k:=k))
 let z:=zoomC L
 have zp:0<z:=zero_lt_one.trans_le (zoomC_p ..)
 obtain ⟨d,h⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show 1<Nm by norm_num)).eventually
                      (eventually_ge_atTop (z^2))).exists
 have h': z^2≤ Nm^d:=h
 let C:=(|c|+1)*4*z
 refine ⟨C*(Nm^(n+1))^d,d,by unfold C;positivity,?_⟩
 intro t e y
 obtain ⟨a,p,q,b⟩:=power_fit n d t e y
 have g:=ht a p
 refine ⟨2*a,⟨g.1,fun j=>⟨(g.2 j).1.trans q,(g.2 j).2⟩⟩,?_⟩
 rw [mul_div_assoc]
 apply le_trans ?_ (mul_le_mul_of_nonneg_left b (show 0≤C from by unfold C;positivity))
 have r₀: z^(2*a) ≤ (Nm^a)^d:=by
    rw [← pow_mul,mul_comm a,pow_mul,pow_mul];gcongr -- RHS first? 
 unfold orbitRent C z at *
 rw [pow_succ, ←mul_assoc]
 rw [show (|c|+1)*4*zoomC L^(2*a)*zoomC L=(|c|+1)*4*zoomC L *zoomC L^(2*a) from by ring]
 gcongr

structure Folding (P:Spine) (x:P.Spectrum0 3)
    (f:ℕ)(u:ℕ→ℕ)(c:ℕ→ℝ) :Prop where
 goes:Tendsto u atTop atTop
 bill:∃ (B:ℝ)(d:ℕ),0<B ∧ ∀ t:ℝ,0<t→t≤1→∀ᶠ i:ℕ in atTop,
    ∀ (a b:ℝ), t ≤ a → t≤ b → ∀ j l, ‖(c i:ℂ) • P.crop j x f (u i) l a b‖≤ B / t^d
 charge:∀ (j:Axis)(l:List Axis)(a b:ℝ),0<a→0<b→
     ∃ T,Tendsto (fun i=>(c i:ℂ) • P.crop j x f (u i) l a b) atTop (𝓝 T)
-- applies on all axes
lemma folding {A C c:ℝ}{u:ℕ→ℕ}{y:ℕ→ℕ × ℕ→ℝ}
      (p:Skyways P f k A C c u y)(e:P.NightCop) :
      Folding P x f u (fun i=>c*y i (f,k)):= by
 obtain ⟨B,d,jB,h⟩:= P.all_affords c (f:=f) (k:=k)
 have pos:0<P.scaleCosy A:=P.scaleCosy_p
 refine ⟨p.post.tendsto_atTop, ⟨B*scaleCosy P A,d,mul_pos jB pos,?_⟩,?_⟩

 · intro t q m
   obtain ⟨s,h₁,h₂⟩:=h _ q m
   filter_upwards [p.post.tendsto_atTop.eventually (eventually_gt_atTop s)] with i v a b w g j l
   have Hs: P.rosePad j s ≤ t:=(h₁.2 j).1
   refine (P.violet_norm j x l p e h₁.1 ((h₁.2 j).2 l) (Hs.trans w)
           (Hs.trans g) v).trans ?_
   exact (mul_le_mul_of_nonneg_right h₂ pos.le).trans_eq (by ring)
 intro j l a b d₁ d₂
 have hp:0< min 1 (min a b):=lt_min zero_lt_one (lt_min d₁ d₂)
 obtain ⟨s,h₀,-⟩:=h _ hp (min_le_left ..)
 have Hs:= (h₀.2 j).1.trans (min_le_right ..)
 exact P.violet_joins j x l p e h₀.1 ((h₀.2 j).2 l) (Hs.trans (min_le_left ..)) (Hs.trans (min_le_right ..))

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.folding
