import YM.SU5.Reconstruction.Quartz.Coup
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
open YM.Quartz YM.Quartz.Waltz YM.Quartz.Ship
local notation "Qv"=> Picket.quarter j z
local notation "Lvl" i:max=>floor Y H V G C a χ i
local notation "Uj" i:max=>Picket.trans (S₀ i)
local notation "Oh" i:max=>parcelUp (S₀ i)
local notation "Wj"=> Wedge j z
local notation "Wz"=> Counter z j
local notation "M₁"=> (Lvl j) Wj
local notation "M₂"=> (Lvl z) Wz
local notation "ι"=> Z.look.conjStarAlgEquiv
local notation "Cj" i:max k:max bj:max=> Creased Y H V G C a χ F i k bj
local notation "Dₘ"=> floor Y H V G C a χ z (Wedge z j)
local notation "Yₒ"=> Z.look.symm.conjStarAlgEquiv
local notation "Leg"=> volunteer Y H V G C a χ j z
variable (r:Creased Y H V G C a χ F z j b.symm)
include F b p r
lemma lend (t M R:ℝ) (e: M+ 3*R≤ Real.exp (-3)*t)(v:0≤t)(B:(G₀ z).Op)(h:B∈ (Lvl z) (hikeWorld (Wedge z j) (t • basis j))) : Worth (b:=j) (S₀ z) Z.Back B R (ticketCrew Y H V G C a χ j z (M • basis j)) := by
 let u:= back_quarter Y H V G C a χ F j z b Z p; let D'ₘ:= Dₘ; let P:= Wedge z j; let k0:= t • basis j; let M0:= M • basis j
 intro s g x wx A l y k
 let V₁:= (Picket.move z j s k0); let d:= path z j (x+y,y); let d' := V₁+d-M0;
 have h1: ascend s Z.Back B∈ (Lvl z) (hikeWorld P V₁):= by
    have hp:= (transported_room Y H V G C a χ F z j b.symm Z.Back u r s k0 true B).1 h; rw[eitherShift b] at hp; exact hp
 have h2: stowed z j d':= by rw [show d'= d+V₁-M0 from congrArg (·-M0) (add_comm ..)]; rw [show d=path z j (y+x,y) from (by simp [d,add_comm])]; exact steward b g v k wx e -- tune ht/hδ
 let B' := rateTime (b:=j) (S₀ z) (ascend s Z.Back B) (x+y,y); have eh:B'∈ (Lvl z) (hikeWorld P M0):= by
   apply translation_bound Y H V G C a χ F z _ (hikeWorld P M0) d _ _ h1; rintro _ ⟨_,⟨i,hi,rfl⟩,rfl⟩; exact ⟨i+d',sun_plus hi h2,(show i+d'+M0= (i+V₁)+d from (by unfold d'; abel))⟩
 obtain ⟨X',z0,hx⟩:= ascentW Y H V G C a χ F z A M0 (Counter z j) l; obtain ⟨x',h₀,hx'⟩:= ascentW Y H V G C a χ F z B' M0 (Wedge z j) eh
 change A*B'=B'*A; rw[hx,hx',←parcel_mul,← parcel_mul]; apply congrArg; exact (VonNeumannAlgebra.mem_commutant_iff.mp (foes Y H V G C a χ F z j b.symm z0) x' h₀).symm -- `foes` param
lemma chief (A:(G₀ j).Op)(i:A∈ volunteer Y H V G C a χ j z): ∃ t>(0:ℝ), (Oh z) (-(t • basis j)) ((ι) A)∈M₂:=by
 obtain ⟨u,v,d,e⟩:=i; obtain ⟨W',M,c,q,h⟩:=e -- unfold? i∈ ... uses Engages
 let δ:=( (u z:ℝ)+(v z:ℝ)); let UpT:= Real.toNNReal δ
 have d': (UpT:ℝ) = δ:= Real.coe_toNNReal δ (add_nonneg d.le (q.posv z b.symm).le)
 let R:= scud (UpT:ℝ) (6*ceilingCost (UpT:ℝ))
 obtain ⟨t,v',k⟩:= adequate M R; refine ⟨t,v',?_⟩; let pz:= back_quarter Y H V G C a χ F j z b Z p
 let Lx:= A*(Uj j) (δ • basis z)
 obtain ⟨g,Gₚ⟩:= echoPowered Z Lx W' (bookedEcho Y H V G C a χ F j z b Z p u v A W' q); have ht: ι Lx= (ι A)*(Uj z) (-((UpT:ℝ) • basis j)):=by unfold Lx; rw[map_mul,movedInto Y H V G C a χ j z b Z p,quarterCare Y H V G C a χ j z b Z p,d']
 let s:= t • basis j; rw [← equalsShade Y H V G C a χ F z j b.symm Z.Back pz r]; refine VonNeumannAlgebra.mem_commutant_iff.mpr (fun x y=> ?_)
 let B:=(Oh z) s x; have x':B∈(Lvl z) (hikeWorld (Wedge z j) (t • basis j)):= (translation_cov Y H V G C a χ F z (Wedge z j) s x).1 y
 have he:= basement (p:=b) (S:= (S₀ z)) (C:=Z.Back) (B:=B) («X»:=(ι) Lx) (W:=W') (d:= UpT) _ g Gₚ (fun s=>(pz.spins s).2) c (lend Y H V G C a χ F j z b Z p r t M R k v'.le B x') h -- tune `N'` explicit
 have hi:= loomComm (S₀ z) _ _ B ht he -- order `(A:E.Op)(B:E.Op)(x:E.Op)` tune!
 have hyp:x= (Oh z) (-s) B:= (parcel_went ..).symm
 rw [hyp]; -- tune
 rw[← parcel_mul,← parcel_mul]; exact congrArg ((Oh z) (-s)) hi.eq.symm
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
