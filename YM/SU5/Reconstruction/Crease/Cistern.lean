import YM.SU5.Reconstruction.Crease.Regional
import YM.SU5.Reconstruction.Crease.Diagonal
import YM.SU5.Reconstruction.Crease.Launch
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
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
open CrossedFrame Clasp
local notation "Φ"=> Flare Y H V G C a χ F j z b
local notation "ℶ"=> Flare Y H V G C a χ F z j b.symm
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Ξ"=>parcelUp (S₀ j)
local notation "Λ₁"=>Sight Y H V G C a χ j
local notation "ℓ"=>Wing Y H V G C a χ j
local notation "ζ"=>floor Y H V G C a χ j
local notation "Ω" => Ω₀ j
local notation "P" => Z.plume
local notation "R" => Z.shadow
local notation "J" => (Φ).f
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
-- allow spatial-time pin as specified
include F p
lemma lamp (u v :Axis→ Gt)(A:(G₀ j).Op)(s:Λ₁ u v A)(hq:0<(u z:ℝ)) : P ((Φ).f (star A Ω))= R (A Ω):=by
 obtain ⟨g,h,x,B,k0,hx,e⟩:=s; obtain ⟨T0,t⟩:=e z b.symm
 choose Y' L U ε using fun n=> second_mirror Y H V G C a χ F j z b Z p u v (x n) (h n) (k0.phase n) (B n) (k0.stays n) (hx n) hq (g z b.symm) (T0 n) (t.beyond n)
 obtain ⟨d,v⟩:= t.bounded; let kalpha(n:ℕ):= Picket.trans (S₀ z) ((h n:ℝ) • basis j); let bank(n:ℕ):= (Π j) (B n)
 refine BridgeClub.press Z (Φ) (ℶ) atTop (A Ω) (star A Ω) (fun n=>(bank n) Ω) (fun n=>(star (bank n) Ω)) Y' kalpha L U (deep_after Y H V G C a χ F j z b Z p) (fun x=> k0.propitious.confirms x Ω) (fun x=>(star_Limited k0.propitious).confirms x Ω) d (fun i=>(ε i).trans (v i)) ?_
 intro x; unfold kalpha; simp_rw [Picket.trans_star]
 have he: Tendsto (fun i=> -((h i:ℝ) • basis j)) atTop (𝓝 0):= by simpa using (k0.short.smul (tendsto_const_nhds (x:=basis j))).neg
 have hm : x = Picket.trans (S₀ z) 0 x:=by rw [show Picket.trans (S₀ z) 0=1 from (S₀ z).unit.origin]; rfl
 nth_rw 2 [hm]; exact (((S₀ z).unit.moves x).tendsto _).comp he
omit F p
-- plain graph at Plus W. permit either exact 0 or any stereoscopic p times REAL $κ$ boost. Rank via sum canonical P+R. Take no hypothesis graph invariance of boosts on wedge algebras.
noncomputable def pinpoints : Set (G₀ j).Op:= {A| ∃ (u v:Axis→Gt)(B:(G₀ j).Op),0 < (u z:ℝ) ∧ Λ₁ u v B ∧ (A=B ∨ ∃ (r:Gt)(t:ℝ), 0< (r:ℝ) ∧ A= Ξ (stern j z t (r:ℝ)) B)}
local notation "Γ"=> pinpoints Y H V G C a χ j z
include b F
lemma point_prices (A:(G₀ j).Op)(t:A∈Γ):star A∈ Γ:= by
 obtain ⟨u,v,B,h,d,rfl|⟨r,x,d',rfl⟩⟩:=t
 · exact ⟨u,v,star A,h,adjSight Y H V G C a χ F j u v A d,Or.inl rfl⟩
 exact ⟨u,v,star B,h,adjSight Y H V G C a χ F j u v B d,Or.inr ⟨r,x,d',parcel_star ..⟩⟩
local notation "Sq"=> Wedge j z
lemma point_awake (A:(G₀ j).Op)(t:A∈Γ): A ∈ ζ Sq:= by
 apply audition (ℓ Sq); obtain ⟨u,v,B,o,h,pq⟩:=t
 let ℓT:= Reel j (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ)); have he : ℓT⊆ Sq:=fun x p=>(show |x j|<x z from (p.1.symm ▸ (lt_of_eq_of_lt (_root_.abs_zero) (o.trans_le ((p.2 z b.symm).1))))) -- rw may subst x
 rcases pq with rfl|⟨r,x,q,rfl⟩
 · exact ⟨u,v,0,A,h,by rintro _ ⟨x,p,rfl⟩; simpa using he p,Eq.symm (parcel_zero ..)⟩ -- rfl: A var vs A
 exact ⟨u,v,stern j z x (r:ℝ),B,h,by rintro _ ⟨y,p,rfl⟩; exact scope_add j z (he p) (stern_p b.symm _ _ q), rfl⟩
omit F b
lemma keepsLaw (t:E4)(A:(G₀ j).Op): Ξ t A Ω=Picket.trans (S₀ j) t (A Ω):= by unfold BridgeClub.parcelUp; rw [mul_apply_eq_comp,mul_apply_eq_comp,show Picket.trans (S₀ j) (-t) Ω=Ω from compass_origin ..]
include b F p
lemma aboveUp (A:(G₀ j).Op)(t:A∈Γ): P (J (star A Ω))= R (A Ω):= by
 obtain ⟨u,v,B,kR,h,e⟩:=t; have hs:= lamp Y H V G C a χ F j z b Z p u v B h kR; rcases e with e|⟨r,x,g,rfl⟩
 · rw [e]; exact hs
 rw [parcel_star, keepsLaw,keepsLaw,← (Φ).shade_light, orbitF,stern_opp b.symm]; -- choose cost center
 let k:=(Pr j); have hp:= stepB Y H V G C a χ j z b.symm Z (F.present j) (F.present z) p.port (eject z r) (by simp [b]) (by simp [g.le]); rw [castSpace Y H V G C a χ j b.symm r, bridge_time] at hp
 exact courseGram Z b.symm (S₀ j) x (r:ℝ) _ hp ((S₀ z).stare _) (p.spins x).2 (B Ω) _ hs
-- rank. Actual purchases from Corridor
lemma engaged (h: Rank (Φ) Ω Γ): BridgeClub.Club Z (Φ) (ζ Sq) Ω Γ:= by
 refine ⟨(fun i e=>point_awake Y H V G C a χ F j z b i e), point_prices Y H V G C a χ F j z b, aboveUp Y H V G C a χ F j z b Z p,?_,stillHere Y H V G C a χ F j z b,h⟩
 intro x e; have t:= reflection_bound Y H V G C a χ F j z b Sq (Counter j z) (by rintro _ ⟨i,h,rfl⟩; exact (BridgeClub.turning j z i).mpr h) x e
 have hv:= spacelike Y H V G C a χ F j Sq (Counter j z) (room_separated j z b)
 apply VonNeumannAlgebra.mem_commutant_iff.mpr; intro i p; exact (VonNeumannAlgebra.mem_commutant_iff.mp (hv p) _ t).symm
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
