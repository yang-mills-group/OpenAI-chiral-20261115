import YM.SU5.Reconstruction.Sleet.Squaw
/-! # Paying the universal speed-bound on this posture -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter Metric Function MeasureTheory Spectral Analysis
open scoped Topology ComplexOrder NNReal ENNReal InnerProductSpace Real Classical
open Complex CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis OS Semigroup Picket Boundary Probe Snowball
variable {H : Hilbert} {a : Axis} {Γ : AddSubgroup ℝ} (S : OS.Semigroup H a)
variable (d : Dense (Γ:Set ℝ)) (X : Sunbelt a Γ H)
  (g : ∀ i,∀ (z : Γ) (t:ℝ≥0), ((X.track.crew i).play z).comp (S.E t)=(S.E t).comp ((X.track.crew i).play z))
local notation "C₀" => X.track.aviator X.list
local notation "U" => glass X d S g
local notation "G₀" => X.track.Realm X.list
local notation "D₁" => {i:Axis//i≠a}
variable (j : {i:Axis//i≠a})(f: X.track.Realm X.list)
local notation "Ecc"=> X.track.crew j

-- wing consultation. Obtain unconditionally from OTHER axis physical law at this diagnosis (next files).
structure Blizzard (S:OS.Semigroup H a)(Y:Players Γ H)(x:H)(b Q:ℝ): Prop where
  grants(s:Γ) (w:0≤(s:ℝ)): ∃ F:ℂ→ℂ, AnalyticOnNhd ℂ F (rightWork b) ∧ (∀ t∈ rightWork b, ‖F t‖≤ Q) ∧ ∀ u:Γ,b<(u:ℝ)→ F (↑(u:ℝ))=radiation S Y x s u
  pos:0<b

variable {r:Γ}(hr:0≤(r:ℝ))
variable {C b Q:ℝ}
include hr
lemma Blizzard.fittings (p: Blizzard S (X.track.crew j) f.val b Q): InPocket Q b (tundra (glass X d S g) j.val f (r:ℝ)):=by
 obtain ⟨F,e,t,v⟩:= p.grants r hr; refine ⟨F,e,t,?_⟩
 have hg : Continuous (tundra (U) j.val f (r:ℝ)):=by have ht:= perennity (U) _ j.property f ((r:ℝ).toNNReal); rwa [Real.coe_toNNReal _ hr] at ht
 refine fun x H=> cursor d (isOpen_Ioi (a:=b)) (e.continuousOn.comp continuous_ofReal.continuousOn (fun i (p:b < i)=>  (show b<(i:ℂ).re from p))) hg.continuousOn (fun u hU=> (v u hU).trans (climate S d X g j f r u hr).symm) (show x ∈ Ioi b from H) -- fix

variable (p:Reflex S (X.track.crew j) f.val r C)(k:Blizzard S (X.track.crew j) f.val b Q)
include p hr k
lemma missing_lane: let μ:= (glass X d S g).ℚmeasure.diagonal f
                    ∀ y∈ μ.support, |y j.val|≤ y a:= by
 intro μ y t
 have ht:Crystalline μ (heightP a) (spatialP j.val) (r:ℝ) b C Q:=by
    refine ⟨k.pos,hr, frequently_atTop.mpr ?_⟩; intro R
    obtain ⟨q,l,e⟩:= d.exists_mem_open isOpen_Ioi (show (Set.Ioi (max R 0)).Nonempty from Set.nonempty_Ioi); let v:Shard Γ:=⟨⟨q,l⟩,(le_max_right R 0).trans_lt e⟩; let s:= r+v.val+v.val; have hv: (s:ℝ)=(r:ℝ)+q+q:=by unfold s;rw [AddSubgroup.coe_add,AddSubgroup.coe_add]
    have hp:q>max R 0:= e; have h:q ≥0:=by linarith [le_max_right R (0:ℝ)]
    exact ⟨s,(by rw [hv]; linarith [le_max_left R (0:ℝ)]), northern S d X g j f hr p v,Blizzard.fittings S d X g j f (r:=s) (by rw [hv];linarith) k⟩
 have he := ht.forces μ (heightP a) (spatialP j.val) (by unfold heightP;fun_prop) (by unfold spatialP;fun_prop) (fun x=>le_max_left ..) y t
 rwa [heightP,max_eq_right ((U).nonneg f t)] at he
-- no temperature support ghosts in the spectrum of this cost. Now reclaim that very CP5 inequality from this test x.
include d g
lemma drops (s:Γ)(h:0<(s:ℝ)): let t:= (face (byStamp a j.val s) a).toNNReal;
                               ‖(S.E t) (transverse_play X (byStamp a j.val s) f.val)- S.E t f.val‖ ≤ ‖f.val - S.E t f.val‖:= by
 apply (buy_clear S d X g f _).1; unfold clears
 obtain ⟨hx,hw,_⟩:= spotlight2 X s j s
 unfold byStamp; rw [hw,show (diameter (a:=a) _)=(s:ℝ) • Picket.cross a j.val j.property from Subtype.ext hx]; have ht:= retunes (U) _ j.property f (missing_lane S d X g j f hr p k) (s:ℝ).toNNReal; dsimp only at ht; rw [show (Real.toNNReal (s:ℝ)).val=(s:ℝ) from Real.coe_toNNReal _ h.le] at ht; exact ht
end YM.ConePrice.Storm
