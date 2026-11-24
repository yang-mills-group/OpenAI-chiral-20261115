import YM.SU5.Reconstruction.Sleet.Anomaly
/-! # In the cont spectator climatology. Turn one way. -/
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
include g
lemma climate (s t:Γ)(p:0≤(s:ℝ)): tundra (glass X d S g) j.val f (s:ℝ) (t:ℝ)= radiation S Ecc f.val s t:=by
 let Z:=(Real.toNNReal (s:ℝ)); have h:tundra (U) j.val f (s:ℝ) (t:ℝ)= inner ℂ f ((U).U ((t:ℝ) • cross a j.val j.property) ((U).E Z f)):= by have ht:= shift_dials (U) _ j.property f Z (t:ℝ); rwa [show (Z:ℝ)=(s:ℝ) from Real.coe_toNNReal _ p] at ht
 let v:= Function.update (Function.update (0:Axis→Γ) a s) j.val t; obtain ⟨x,y,e⟩:= spotlight2 X s j t
 rw [h,← ContinuousLinearMap.comp_apply ( (U).U _), ← (U).independent, ContinuousLinearMap.comp_apply ( (U).E _)]
 rw [show (t:ℝ) • Picket.cross a j.val j.property= diameter (a:=a) (face v) from Subtype.ext x.symm]
 apply congrArg (fun x:H=> inner ℂ (f.val:H) x) (?_:(( (U).E Z ( (U).U (diameter (a:=a) (face v)) f)):C₀).val=_)
 rw [glass_heat,glass_move]; rw [←e] -- unfolding? 
omit g
variable {A:Set ℝ}
include d in
lemma cursor {U₁ V:ℝ→ℂ}(h:IsOpen A)(p:ContinuousOn U₁ A)(q:ContinuousOn V A)(g:∀ x:Γ,(x:ℝ)∈A→ U₁ (x:ℝ)=V (x:ℝ)): EqOn U₁ V A:=by
 intro u t; haveI : NeBot (𝓝[A∩ (Γ:Set ℝ)] u):= mem_closure_iff_nhdsWithin_neBot.mp (d.open_subset_closure_inter h t)
 have ht: (𝓝[A∩ (Γ:Set ℝ)] u)≤𝓝[A] u:= nhdsWithin_mono _ inter_subset_left
 apply tendsto_nhds_unique ((p u t).mono_left ht) (((q u t).mono_left ht).congr' ?_)
 filter_upwards [self_mem_nhdsWithin] with i t; exact (g ⟨i,t.2⟩ t.1).symm
variable {r:Γ}(hr:0≤(r:ℝ))
variable {C:ℝ} (Q:Reflex S (X.track.crew j) (f.val:H) r C) -- f is subtype? macro f.val
include g hr Q
set_option maxHeartbeats 320000 in
lemma northern (v:Shard Γ): let s:=r+v.val+v.val
                            Weatherproof C ((s:ℝ)-(r:ℝ)) (tundra (glass X d S g) j.val f (s:ℝ)):=by
 intro s; obtain ⟨F,G,k,y⟩:= Reflex.weather d S Ecc (g j) _ Q -- arg order check
 let R:= thermal v; let u(z:ℂ):=(R:ℂ)+z/2; let w(z:ℂ):=(R:ℂ)-z/2; let V(z:ℂ):= sally F (u z) (w z); let D:= watch ((s:ℝ)-(r:ℝ))
 let Y:= tundra (U) j.val f (s:ℝ)
 have hs: (s:ℝ)-(r:ℝ)=2*R:=by unfold R thermal s; push_cast; change r.val+v.val.val+v.val.val-r.val=_; ring
 have hR:0<R:= thermal_pos v
 have hv(z:ℂ)(e:z∈ D): Towerbound (u z) (w z):=by
    unfold D at e; rw [hs] at e; have he:= Metric.mem_ball.mp e
    apply deck; rw [norm_div, norm_ofNat]; rw [dist_zero_right] at he; linarith
 have hV: AnalyticOnNhd ℂ V D:= accountCurve k Metric.isOpen_ball hv (fun z _=> (by unfold u; fun_prop)) (fun z _=> (by unfold w; fun_prop))
 have hY : Continuous Y:= by have he:=perennity (U) _ j.property f (Real.toNNReal (s:ℝ)); rw [Real.coe_toNNReal _ (by linarith:0≤(s:ℝ))] at he; exact he
 have hc(x:ℝ): (↑x:ℂ)∈ D ↔ |x|<2*R:= by unfold D;rw [hs]; change _↔ _; simp [watch,Metric.mem_ball, Real.norm_eq_abs]
 let S₀:={x:ℝ| (↑(2*x):ℂ)∈ D}; have hc2(x:ℝ): x∈S₀↔|x|< R := by unfold S₀; rw [mem_setOf_eq,hc,abs_mul,abs_of_pos (show (0:ℝ)<2 by norm_num),mul_lt_mul_iff_right₀ (by norm_num:(0:ℝ)<2)]
 have hop:IsOpen S₀:=(isOpen_ball (x:=(0:ℂ))).preimage (f:=fun x:ℝ=>(↑(2*x):ℂ)) (by fun_prop) -- tune
 have hu: EqOn (fun x:ℝ=>V ((2*x:ℝ):ℂ)) (fun x:ℝ=> Y (2*x)) S₀:= by
    refine cursor d hop (hV.continuousOn.comp (Continuous.continuousOn (by fun_prop)) (fun i h=>h)) ((Continuous.comp' hY (f:=fun x:ℝ=>2*x) (by fun_prop)).continuousOn) ?_
    intro z hz; obtain ⟨h1,h2⟩:=abs_lt.mp ((hc2 z).1 hz)
    have ht: -(v.val:ℝ)<(z:ℝ) ∧ (z:ℝ)< (v.val:ℝ):= ⟨h1,h2⟩
    let L:Shard Γ:=⟨v.val+z,by rw [AddSubgroup.coe_add]; linarith [ht.1]⟩; let N:Shard Γ:=⟨v.val-z,by rw [AddSubgroup.coe_sub]; linarith [ht.2]⟩
    let t:=(↑(2*(z:ℝ)):ℂ)
    have hE:thermal L=R+(z:ℝ) := by change ((↑(v.val+z):ℝ))= _; rw [AddSubgroup.coe_add]; rfl
    have hN:thermal N=R-(z:ℝ):= by change ((↑(v.val-z):ℝ))=_; rw [AddSubgroup.coe_sub]; rfl
    change sally F (u t) (w t)= Y _
    rw [show u t= thermal L from (by unfold u t; rw [hE]; push_cast;ring), show w t=thermal N from by unfold w t; rw [hN]; push_cast;ring]
    rw [sally_land k _ (thermal_pos L) _ (assigned_ground (thermal_pos N)), (y L N).1]; unfold tiltTest; rw [show r+L.val+N.val=s from by change r + (v.val+z) + (v.val-z)=r+_+_; abel, show L.val-N.val=z+z from by change v.val+z-(v.val-z)=_; abel]; unfold Y; rw [show 2*(z:ℝ)= (↑(z+z):ℝ) from by push_cast; ring, climate S d X g j f s (z+z) (by linarith)]
 refine ⟨V,hV,fun z Z=> rocket k (hv z Z),fun x hx=>?_⟩; let q:=x/2; have he:2*q=x:=by unfold q;ring
 have hg:=hu (show q∈ S₀ from (by change (((2*q:ℝ):ℂ))∈D; rw [he]; exact hx)); dsimp only at hg; rwa [he] at hg
end YM.ConePrice.Storm
