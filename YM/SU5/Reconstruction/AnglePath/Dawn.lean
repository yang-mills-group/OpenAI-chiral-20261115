import YM.SU5.Reconstruction.AnglePath.Framing
/-! # angular prices on this law CP. -/

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (P:Ramp)(e:RPos Y H V G P C a χ)(B:BoostBacking Y H V G C a χ)(W:Chat Y H V G P C a χ)
open CrossedFrame.Cardio _root_.YM.ConePrice.Storm.StepVoucher
local notation "S"=> SpinOn Y H V G C a χ P e
local notation "G₁" => Domain Y H G false (aperture P)
local notation "H₀" => Domain Y H G false (northD P)
local notation "U"=> audition Y H V G C a χ P P.a (stocks_a P)
local notation "Z"=> audition Y H V G C a χ P P.b (stocks_b P)
local notation "M"=> motor Y H V G C a χ B S (Oriented.rotateAB P)
local notation "R"=> retina Y H V G C a χ P e B
local notation "K₁"=> profile Y H V G C a χ P W
include V
lemma aperture_move {x : Sky (tent Y H)}(u:x∈G₁)(v:placement Λ)(p:0≤(coordinates Λ v P.a))(q:0≤(coordinates Λ v P.b)): move K v x∈ G₁:=by
 refine domain_mono Y H G ?_ (moving Y H V G v _ u); rintro _ ⟨X,⟨⟨a,b⟩,t⟩,rfl⟩; refine ⟨⟨add_nonneg (b:=(coordinates Λ v P.a)) a p, add_nonneg b q⟩,?_⟩
 show 0<landN P (X+ _); rw[map_add]; exact add_pos_of_pos_of_nonneg t (add_nonneg p q)
local notation "κ"=> treks Y H V G P
lemma aperture_event (x:H₀) : ∃ M':ℝ,∀ r:Gt,M'<(r:ℝ) → move K (billT P r) x.val∈ G₁:= by
 obtain ⟨T,h,e,p⟩:=(compact_domain Y H G).1 x.property
 obtain ⟨A,w⟩:=(h.image (continuous_apply P.a)).bddBelow; obtain ⟨B,w'⟩:= (h.image (continuous_apply P.b)).bddBelow
 refine ⟨max (-A) (-B),fun r v=> domain_mono Y H G ?_ (moving Y H V G (billT P r) x.val p)⟩
 rintro _ ⟨z,k,rfl⟩; let V':= z+coordinates Λ (billT P r)
 have p:0<V' P.a:= by have e:A≤z P.a:= w (mem_image_of_mem _ k); change 0<z P.a+(terrainK _ _ r r _).val; rw[terrain_time P.cross]; linarith[le_max_left (-A) (-B)]
 have q:0<V' P.b:= by have e:B≤z P.b:= w' (mem_image_of_mem _ k); change 0<z P.b+(terrainK _ _ r r _).val; rw[terrain_space]; linarith[le_max_right (-A) (-B)]
 exact ⟨⟨p.le,q.le⟩,add_pos p q⟩
lemma aperture_dawn (x:H₀): ∃ r:Gt,∃ p:0<(r:ℝ),∃ y:H₀, x= κ r p.le y:= by
 obtain ⟨T,h,e,p⟩:=(compact_domain Y H G).1 x.property
 have mx:∃ k:ℝ,0<k∧∀ x∈ T, k<landN P x:=by
    rcases T.eq_empty_or_nonempty with v|u
    · exact ⟨1,zero_lt_one,fun i p=> by rw [v] at p; exact p.elim⟩ -- replace
    obtain ⟨x,t,z⟩:= h.exists_isMinOn u (landNp P).continuousOn; have K':0<landN P x:=e t; exact ⟨landN P x/2,by positivity,fun y p=> (half_lt_self K').trans_le (z p)⟩
 obtain ⟨k,o,Mk⟩:=mx; obtain ⟨r,sr,p'⟩:=(daylight (timeMesh Λ)).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (show 0<k/2 from half_pos o))
 let s:Gt:=⟨r,sr⟩; let B':=billT P s; have hT:move K (-B') x.val∈ H₀:=by
    refine domain_mono Y H G ?_ (moving Y H V G (-B') x.val p); rintro _ ⟨v,t,rfl⟩; change 0<landN P (v+coordinates Λ _); rw [map_add, hour_age,map_neg]; unfold B' billT; rw[hourMark,AddSubgroup.coe_neg,AddSubgroup.coe_add]; change 0 < landN P v + -(r+r); linarith [p'.2,Mk v t]
 refine ⟨s,p'.1,⟨_,hT⟩, Subtype.ext ?_⟩; change x.val=move K B' (move K (-B') x.val); rw [move_sum,add_neg_cancel,move_by_zero]
local notation "X" => footpath (fanoForm Y H V G P C a χ) W
lemma grants_rise (r:Gt)(p:0≤ (r:ℝ))(f:G₁):∃ y:G₁,(K₁) y= W.plant (κ r p (forwardG Y H G P f)):= by
 have h1:0≤coordinates Λ (billT P r) P.a:=by change 0≤(terrainK _ _ r r _).val; rw[terrain_time P.cross]; exact p
 have h2:0≤coordinates Λ (billT P r) P.b:=by change 0≤(terrainK _ _ r r _).val; rw[terrain_space]; exact p
 exact ⟨⟨_,aperture_move Y H V G P f.property _ h1 h2⟩,rfl⟩
local notation "T"=>radial Y H V G P C a χ W
local notation "K₁'"=> (LinearMap.range K₁).topologicalClosure
private lemma stead_range (r:Gt)(h:0<(r:ℝ)) (f:W.H) (g:f ∈K₁') : T r h.le f∈K₁':=by
 let U':= T r h.le; let A:= LinearMap.range K₁; let A':= A.topologicalClosure; have he:IsClosed (A':Set W.H):=Submodule.isClosed_topologicalClosure _
 apply closure_minimal (s:=(A:Set W.H)) (t:=(U' ⁻¹' (A':Set W.H))) _ (he.preimage U'.continuous) g
 rintro _ ⟨x,rfl⟩; change U' (K₁ x)∈A'; apply Submodule.le_topologicalClosure A
 obtain ⟨z,e⟩:= grants_rise Y H V G C a χ P W r h.le x; exact ⟨z,e.trans ((service Y H V G P C a χ W _ h.le).2 (forwardG Y H G P x)).symm⟩
private lemma reach (r:Gt)(h:0<(r:ℝ))(z:H₀): ∃ n:ℕ, ((T r h.le)^n) (W.plant z)∈ K₁':= by
 obtain ⟨B,c⟩:=aperture_event Y H V G P z
 obtain ⟨n,s⟩:=exists_nat_gt (B/r.val)
 let p:= n • r; have hp: 0≤(p:ℝ):=cast_Δ r n h.le
 have ht:B<(p:ℝ) := by unfold p; rw [AddSubgroup.coe_nsmul,nsmul_eq_mul]; exact (div_lt_iff₀ h).mp s
 let y:G₁:=⟨_, c p ht⟩
 have Z':(K₁) y =W.plant (κ p hp z):= rfl
 have eq:T p hp (W.plant z)=W.plant (κ p hp z):=(service Y H V G P C a χ W p hp).2 z
 -- compare maps separately. avoid rfl coercion hell
 have g:T p hp=(T r h.le)^n:=(ticks Y H V G P C a χ W r h.le n).symm
 have x : K₁ y = ((T r h.le)^n) (W.plant z):= Z'.trans (eq.symm.trans (congrArg (fun v:W.H.Op=> v (W.plant z)) g))
 exact ⟨n, Submodule.le_topologicalClosure (LinearMap.range K₁) (LinearMap.mem_range.mpr ⟨y,x⟩)⟩
lemma steady_d : DenseRange K₁:= by
 let A:= LinearMap.range K₁; let A':= A.topologicalClosure; have he:IsClosed (A':Set W.H):=Submodule.isClosed_topologicalClosure A
 have e:(closure (Set.range K₁) = A'):=rfl
 intro x; change x∈(A':Set W.H); refine closure_minimal (t:=(A':Set W.H)) ?_ he (everyone _ W x)
 rintro y ⟨t,rfl⟩; obtain ⟨r,h,z,hz⟩:= aperture_dawn Y H V G P t
 let U':=radial Y H V G P C a χ W r h.le
 have hp: W.plant t=U' (W.plant z):=by unfold U'; rw [(service Y H V G P C a χ W _ h.le).2,hz]
 change W.plant t∈A'; rw [hp]; exact inductReach (H:=W.H) A' U' (IsSelfAdjoint.of_nonneg (positive_speed Y H V G P C a χ W r h.le)) (W.plant z) he (stead_range Y H V G C a χ P W r h) (reach Y H V G C a χ P W r h z)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
