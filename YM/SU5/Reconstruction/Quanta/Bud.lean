import YM.SU5.Reconstruction.Quanta.Candle
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
set_option linter.unusedVariables false -- h₁, V etc
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "au"=>move K
variable (P:Ramp)
local notation "H₀"=> Ark.Ht Y H G.history.circuit j 0 false (C j)
local notation "A"=>Aurora Y H V G.history j false (C j)
open PolarArchives
local notation "Pc"=>album Y H V G C j
local notation "pay"=> LightBudget.prepaid Y H V G j (C j)
local notation "vc"=>seat0 Y H V G.history j false (C j)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank j 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject j t)
variable {q:Bool}{U:Set RSpace}
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped j false (C j)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped j false (C j)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped j false (C j)
open Chambers Brazier
local notation "V₀"=> Nₐ
local notation "Rt" t:max=> Pub Y H j t
variable (m:MeshClock.marks (timeMesh Λ))(p:0< m)
local notation "xq" q:max=>Domain Y H G q (carton P (m:ℝ))
local notation "Cm"=> strip j (-(m:ℝ)) (m:ℝ)

open PolarArchives
variable {d:ℝ}{U:Set RSpace}
variable {s:ℕ} {f g:Dome (tent Y H)} {Y₁:Family (tent Y H)}
private lemma plot_min (W:Set RSpace)(a:IsCompact W):∃ d:ℝ,0≤d∧ W⊆strip j (-d) d:=by
 obtain ⟨u,A'⟩:= (a.image (continuous_apply j)).bddAbove; obtain ⟨v,B⟩:= (a.image (continuous_apply j)).bddBelow
 refine ⟨max 0 (max u (-v)),le_max_left ..,fun i t=>?_⟩
 have ht:=mem_image_of_mem (fun x:RSpace=>x j) t
 change -_≤ i j∧ i j≤ _; constructor; swap; · exact (A' ht).trans ((le_max_left ..).trans (le_max_right ..))
 linarith [le_max_right u (-v), le_max_right 0 (max u (-v)), (show v≤ i j from B ht)]
private lemma coincidence (f:Dome (tent Y H))(s:ℕ):∃ d:ℝ,0≤d∧ f∈ insideAt Λ l K false (strip j (-d) d) s:=by
 let S:=( (marque (tent Y H)).1 f.property).paid.choose
 have h:InTest K true S false f.val := _root_.Classical.choose_spec (((marque (tent Y H)).1 f.property).paid)
 obtain ⟨d,d',hd⟩:= plot_min j (bufferedHull Λ l s S) (compact_hull ..)
 exact ⟨d,d',(mem_insideAt ..).2 ⟨⟨_,h,(supported_iff ..).2 hd⟩,nofun⟩⟩
private lemma topEarn (d:ℝ)(m:Gt)(h:d< (m:ℝ))(t:0≤d): Disjoint (strip j (-d) d) (mirrorE j 0 '' flank j (m:ℝ)) ∧ Disjoint ((strip j (-d) d) ∪ mirrorE j 0 '' flank j (m:ℝ)) (flank j (m:ℝ)) :=by
 have hz : ∀ x∈ mirrorE j 0 '' flank j (m:ℝ), x j ≤ -(m:ℝ):=by rintro _ ⟨x,g,rfl⟩; simp [mirrorE]; exact g
 refine ⟨disjoint_left.mpr (fun x t v=>?_ ),disjoint_left.mpr (fun x v u=>?_ )⟩ -- bind implicit? sets
 · linarith [hz _ v,(show -d≤ x j from t.1)]
 replace u:(m:ℝ)≤x j:=u; rcases v with w|w;· linarith [(show x j≤ d from w.2)]
 linarith [hz _ w]
local notation "Cb" h:max => strip j (-h) h
local notation "UP" h:max => flank j h
section height
variable {b:Bool}{S:Finset Cover}(Hx:InTest (tent Y H) true S b Y₁)(hy:Tower.region j 0 ((tent Y H).ℓ) S)
    (kz:f.val=poleForm (tent Y H) j 0 b Y₁ Y₁)
-- powers of the ROOT grade amplifier
local notation "Px" h:max g:max => ticket Y H G h g
include V Hx hy kz
private lemma human {T₁:Finset Cover}(n:ℕ)(g:Dome (tent Y H))(hw:InTest (tent Y H) true T₁ false g.val)(u:Tower.region j 0 ((tent Y H).ℓ) T₁) :
    0 ≤ E (s+n) ((aureole K j 0 g).val * (spreadTo Y H G s (s+n) f).val * g.val):=by
 let W:= reflectedBox j 0 S∪ S -- union ambiguous
 have e:InTest K true W false (poleForm K j 0 b Y₁ Y₁):= NorthTapes.statement j 0 Hx Hx
 have hp:Heat.gaugeShift Λ.block 0=0:=by simp [Heat.gaugeShift]
 have ht := Garret.equipped Y H V s j 0 G.history n W Hx (hp.symm ▸ hy) hw (by rw [hp,mul_zero]; exact u) (hp.symm ▸ e)
 rw [hp,mul_zero] at ht; rw [spreadTo_val,kz, Nat.add_sub_cancel_left s n]; exact ht
-- earning genuinely beyond Sym planner operations at this state; no Odd covariance rule on G beyond proving these.
include p
lemma attends (v:f∈ insideAt Λ l K false (Cb d) s)(h:d<(m:ℝ))(t:0≤d) (x:Domain Y H G false (UP 0)):
    ∀ u: (Mirror j) ((Rt m) x.val)* Px s f *(Rt m) x.val ∈ Domain Y H G false Set.univ,
    0 ≤ courseValue Y H V G ⟨(Mirror j) ((Rt m) x.val)* Px s f *(Rt m) x.val,u⟩:=by
 let U₁:= flank j (m:ℝ); let U₂:= mirrorE j 0 '' U₁
 have he:(Rt m) x.val∈ Domain Y H G false U₁:=by simpa only [U₁,zero_add] using (pub_area Y H V G j (t:=m) x.val x.property)
 obtain ⟨s₁,⟨y,w,e⟩,u⟩:= (((domain_eventually Y H G).1 he).and (eventually_ge_atTop s)).exists
 obtain ⟨d',rfl⟩:=Nat.exists_eq_add_of_le u
 intro z
 let T' : Dome (tent Y H) := spreadTo Y H G s (s+d') f; let v':T'∈ insideAt Λ l K false (Cb d) (s+d') := inside_spread Y H G v u
 let s':=s+d'; let X:= aureole K j 0 y * T' * y; have k:aureole K j 0 y∈ insideAt Λ l K false U₂ s':= mirror_inside Y H j y _ w
 obtain ⟨b',D₂⟩:= topEarn j d m h t -- p unused? Λ implicit
 have hz: (aureole K j 0 y*T')∈ insideAt Λ l K false ((Cb d)∪ U₂) (s+d') := (insideAt Λ l K false ((Cb d)∪U₂) (s+d')).mul_mem (insideAt_mono Set.subset_union_right k) (insideAt_mono Set.subset_union_left v') -- carrier wrong notation
 have e':(Mirror j) ((Rt m) x.val)* Px s f *(Rt m) x.val= ticket Y H G s' X:=by
    unfold X; rw [e,flipMark_ticket,ticket_separated Y H G hz w D₂,ticket_separated Y H G k v' b'.symm]; rw [← show Px s' T'= Px s f from ticket_spread Y H G u f]
 have Z': ((⟨_,z⟩ : Domain Y H G false univ))=⟨ticket Y H G s' X,ticket_loose ..⟩:=Subtype.ext e'; rw [Z',course_ticket_val]
 -- y positive => y.r qualification
 have q: y.val ∈ purpose K (meshface (Λ:=Λ) 0 s') j false:= (positive_today Y H j s' y).1 (insideAt_mono (show U₁⊆UP 0 from fun x h=>(show (0:ℝ) ≤ (m:ℝ) from (show 0<(m:ℝ) from p).le).trans (show (m:ℝ) ≤ x j from h)) w)
 obtain ⟨K',hq,ht⟩:= (((purpose_ok ..).1 q).1 : ∃ S, InTest K true S false y.val ∧ Tower.region j _ _ S)
 rw [area0] at ht; exact human Y H V G j Hx hy kz d' y hq ht
omit p
lemma purchases : 0 ≤ album Y H V G C j ⟨ticket Y H G s f,ticket_loose ..⟩ :=by
 obtain ⟨d,d₀,h⟩:= coincidence Y H j f s
 obtain ⟨m,g⟩:= anywhere Λ d; let F: µ:= ⟨ticket Y H G s f,ticket_loose ..⟩
 have hm:(0:Gt) < m :=show (0:ℝ)<(m:ℝ) from lt_of_le_of_lt d₀ g
 have h₁ : ∀ x:RSpace,x ∈ Cb d→ x∈ strip j (-(m:ℝ)) (m:ℝ):=by
    rintro u ⟨p,q⟩; constructor<;>linarith
 obtain ⟨B,B0,BP,BY⟩:= squareCandle Y H V G C j m hm F (ticket_mem Y H G (insideAt_mono (show Cb d ⊆ strip j (-(m:ℝ)) (m:ℝ) from fun u g=>h₁ u g) h))
 change 0 ≤ Pc F; rw [←B0]; apply reduce_nonneg
 change 0≤ (B.val : H₀→L[ℂ] H₀)
 apply (ContinuousLinearMap.nonneg_iff_isPositive _).2; apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp -- tune orientation
 apply (LinearMap.isPositive_iff_complex _).2
 intro x
 have hx:0≤ inner ℂ x (B.val x):=by
   apply closure_minimal (t:={x:H₀|0≤ inner ℂ x (B.val x)}) _ (isClosed_le continuous_const (continuous_id.inner B.val.continuous)) (LightBudget.advance_dense Y H V G j (C j) 0 x)
   rintro x ⟨f₁,g',x',t,rfl⟩; let y₁:Nₐ:= ⟨f₁,t⟩
   change 0 ≤ inner ℂ (pay y₁) (B.val (pay y₁)); rw [← BY y₁ (BP y₁)]; exact attends Y H V G j m hm Hx hy kz h g d₀ y₁ _
 have ht:0≤ inner ℂ (B.val x) x:=by rw [← inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using hx
 exact ⟨Complex.ext rfl ht.2, ht.1⟩
lemma station_happy : 0 ≤ oneAt Y H V G j (C j) χ s f:=by
 change 0≤ χ ((located Y H V s G.history G.clipped j false (C j)) (asLoose K f))
 rw [←atStamp Y H V G C j s f (ticket_loose ..)]; exact _root_.map_nonneg _ (purchases Y H V G C j Hx hy kz)
end height
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.attends
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.station_happy
