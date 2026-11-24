import YM.SU5.Reconstruction.PolarArchives.Reverb
/- Amplify the CP18 kernel proofs (adapt our Dr. ..) from just the fixed-FAR SINGLET stencils. Economical area. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open PolarArchives
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
variable (P:Ramp) {J: Calibration}
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
variable (gap:ℝ≥0)
local notation "Π" => Domain Y H G true (PolarArchives.Acres P gap)
local notation "S" => Domain Y H G true (PolarArchives.SkyAcres P gap)
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
variable (W:Chat_remote Y H V G P C a χ gap)
local notation "M₀" => timeMesh Λ
local notation "Wr" => stretchD P
open _root_.YM.ConePrice.Storm.StepVoucher

private lemma stepSize_remote (Λ:Preparation)(s:ℕ): 0<(notch (timeMesh Λ) s 1).val:=by change 0<bell _ s 1; unfold bell; rw [Int.cast_one,one_mul]; exact mill_pos ..
private lemma supported_ticks_remote {X:Type*}(m:Finset X)(f:X→Shard Gt):∃ (ρ:marks (timeMesh Λ)),0<(ρ:ℝ)∧ ∃ t:X→ℕ, (∀ i∈m, 0<t i ∧ (t i)•ρ=(f i).val) :=by
 have p(i:X): ∀ᶠ s:ℕ in atTop, ∃ t:ℕ,0<t ∧ t • notch (timeMesh Λ) s 1=(f i).val:= by
    let u:Gt:= (f i).val; obtain ⟨v,w,p⟩:= notch_exists _ u
    filter_upwards [eventually_ge_atTop v] with s h; let z:=castor (timeMesh Λ) v s w; have p':notch (timeMesh Λ) s z=u:= (notch_up (timeMesh Λ) v s h w).trans p
    have hp : z>0:=not_le.mp (fun e=> not_le.mpr (thermal_pos (f i)) (by
        change u.val ≤ (0:ℝ); rw [← p']; change bell _ s z≤_; have h':= (MeshClock.bell_le (timeMesh Λ) s z 0).2 e; simpa only [MeshClock.bell,Int.cast_zero,zero_mul] using h'))
    refine ⟨z.toNat,by omega,(Subtype.ext (by change ((z.toNat • _ : Gt):ℝ)=u.val; rw [AddSubgroup.coe_nsmul,←p']; change z.toNat • (bell _ s 1)= bell _ s _; rw [nsmul_eq_mul]; unfold MeshClock.bell; rw [Int.cast_one,one_mul, show (z.toNat:ℝ)=(z:ℝ) by rw [←Int.cast_natCast,Int.toNat_of_nonneg hp.le]]))⟩
 obtain ⟨s,v⟩:=(m.eventually_all.mpr (fun i _=>p i)).exists
 choose k h e using v -- probably dependent proof arg. want t all i
 exact ⟨_,stepSize_remote Λ s,fun i=> if x:i∈m then k i x else 1,fun i y=> by simp only [dif_pos y]; exact ⟨h i y,e i y⟩⟩
lemma knows_price_remote (p p':Domain Y H G true (PolarArchives.Acres P gap)): Voucher thermal (fun s:Shard Gt=> inner ℂ (W.plant p) (W.plant (treks_remote Y H V G P gap s.val (thermal_pos s).le p'))) (‖W.plant p‖*‖W.plant p'‖):= by
 intro c l C' hx; obtain ⟨ρ,φ,v,w⟩:= supported_ticks_remote l (fun x=>x)
 let Z:=radial_remote Y H V G P C a χ gap W ρ φ.le
 have h(x)(y:x∈l): (Z^(v x)) (W.plant p')=W.plant (treks_remote Y H V G P gap x.val (thermal_pos x).le p'):=by
    unfold Z; rw [ticks_remote Y H V G P C a χ gap W, (service_remote Y H V G P C a χ gap W _ (cast_Δ ρ (v x) φ.le)).2]; apply congrArg W.plant; apply Subtype.ext; change au (billT P _) _=au (billT P _) _; rw [(w x y).2]
 rw [show (∑ i∈l,c i*(inner ℂ (W.plant p) (W.plant (treks_remote Y H V G P gap i.val (thermal_pos i).le p')):ℂ)) = ∑ i∈l,c i*inner ℂ (W.plant p) ((Z^(v i)) (W.plant p')) from Finset.sum_congr rfl (fun i he=>by rw [h i he])]
 apply credit_pos Z (positive_speed_remote Y H V G P C a χ gap W ρ φ.le) (service_remote Y H V G P C a χ gap W ρ φ.le).1 c v l (ρ:ℝ) φ _ (fun i h=>(w i h).1) (W.plant p) (W.plant p'); intro x y
 specialize hx x y; convert hx using 2; apply Finset.sum_congr rfl; intro i hi; have e: thermal i=(v i:ℝ)* ρ.val:=by
    change i.val.val = _; rw [←(w i hi).2, AddSubgroup.coe_nsmul,nsmul_eq_mul]
 rw [e,show -(ρ:ℝ)*x * (v i:ℝ)= -((v i:ℝ)*ρ.val)*x by ring]

private lemma blank_path_remote (s:Gt):0≤ (hoursN P (Wr (-s) s)).val := by rw [hourMark,neg_add_cancel]; exact le_rfl
-- Need s tests, motion (time +s,space -s), so use at -s. Can define straight.
private lemma tangent_path_remote(s:Gt):0≤(hoursN P (Wr s (-s))).val:= by rw [hourMark,add_neg_cancel]; exact le_rfl
lemma tangent_cost_remote(p:Domain Y H G true (PolarArchives.Acres P gap))(s:Gt): let t:=sails_remote Y H V G P gap (stretchD P s (-s)) (tangent_path_remote P s); ‖W.plant (t p)‖=‖W.plant p‖:=by
 intro t; have h:=sail_cost_remote Y H V G P C a χ gap W p p s (-s) (tangent_path_remote P s) (tangent_path_remote P s) p (show p.val=move K (Wr (s+ -s) (s+ -s)) p.val from by rw [add_neg_cancel,mark_zero,move_by_zero]) (by rw [add_neg_cancel]; exact le_rfl)
 change inner ℂ (W.plant (t p)) (W.plant (t p))=inner ℂ (W.plant p) (W.plant p) at h; have ht:= congrArg (RCLike.re («K»:=ℂ)) h
 simp_rw [inner_self_eq_norm_sq] at ht; nlinarith [norm_nonneg (W.plant (t p)),norm_nonneg (W.plant p)] -- tune
set_option maxHeartbeats 1000000
include W in
lemma outgoBook_remote {x:Sky (tent Y H)}(h:x∈ Domain Y H G true (flank P.a 0)) : Desired Y H V G C a χ P.a P.b x:= by
 let k₀:=P.a; let A:=flipMark k₀ K x; let O: ℝ:= (0:ℝ)
 obtain ⟨D₀,g⟩:= dump_x_remote Y H V G P gap (f:=flipMark k₀ K x) (domain_mono Y H G (subset_univ _) (mirror_support Y H G P.a x h))
 obtain ⟨D₁,e⟩:=pump_x_remote Y H V G P gap (domain_mono Y H G (subset_univ _) h)
 obtain ⟨M,w⟩:= anywhere Λ (max (max D₀ D₁) 0)
 have z:0<M.val:=lt_of_le_of_lt (le_max_right ..) w
 let U:=Wr M 0
 have h₀:au (Wr (-M) 0) A∈Domain Y H G true (PolarArchives.SkyAcres P gap):=g _ (by rw[hourMark,add_zero,AddSubgroup.coe_neg]; linarith [le_max_left D₀ D₁,le_max_left (max D₀ D₁) 0])
 let p:Π:= ⟨_,glides_S_remote Y H V G P gap h₀⟩; have hp:gust P K p.val = move K (Wr (-M) 0) (flipMark P.a K x):= gust_square P _
 have h₁:au U x∈ Domain Y H G true (PolarArchives.Acres P gap):= e _ (by unfold U; rw [hourMark,add_zero]; linarith [le_max_right D₀ D₁,le_max_left (max D₀ D₁) 0])
 let p':Π:=⟨_,h₁⟩; refine ⟨M+M,‖W.plant p‖*‖W.plant p'‖,add_nonneg z.le z.le,fun s=>?_⟩
 let B:= sails_remote Y H V G P gap (Wr s.val (-s.val)) (tangent_path_remote P s.val) p'
 have K':= knows_price_remote Y H V G P C a χ gap W p B
 rw [show ‖W.plant B‖=‖W.plant p'‖ from tangent_cost_remote Y H V G P C a χ gap W p' s.val] at K'; apply Voucher.rename thermal (‖W.plant p‖*‖W.plant p'‖) _ K'
 funext t
 -- direction: inner -> arcing (?), Voucher.rename p:F=G changes F to goal G
 have ht: Π= Π:=rfl -- notation volatile
 let Z: Π := treks_remote Y H V G P gap t.val (thermal_pos t).le B
 have Kz:Z.val=au (Wr t.val t.val) (au (Wr s.val (-s.val)) (au (Wr M 0) x)):=rfl
 change inner ℂ (W.plant p) (W.plant Z)= _; rw [guide_remote Y H V G P C a χ gap W,← whiff_move Y H V G C a χ (on_Cover_remote Y H V G P gap p.property Z.property) U, Kz, hp]
 unfold U; rw [move_prod,move_sum,move_sum,move_sum,move_sum]
 simp only [stretch_add, add_neg_cancel, add_zero, zero_add, mark_zero,move_by_zero]
 change Ω (_* move K (Wr _ _) _)= Ω (flipMark P.a K x * move K (Wr _ _) x)
 -- arithmetic.
 rw [show M+t.val+s.val+M=M+M+t.val+s.val by abel, sub_eq_add_neg t.val]

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
