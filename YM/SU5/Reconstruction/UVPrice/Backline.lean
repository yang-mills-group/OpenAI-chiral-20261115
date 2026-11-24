import YM.SU5.Reconstruction.UVPrice.HighEnergy
/-!
# momentum bounded on low energy grants. True in ALL finite slices
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
local notation "D₁" => {i:Axis//i≠a}

def Tense (ε δ:ℝ):Prop:= ∀ (i:{i : Axis// i≠a})(t:ℝ≥0), 0<t→ (t:ℝ)<ε→ ∀ x∈ Shelf S,tension ((t:ℝ) • cross a i.val i.property) t x≤δ
abbrev Wheater:= ∀ δ:ℝ,0<δ→ ∃ ε>0,Tense S ε δ
def Beneath (C:ℝ): Set E4:= {x∈Shelf S|x a≤ C}
lemma beneath_closed (u:ℝ) : IsClosed (Beneath S u):=isClosed_closure.inter (isClosed_le (show Continuous fun x:E4=> x a from by fun_prop) continuous_const)
section
-- elementary grants pouring-only low energy slices
variable {ε:ℝ} (hp:0<ε)(hx:Tense S ε 1)
include hp hx
theorem amount_bound {C:ℝ}(v:0 < C) (i:D₁) (x:E4)(hy:x∈Beneath S C):
    |x i.val| ≤ max (π/ε) (8*π*C):=by
 let P:=|x i.val|; have h0:= hy.1; let y:= cross a i.val i.property
 by_contra z; push Not at z
 -- push Not decomposes max?
 have z':max (π/ε) (8*π*C)<P:= z
 have hv: π/ε<P:= lt_of_le_of_lt (le_max_left ..) z'; have ht:0<P:= (by exact lt_trans (by positivity) hv); let t:=π/P
 have he:0<t:= by unfold t; positivity
 let u:ℝ≥0:= ⟨t,he.le⟩; have hr: t< ε:= (div_lt_iff₀ ht).mpr (by linarith [(div_lt_iff₀ hp).mp hv])
 have h:= hx i u (show 0<u from he) hr x h0; rw [tension_true] at h
 have hb: cos (inner ℝ (SEP a x) ((u:ℝ) • cross a i.val i.property))= -1 := by
    rw [real_inner_smul_right (SEP a x) (cross a i.val i.property) (u:ℝ),← cone_mean]; change cos (t * inner ℝ x (basis i.val)) = _; rw [real_inner_comm,basis_inner, ← cos_abs]; rw [abs_mul,abs_of_pos he, show t*|x i.val|=π from div_mul_cancel₀ _ ht.ne']; exact cos_pi
 rw [hb] at h
 let d:= Real.exp (-(x a)*t)
 have h₁ : d≤1:=exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [shelf_ePays S _ h0]) he.le)
 have h₂: 8*t*x a ≤1:= by
    have ht: t*(8*C) ≤1:= by
       unfold t; rw [div_mul_eq_mul_div,div_le_iff₀ ht]; have h:= (le_max_right (π/ε) (8*π*C)).trans z'.le; linarith
    linarith [mul_le_mul_of_nonneg_left (show x a≤ C from hy.2) he.le]
 change 2*(1- -1)*d^2-(1-d)^2 ≤1 at h
 nlinarith [show -(x a)*t+1 ≤ d from Real.add_one_le_exp _,sq_nonneg (1-d)]
-- true compactness via E4 basis
lemma compact_shelf (C:ℝ) : IsCompact (Beneath S C):= by
 let u:= max C 1; have hu:0<u:=lt_of_lt_of_le zero_lt_one (le_max_right ..)
 let B:=max u (max (π/ε) (8*π*u)); have h:∀ x∈Beneath S C, ∀ i:Axis, x i ∈ Icc (-B) B:= by
   intro x hz i; apply Iff.mp (_ : |x i|≤ B ↔ x i∈ _)
   swap; exact abs_le
   by_cases p:i=a
   · subst i; rw [abs_of_nonneg (shelf_ePays S _ hz.1)]; exact hz.2.trans ((le_max_left ..).trans (le_max_left ..))
   exact le_trans (amount_bound S hp hx hu ⟨i,p⟩ x ⟨hz.1,hz.2.trans (le_max_left ..)⟩) (le_max_right ..)
 have he := isCompact_univ_pi (fun _ : Axis=> isCompact_Icc (a:= -B) (b:=B)); change IsCompact (Set.univ.pi _) at he
 exact (he.image (PiLp.continuous_toLp 2 _)).of_isClosed_subset (beneath_closed S C) (fun i v=> ⟨i.ofLp,(fun y _=> h i v y), WithLp.toLp_ofLp ..⟩)
end
abbrev Backs : Prop:= ∀ C,IsCompact (Beneath S C)
lemma wheatBacks (h:Wheater S) : Backs S:= by obtain ⟨ε,h,t⟩:= h 1 zero_lt_one; exact compact_shelf S h t
lemma cost_back {Γ : AddSubgroup ℝ} (d:Dense (Γ:Set ℝ)) (X : Sunbelt a Γ H) (g : ∀ i,∀ (z : Γ) (t:ℝ≥0), ((X.track.crew i).play z).comp (S.E t)=(S.E t).comp ((X.track.crew i).play z)) (h:SmallCost S X): Wheater (glass X d S g):=by
 intro δ t; obtain ⟨p,h,v⟩:= h δ t; exact ⟨p,h, soft_shelf S d X g v⟩
lemma bdd_beneath (C:ℝ)(p:IsCompact (Beneath S C))(b:Axis): ∃ z:ℝ,0 ≤ z∧ ∀ x∈Beneath S C,|x b|≤ z:=by
 obtain ⟨v,w⟩:= IsCompact.bddAbove (p.image (show Continuous fun x:E4=>|x b| by fun_prop)); exact ⟨max v 0,le_max_right ..,fun x h=> le_trans (w (mem_image_of_mem _ h)) (le_max_left ..)⟩
end YM.Roy
