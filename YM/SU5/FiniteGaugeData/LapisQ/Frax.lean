import YM.SU5.FiniteGaugeData.LapisQ.Wing
/-! # Maxwell-projected density. Stable comparator on punctured ball. Exact discontinuity through 0.
No approx near 0 singular at SOME k assumption.
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Nosh
open Vulcan
variable {α:Type}[Fintype α] {β:Type}[Fintype β]
variable {n:Side} {G:Gauge} {ρ C Δ ε σ K:ℝ}
variable {u:Stage}{P:Bed}
abbrev Phase4:= Axis→ℂ
variable (p q:Phase4)(j:ℕ)
abbrev roomW (Y:Type)[Fintype Y] := Matrix Y Y ℂ
local notation "W"=> roomW (TypeFace 2)
local notation "x⁰"=> wedge 1 p
local notation "x₁"=> wedge 2 p
lemma recital (r:α→ℂ): dotProduct (star r) r=(sqLength r:ℂ):=by
 rw [sqLength_apply]; unfold dotProduct; simp only [ofReal_sum]; apply sum_congr rfl; intro i _; rw [← normSq_eq_norm_sq]; exact (Complex.normSq_eq_conj_mul_self).symm
lemma eq_bill : wedge 1 p * (wedge 1 p)ᴴ + (wedge 2 p)ᴴ * wedge 2 p= (sqLength p :ℂ) • 1:=by
 have he(j:ℕ):(wedge j p)ᴴ= ∑ i:Axis,star (p i) • (Exterior.left ℂ j i).transpose :=by
    unfold wedge; rw [Matrix.conjTranspose_sum]; apply sum_congr rfl; intro i _; rw [Matrix.conjTranspose_smul]; congr 1; ext a b; simp only [conjTranspose_apply,transpose_apply,Exterior.left,Matrix.of_apply]; split_ifs <;> simp [parity]
 refine Matrix.ext_iff_mulVec.mpr fun x=>?_ ; rw [Matrix.smul_mulVec,one_mulVec,add_mulVec,←mulVec_mulVec,←mulVec_mulVec,he,he]; simp_rw [Matrix.sum_mulVec, Matrix.mulVec_sum,Matrix.smul_mulVec,Matrix.mulVec_smul,← Finset.sum_add_distrib, ← smul_add,Work.F06.cartan,smul_smul]; rw [←recital,dotProduct,Finset.sum_smul]; rfl -- tune argument universe
abbrev camp (p:Phase4): roomW (TypeFace 2):= ((sqLength p:ℂ))⁻¹ • (wedge 1 p * (wedge 1 p)ᴴ)
local notation "y⁰"=> camp p
lemma rent_sq {q:α→ℂ}(h:q≠0): 0<sqLength q:=by
 rcases Function.ne_iff.mp h with ⟨x,h⟩; refine lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2) (component_sq_le ..) -- tune
lemma camp_p (h:p≠0){y:TypeFace 2→ℂ}(S:wedge 2 p *ᵥ y=0) : camp p*ᵥ y=y:=by
 have hz:=eq_bill p; let a:=sqLength p; have hv:(a:ℂ)≠0:= by apply Complex.ofReal_ne_zero.mpr; exact (rent_sq h).ne'
 have he: (x⁰ * (x⁰)ᴴ)= ((a:ℂ) • 1)-(x₁)ᴴ * x₁:=by rw [eq_sub_iff_add_eq]; exact hz
 unfold camp; rw [Matrix.smul_mulVec, he, sub_mulVec,←Matrix.mulVec_mulVec, S,mulVec_zero,sub_zero,Matrix.smul_mulVec,one_mulVec,smul_smul]; rw [show sqLength p=a from rfl, inv_mul_cancel₀ hv,one_smul]
lemma camp_z (y:TypeFace 2→ℂ) : wedge 2 p*ᵥ (camp p*ᵥ y)=0:=by
 rw [camp,mulVec_mulVec, Matrix.mul_smul,← Matrix.mul_assoc,d_d 1 p]; simp
lemma heroic : (camp p)ᴴ=camp p:=by unfold camp; rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose, Complex.star_def, map_inv₀, conj_ofReal]
lemma heroic_id(p0:p≠0): camp p*camp p=camp p:=Matrix.ext_iff_mulVec.mpr fun x=>by rw [←mulVec_mulVec]; exact camp_p p p0 (camp_z p x)
lemma closing (v:α→ℂ) (e:Matrix α α ℂ)(p:eᴴ=e)(t:e*e=e) : sqLength (e*ᵥ v) ≤ sqLength v:=by
 let w:=e*ᵥ v; let z:= v-w
 have hp:e*ᵥ w=w:=by unfold w; rw [mulVec_mulVec,t]
 have hh:dotProduct (star w) v=dotProduct (star w) w:=by
    conv_lhs => arg 1; rw [← hp]
    rw [star_mulVec,p,← dotProduct_mulVec] -- tune
 have ht: dotProduct (star v) w=dotProduct (star w) w:=by
    have he(x y:α→ℂ): dotProduct (star x) y=star (dotProduct (star y) x):=by rw [star_dotProduct]
    rw [he v w,hh,← he w w]
 have hg:= sqLength_nonneg z; unfold sqLength z at *; simp_rw [star_sub, sub_dotProduct,dotProduct_sub, hh,ht] at hg; simp only [Complex.sub_re] at hg; change (dotProduct (star w) w).re ≤ _; linarith
lemma passport (h:p≠0) (i j:TypeFace 2): ‖camp p i j‖ ≤ 1:=by
 let x:TypeFace 2→ℂ:= Pi.single j 1; let y:=camp p*ᵥ x
 have he: sqLength x=1:=by
    rw [sqLength_apply,sum_eq_single j]; · simp [x]
    · intro i t h; simp [x,h]
    simp
 rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one, one_pow, ← show y i= camp p i j from dotProduct_single_one _ _]; exact (component_sq_le y i).trans ((closing x _ (heroic p) (heroic_id p h)).trans_eq he)
@[fun_prop] private lemma rent_c : Continuous (fun p:Phase4=> sqLength p):= by simp_rw [sqLength_apply]; fun_prop
@[fun_prop] private lemma pedestal(i j) : Continuous (fun p:Axis→ℂ=> (wedge 1 p i j)):=by simp_rw [wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]; fun_prop
lemma cap_C (h:p≠0) (i j:TypeFace 2) : ContinuousAt (fun p:Phase4=> camp p i j) p:=by
 have h1:(sqLength p:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (rent_sq h).ne'
 have he:Continuous (fun p:Phase4=> (wedge 1 p*(wedge 1 p)ᴴ) i j):=by simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]; fun_prop
 change ContinuousAt (fun p=> ((sqLength p:ℂ))⁻¹ * _) p; refine ContinuousAt.mul ((Complex.continuous_ofReal.comp rent_c).continuousAt.inv₀ h1) he.continuousAt
-- cores. F01
abbrev leg0:PlaqAxes:=⟨(0,1),by decide⟩
abbrev f0: TypeFace 2:= plaquette leg0
lemma pedestal_only(r:ℕ)(v:Axis)(c:ℂ) : wedge r (Pi.single v c)= c • Exterior.left ℂ r v:=by
 unfold wedge; rw [sum_eq_single v]; · simp
 · intro i t h; simp [h]
 simp
lemma camp_high (c:ℂ)(p':c≠0) : camp (Pi.single 0 c) f0 f0=1:=by
 let v:TypeFace 2→ℂ:= Pi.single f0 1; let A':Phase4:= Pi.single (0:Axis) c; let y:=camp A'
 have hE : A'≠0:=by intro he; apply p'; apply Eq.trans _ (congrFun he 0); simp [A']
 suffices he:y*ᵥ v=v by
   change y f0 f0=_; rw [← show (y*ᵥ v) f0=y f0 f0 from dotProduct_single_one _ _,he,show v f0=1 from Pi.single_eq_same _ _] -- tune defeq
 refine camp_p A' hE ?_; unfold A'; rw [pedestal_only 2,Matrix.smul_mulVec]; suffices he:Exterior.left ℂ 2 0*ᵥ v=0 by rw [he,smul_zero]; -- tune binder
 funext i; rw [eliminate]; split_ifs with h; swap; · rfl
 have he:Exterior.remove 0 i h≠f0:=by intro z; have h0:= notMem_cut 0 i h; rw [z] at h0; exact h0 (mem_insert_self ..)
 rw [show v _=0 from (Pi.single_eq_of_ne he _), mul_zero]; rfl
lemma camp_nil (c:ℂ): camp (Pi.single 2 c) f0 f0=0:=by
 let v:Phase4:= Pi.single (2:Axis) c; unfold camp; rw [pedestal_only 1, Matrix.smul_apply, Matrix.mul_apply]; rw [sum_eq_zero,smul_zero]; intro i _; have he:(2:Axis)∉f0.val:=by decide
 rw [Matrix.smul_apply,Exterior.left,Matrix.of_apply, dif_neg he,smul_zero,zero_mul]
variable {A:Matrix (Body 2 n) (Body 2 n) ℝ}(t: Site n)
local notation "ẑ"=> Exterior.q (mon t)
local notation "F"=> facet A t
variable (g:Gate u P ρ C σ K n A)(S:Exterior.q (mon t)≠0)
include g S
lemma sure : camp (Exterior.q (mon t))* facet A t=facet A t:=by
 apply Matrix.ext_iff_mulVec.mpr; intro i; rw [← Matrix.mulVec_mulVec]; apply camp_p _ S; rw [Matrix.mulVec_mulVec, show wedge 2 (Exterior.q (mon t))*facet A t=0 from closed_pulse g t, Matrix.zero_mulVec] -- stuck grammar?
lemma earnings : facet A t - camp (Exterior.q (mon t))= facet A t*(1-P.metric.read (mon t))* camp (Exterior.q (mon t)):=by
 let w:=camp (Exterior.q (mon t)); let x:= P.metric.read (mon t)
 have hv:F*w=F:=by rw [←ballet t g.stands g.pays.1]; -- loops F use case
                      unfold w; rw [←heroic (p:=ẑ)]; -- tune spaces & congr
                      exact Eq.trans ((Matrix.conjTranspose_mul _ _).symm) (congrArg Matrix.conjTranspose (sure t g S)) -- tune we will fix
 have hr: F*x*w=w:=by unfold w camp; let z:= ẑ; rw [Matrix.mul_smul,← Matrix.mul_assoc]; rw [show F*x*wedge 1 z=wedge 1 z from (Matrix.mul_assoc ..).trans (wall_pulse g t)] -- tune
 change F-w=_; rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hv,hr]
lemma owed (Δ:ℝ)(d:0≤Δ) (S':‖Exterior.q (mon t)‖≤ Δ) (i j:TypeFace 2) : ‖facet A t i j-camp (Exterior.q (mon t)) i j‖ ≤ ((Fintype.card (TypeFace 2):ℝ)^2*(1/ρ))*(Δ/σ* K):=by
 let x:= P.metric.read (mon t); let L:= (Fintype.card (TypeFace 2):ℝ); let r:=1/ρ; let e:=Δ/σ*K
 have he(i j:TypeFace 2): ‖((1-x):W) i j‖≤ e:=by
    simp only [Matrix.sub_apply]; rw [norm_sub_rev,←g.F.starts]; exact row_entry_depart g.pen g.width (mon t) (real_frequency t) Δ d (fun i=> (norm_le_pi_norm _ i).trans S') i j -- tune args
 have hp:g.cost.le=g.cost.le:=rfl
 have hg(ℓ:TypeFace 2): ‖(facet A t*(1-x)) i ℓ‖ ≤ L*(r*e):=by
    rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> r*e) (fun j _=> ?_)).trans_eq (by simp [L])) -- tune
    rw [norm_mul]; exact mul_le_mul (frontier_entry g t i j) (he j ℓ) (norm_nonneg _) (one_div_nonneg.mpr g.cost.le)
 rw [← Matrix.sub_apply]; rw [earnings t g S]; rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> L*(r*e)) (fun j _=> ?_)).trans_eq (by simp [L,r,e]; ring)) -- variable capture j.Inner.
 rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (passport _ S _ _)).trans (hg _)
omit g S in
lemma promise (σ ρ K:ℝ)(p:0<ε): ∃ x:ℝ,0<x∧∀ {n:Side}{t:Site n}{P:Bed}{u:Stage}{C:ℝ}{A:Matrix (Body 2 n) (Body 2 n) ℝ},Gate u P ρ C σ K n A → Exterior.q (mon t)≠0→‖Exterior.q (mon t)‖≤x→∀ i j:TypeFace 2, ‖facet A t i j-camp (Exterior.q (mon t)) i j‖ ≤ ε:=by -- included g S remove
 let f(x:ℝ):= ((Fintype.card (TypeFace 2):ℝ)^2*(1/ρ))*(x/σ*K); have he:Tendsto f (𝓝 0) (𝓝 0):=by
    have hh:Continuous f:=by unfold f; fun_prop
    simpa [show f 0=0 from (by simp [f])] using hh.tendsto 0
 obtain ⟨x,h,v⟩:=(show ∃ x∈ Set.Ioi 0,f x≤ ε from (by
    obtain ⟨x,h,v⟩:= ((he.mono_left nhdsWithin_le_nhds).eventually (ge_mem_nhds p) |>.and (self_mem_nhdsWithin (a:=0) (s:=Set.Ioi (0:ℝ)))).exists
    exact ⟨x,v,h⟩)); exact ⟨x,h,fun g v' hp i j=> (owed _ g v' x (show 0<x from h).le hp i j).trans v⟩ -- binder implicit syntax
end Nosh
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Nosh.promise
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Nosh.camp_high
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Nosh.camp_nil
