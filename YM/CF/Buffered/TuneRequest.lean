import YM.CF.Buffered.Detuned
/-! Normalize after Ledger payments. Roof/flags use the same annulus. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Alloy
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember Phase Mint Mint.Roe Fock Dial Gall Advance Pastry MeasureTheory Push.SectorMeasure
open Ballad
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H L' d':ℝ}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
variable {C Q h:ℝ}
structure Crop (j:ℕ)(H D x:ℝ)(w:ℕ): Prop where
 width : 0<x
 costs : ∀ {N:Side},w ≤ N.val →∀ S:Pane N, flags x S=∅ →∀ (M:Jill.Male)(i:LeanV (Single N)),Gall.Pays H (drawT (spar j M S) i) D
lemma crop_f (p:1≤j)(e:0 ≤ H):∃ a d:ℝ,∃ w:ℕ,Crop j H a d w:=by
 obtain ⟨a,b,h,w,k,q⟩:= Graph.burley _ p; obtain ⟨c,h₁,v⟩:= taxon w; exact ⟨(a+1)*H,c,k, h₁, fun {N} l U f M i=> Graph.crag _ _ (q _ l _ (v _ _ f) M) e⟩

variable (D:Pic.Span hP K b' v C' l s' k)
variable {m:Side} (I:GramM (mid m B)) (S:Loom (mid m B))
variable (F:SkinT I S e)(p:k ≤ (mid m B).val)(g:Graph.Ledger h a b r C I)
include D F p g
variable {vA:ℝ}
lemma pace (k':0≤H)(e:0≤vA)(t:0≤r)(g₁:0≤h)(b:0≤C)(W:Mark (mid m B))(v:Orbit (mid m B))(q:v∈Lace I)(z:HelpP v.1 vA r)(w: Gall.Yep H (acts (star (W (drawn S v))) (mateK _)) (changeM (m:=m) P v.1 I.J.M) d') (u:0 ≤ d')(U:pittance (mid m B) vA C≤1)(y:∀ i:LeanV (Single (mid m B)),Gall.Pays H (drawT (spar j I.J.M v.1) i) h)(W':baton (mid m B) a vA C H≤1) :
 ‖letterRead (W (drawn S v)) (recX P I S v)‖ ≤ Graph.dim I v * (2*d') := by
 let N:= mid m B; have hr:S v=v.1:= F.high v q; obtain ⟨i,f,hP'⟩:= F.wave; have hx:= (P.broadness _ (D.plan m p).1 I.J.M).projection (S v) (hP'.paid v)
 let C':=mile j I S v; let Y:=changeM (m:=m) P (S v) I.J.M; let Y':= beam I P S v; have he: Y'= acts (C'-1) Y + Y:=by unfold Y'; rw [act_sub,act_one,sub_add_cancel]; rfl
 let A:= W (drawn S v); have hm: ‖inner ℂ (mateK N) (acts A Y')‖≤2*d':=by
    have hu:= ridge g v (show HelpP (S v) vA r from Eq.mpr (congrArg (fun f=> HelpP f vA r) hr) z) e t g₁ k' b hx q U (fun i=>by rw [hr]; exact y i); have hl:Gall.Yep H (acts (star A) (mateK _)) Y d':=by unfold A Y; rw [hr]; exact w
    rw [←act_inner,he]; refine ((hu.2 _ _ _ u hl|>.join hl).low).trans ?_; nlinarith [mul_le_mul_of_nonneg_right W' u]
 rw [Graph.porch,Graph.dim,Set.indicator_of_mem q]; simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul, norm_smul]; change ‖(past I v.1:ℂ)‖*_≤_; rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
lemma mask (V':Orbit (mid m B))(h':V'∉ Lace I)(t:0≤r)(h₁:1≤h)(u:0≤C)(W:I.path.Bounds I.funds μ L' τ)(v:0≤I.beta)(a':0≤w)(p':w≤I.funds.linear) (X:Mark (mid m B))(Y:Fields (mid m B)): ‖letterRead (X Y) (recX P I S V')‖ ≤ ‖X Y‖*Real.exp (flagT (mid m B) a b C - kinetic (More (mid m B)) I.p L' τ I.beta w) := by
 let N:= mid m B; obtain ⟨l,k,F'⟩:=F.wave; let G:= mile j I S V'; let vM:=changeM (m:=m) P (S V') I.J.M; let C':=flagT N a b C; let q:= kinetic (More (mid m B)) I.p L' τ I.beta w
 have hx: IsStarProjection (spar j I.J.M (S V')):= (P.broadness _ (D.plan m p).1 I.J.M).projection (S V') (F'.paid V'); have ht: ‖vM‖=1:=(sea_g (D.plan m p).1 _ (F'.paid V') I.J.M).2 -- supply arguments
 have hw: ‖G‖≤Real.exp C':=Graph.stout g _ t h₁ u hx
 apply (mark_bound (X Y) (recX _ _ _ _)).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [porch,norm_smul]; have hg:0 ≤ past I V'.1:=(Real.exp_pos _).le
 rw [Real.norm_of_nonneg hg]; refine (mul_le_mul (show past I V'.1 ≤ Real.exp (-q) from Real.exp_le_exp.mpr (neg_le_neg (fullH W I.p V'.1 a' p' v h'))) (show ‖acts G vM‖≤Real.exp C' from (spentS ..).trans (by rw [ht, mul_one]; exact hw)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_; rw [←Real.exp_add]; apply congrArg; unfold C' q N; ring

variable {F I S}
omit g in
lemma marked_up (X:Mark (mid m B))(d z C:ℝ)(W':Envelope X)(p':Ward I)
 (u:0≤d)(g:0 ≤ z) (W:∀ x:Orbit (mid m B),x∈ Lace I → ‖letterRead (X (drawn S x)) (recX P I S x)‖≤ Graph.dim I x * (C*Kea.angel m P I.J.M)*d)(q:∀ x:Orbit (mid m B),x∉Lace I→ ‖letterRead (X (drawn S x)) (recX P I S x)‖≤ z) : ‖num0 P I S X‖ ≤ drip I P*C*d+z:=by
 obtain ⟨s,t,F⟩:= F.wave; have he:= Girt.sailW I p' hP D.stmt D.eP D.p t S F (D.plan m p).1; let a:= angle I; let A:=Kea.angel m P I.J.M; have ht:Integrable (recX P I S) (city _):=(show Integrable (denZ I P S) (city _) from Integrable.of_bound he.meas.aestronglyMeasurable _ (Eventually.of_forall he.cost.choose_spec)).smul (Complex.exp (-I.v))
 unfold num0 markedRead; apply (norm_integral_le_integral_norm ..).trans; refine le_trans (integral_mono (mark_integrable F.bill W' ht|>.norm) ((((worth p').integrable _).mul_const (C*A)|>.mul_const d).add (integrable_const z)) (fun x=>?_)) ?_
 · by_cases h:x∈ Lace I; exact (W x h).trans (le_add_of_nonneg_right g); have hp:= q _ h; change _ ≤ Graph.dim I x *_*d+ z; rw [dim,Set.indicator_of_notMem h,zero_mul,zero_mul,zero_add]; exact hp
 change (∫ x, Graph.dim I x*_ * d+z∂city _ ) ≤ _; rw [integral_add (((worth p').integrable _).mul_const (C*A)|>.mul_const d) (integrable_const z),integral_mul_const,integral_mul_const, integral_const, probReal_univ,one_smul]; apply le_of_eq; unfold drip Graph.angle A; ring -- tune city
end YM.CF.Buffered.Alloy
