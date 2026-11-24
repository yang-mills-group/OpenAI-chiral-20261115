import YM.SU5.Relativistic.Armor
/-! # True sensor shaped on public Spin symbol in the actual physical mesh. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Lat Fock BZ
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π

variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ}
section bound
lemma gesturing (M: Momentum): Continuous (fun x:Momentum=>zen x):=by unfold zen; fun_prop
lemma scoreGraph(j:ℕ)(M:Side)(h:Odd M.val)(u:Bin)(v:Jill.Bound π u)(h':u≠0) : let T:=tmap u; let Z:=zen (mixL j M T);
    acts (bar j M T) (acts (1-Z) (basisKet 0))=acts (1-Z) (basisKet 0):=by
 dsimp only
 let T:=tmap u; let A:=mixL j M T; let Z:=zen A;
 have p:T∈ realCube zone:= base_subset_realCube zone_pos (b_base v)
 have hz: T≠0:=by intro y; apply h'; funext i; have he:(u i:ℂ)=0:=congrFun y i; exact_mod_cast he -- zero Pi
 let Y:=bar j M T; have hc:= graphs_ne (phys_mix j M h _ p.1); rw [←act_mul, (bar_full j M p hz hc).1]
 let t:=prodM A A; let L:= shell j M T; have he : L=(1+t)⁻¹:= shell_inv j M p hz
 have hp:Aop= cutM plusHalf:=Adef.trans Lat.raising.symm
 change acts ((L • ((1-Z)*Aop*(1+Z)))*(1-Z)) _=_
 rw [Algebra.smul_mul_assoc, mul_assoc ((1-Z)*Aop), show (1+Z)*(1-Z)=(1+t) • (1:Op SpinIdx) from ?_]; swap; · rw [add_mul,one_mul,mul_sub,mul_one,show Z*Z= -t • 1 from zenSq A]; module
 rw [Algebra.mul_smul_comm, mul_one,he, inv_smul_smul₀ hc,act_mul,hp,cut_basis, if_pos (by decide)]
end bound

namespace UpStart
variable (P:UpStart d s c r (2*a))
local notation "Ω"=>target s c
local notation "Z"=>turned s c
local notation "U"=>launch d r
local notation "V"=> (launch d r) ×ˢ Set.Icc (-π) π
abbrev mana (M:Jill.Male)(x:Behind)(t:ℝ) := bar 4 M.val (tmap (tack x t))
private abbrev planned (Q: Momentum) (z:ℂ):= z • acts (1-zen Q) (basisKet (0:SpinIdx))
lemma spiritShrink (x:Behind)(y:ℝ)(p:x∈ backPane)(q:y∈Φ) (M:Jill.Male) : ‖acts (mana M x y)‖≤1:=by
 unfold acts
 rw [Matrix.l2_opNorm_toEuclideanCLM]; apply IsStarProjection.norm_le; have hv:Jill.Bound π (tack x y):=by
    apply (pi_norm_le_iff_of_nonneg pi_pos.le).2; intro a; induction a using Fin.lastCases with
    | last=> exact (tack_right ..).symm ▸ (abs_le.mpr q)
    | cast i => rw [tack_left]; exact abs_le.mpr (p i (Set.mem_univ i))
 obtain ⟨h,v⟩:= firm_bar 4 M.val M.property (base_subset_realCube zone_pos (b_base hv)); exact ⟨h,v⟩
include P
private lemma present_c:ContinuousOn (uncurry Ω) (Set.univ ×ˢ Set.Icc (-π) π):=by
 have he: Function.uncurry Ω=(fun p:Behind×ℝ=> ∑ i:SpinIdx,Z i p.1 p.2 • basisKet i):=funext (fun i=> (basis_expand (Ω i.1 i.2)).symm)
 rw [he]; apply continuousOn_finsetSum; intro i _; exact (P.turned_c i).smul continuousOn_const
private lemma trackMoves {M:ℕ → Jill.Male}{f:ℕ → Behind×ℝ}{x:Behind × ℝ}(w:x∈ U ×ˢ Φ)(p:Tendsto (fun i=>(M i).val) atTop atTop)(e:Tendsto f atTop (𝓝 x))(g:∀ i,f i∈ U ×ˢ Φ) :
    Tendsto (fun i=>planned (mixL 4 (M i).val (tmap (tack (f i).1 (f i).2))) (Function.uncurry (pledge s c) (f i))-Function.uncurry (Ω) (f i)) atTop (𝓝 0):=by
 let u:=Function.uncurry Ω x; have hy : Tendsto f atTop (𝓝[Set.univ ×ˢ Φ] x):= tendsto_nhdsWithin_iff.mpr ⟨e,Eventually.of_forall (fun i=> ⟨Set.mem_univ _,(g i).2⟩)⟩
 have hh:Tendsto (Function.uncurry Ω ∘ f) atTop (𝓝 u):= (P.present_c x ⟨Set.mem_univ _,w.2⟩).tendsto.comp hy
 let z:=fun i=>tmap (tack (f i).1 (f i).2); let Y(i:ℕ):=mixL 4 (M i).val (z i); let Z0:=heatLine x.1 x.2
 have he : x.1∈ sunshine:=launch_sun P.wage P.tail w.1
 have hr (i:ℕ) : (f i).1∈ sunshine:=launch_sun P.wage P.tail (g i).1
 have hx:Tendsto z atTop (𝓝 (tmap (tack x.1 x.2))):= ((show Continuous tmap by unfold tmap; fun_prop).tendsto (tack x.1 x.2)).comp ((tack_c.tendsto x).comp e)
 have hn:Tendsto Y atTop (𝓝 Z0):= tendsto_pi_nhds.mpr (fun j=> Shore.gulch p hx (Eventually.of_forall fun i=> (M i).property) (spectrum_b x.1 he x.2 w.2) (tac_nz he) j (Eventually.of_forall fun i=> b_base (spectrum_b _ (hr i) _ (g i).2)))
 have hp:Tendsto (fun i=>planned (Y i) (Function.uncurry (pledge s c) (f i))) atTop (𝓝 u):=( (P.pledge_c.tendsto x).comp e).smul ((Continuous.tendsto (f:=fun v:Momentum=>acts (1-zen v) (basisKet 0)) (by unfold zen; fun_prop) Z0).comp hn)
 have hT:= hp.sub hh; rw [sub_self] at hT; exact hT
private lemma united (ε:ℝ)(p:0<ε): ∃ N:ℕ,∀ M:Jill.Male,N ≤ M.val.val → ∀ k∈launch d r,∀ t∈Φ,
    ‖planned (mixL 4 M.val (tmap (tack k t))) (pledge s c k t) - Ω k t‖ ≤ ε:=by
 by_contra! t
 choose F g k w T e β using t
 let U':= launch d r; let f(x:ℕ): Behind×ℝ:=(k x,T x)
 obtain ⟨x,pX,l,H,h⟩:=((launch_compact d r).prod (show IsCompact Φ from isCompact_Icc)).tendsto_subseq (fun i=> (show f i ∈ _ from ⟨w i,e i⟩))
 have hu:Tendsto (fun i=>(F (l i)).val) atTop atTop:= tendsto_atTop.mpr (fun i=>(H.tendsto_atTop.eventually_ge_atTop i.val).mono (fun x h=> show i.val≤(F (l x)).val.val from h.trans (g _)))
 let Z₀(i:ℕ):= planned (mixL 4 (F i).val (tmap (tack (k i) (T i)))) (pledge s c (k i) (T i))- Ω (k i) (T i)
 have hv:Tendsto (Z₀ ∘ l) atTop (𝓝 0):= trackMoves (M:= F ∘ l) (f:=f ∘ l) P pX hu h (fun i=> ⟨w _,e _⟩)
 have hx:= ge_of_tendsto hv.norm (Eventually.of_forall fun i=> (β (l i)).le)
 rw [norm_zero] at hx; exact p.not_ge hx
-- projected for approximate Fourier polynomial uniform across all true AP momenta.
lemma critical (ε:ℝ)(p:0<ε) : ∃ N:ℕ,∀ M:Jill.Male,N≤M.val.val → ∀ x∈backPane,∀ y∈Φ, ‖acts (mana M x y) (Ω x y)-Ω x y‖ ≤ ε:=by
 obtain ⟨n,w⟩:= P.united _ (half_pos p)
 refine ⟨n,fun M v x i y k=>?_⟩
 set Q:=mana M x y; set u:= Ω x y
 by_cases j:x∈U; swap
 · change ‖acts Q u-u‖≤ _; rw [show u=0 from P.elsewhere x (fun e=> j (interior_subset e)) y]; simpa using p.le -- tune
 let B:= mixL 4 M.val (tmap (tack x y)); let V':=planned B (pledge s c x y); have he : ‖V'-u‖≤ ε/2:=w M v x j y k
 have hu: x∈ sunshine:= launch_sun P.wage P.tail j
 have hh: acts Q V'=V':=by unfold V' planned; rw [map_smul,scoreGraph _ _ M.property _ (spectrum_b _ hu _ k) (tac_nz hu)] -- tune
 apply (norm_sub_le_norm_sub_add_norm_sub _ V' u).trans; rw [←hh]; -- all, beware
 rw [← map_sub,hh]; refine (add_le_add (((acts Q).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (spiritShrink _ _ i k M)).trans (by rwa [norm_sub_rev]))) he).trans_eq (add_halves _)
end UpStart
end YM.CF.Crest.Sleet
