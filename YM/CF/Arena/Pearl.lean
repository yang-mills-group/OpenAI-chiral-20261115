import YM.CF.Arena.Steep
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
section
variable {A W u:ℝ} {p k j r:ℕ}{R: SpaceX G c}{o:Site c}{M:Stores S}
abbrev denCS:= Push.Uniform.shade G
abbrev rankC(s x:ℝ):ℝ:= denCS * tideF s x
lemma rankV(s:ℝ): Tendsto (rankC s) atTop (𝓝 0):=by simpa only [mul_zero] using (tide_s s).const_mul denCS
lemma trod (j n:ℕ)(σ:ℝ)(hp:1≤n)(hu:0<σ)(hs:σ ≤ 1): ∃ s:ℝ,0<s∧∀ᶠ x in atTop, let u:=rankC s x; temp x ≤ u∧0<u∧u≤ σ ∧∀{c f:Side}(S:StepData c f)(V:Config G c)(M:Stores S)(o:Site c),o∉ M.dome ((j+2)*radiusB x) → M.flags= RG.flags (temp x) V→ (j+j+101)*radiusB x ≤ c.val → ∀ (R:SpaceX G c)(p k r:ℕ)(A W:ℝ), k<n→ p ≤ k→ r ≤ (j+1)*radiusB x →Urge R o p k r n σ A W → Allows n (R ∘ Vmove x V) 0 (composeCost n (vatP p k n A W u) (1/2)):=by
 obtain ⟨s,h,hX⟩:=hustle G j n hp; refine ⟨s,h,?_⟩; filter_upwards [hX,(rankV s).eventually (ge_mem_nhds hu)] with x hx hp; intro u; obtain ⟨he,hv,hr⟩:= hx; let t:=tideF s x; have ht:t ≤ u:=le_mul_of_one_le_left he.le (Push.Uniform.shade_one G); refine ⟨hv.trans ht,he.trans_le ht,hp,?_⟩; intro c f S V M o w ξ p' R i k r A W hi hg hx hW
 obtain ⟨P,g,hK,hL⟩:= hr S V M o w ξ p'; let X:= (tint G (Body 1 c)); let s:= denCS; let Z(y):= s⁻¹ • X (P y); have hS:0<s:= Push.Uniform.shade_pos G
 have h: Allows n Z 0 (1/2):= by refine (((hK.2.linear X.toContinuousLinearMap (ContinuousLinearMap.opNorm_le_bound X.toContinuousLinearMap hS.le fun i=> Push.Uniform.tint_le i)).smul s⁻¹).mono ?_); rw [abs_of_pos (inv_pos.mpr hS),← mul_assoc, inv_mul_cancel₀ hS.ne',one_mul]
 apply ((Urge.gem hW (x:=Z 0) (h.value.trans_lt (by norm_num)) (he.trans_le ht) (hp.trans hs) hp hi hg).comp (f:=Z) h).germ
 filter_upwards [hL] with i v; change R (represent (u • Z i))=R _; have he:represent (u • Z i)= facadeX G (t • P i):=by
    have hp:u • Z i= X (t • P i):=by unfold Z; change (s*t) • _= X (t • P i); rw [map_smul,mul_comm s,mul_smul,smul_inv_smul₀ hS.ne']
    rw [hp]; rfl
 rw [he,← hW.1.fixed (Vmove x V i) g]; exact hW.1.reads _ _ (fun i e=> (v i (e.trans hx)).symm)
end
section
variable (x:ℝ)(j r:ℕ)(Φ:Tab S→FileM c G)(A:Tab S→DirP c)
def cClip (a:Stores S)(P:Tab S) : DirP c:= fun i h=> if i ∉ a.dome (r*radiusB x) ∧ h ∉ a.dome (r*radiusB x) then A P i h else 0
def issued(a:Stores S)(P:Tab S)(i:Site c): SpaceX G c:= (if i∈ a.dome (j*radiusB x) then 0 else Φ P i)+ dict (cClip x r A a P) i
variable {Z:Tab S}{a:Stores S}{i y:Site c}{p m L:ℕ}{M D':ℝ}{k:ℕ}
lemma grantsU(a:Stores S)(P:Tab S): ∑ i,issued x j r Φ A a P i=∑ i: Site c, if i∈ a.dome (j*radiusB x) then 0 else Φ P i:=by unfold issued dict; simp_rw [sum_add_distrib,sum_sub_distrib]; rw [sum_comm (f:=fun i j=> cClip x r A a P j i),sub_self]; abel -- argument order f unknown
lemma climb_W(X:Support c)(h:i∉ halo (p+m) X)(hp:separation i y ≤ p): y ∉ halo m X:=fun u=>h (by obtain ⟨z,t,v⟩:=halo_spec.mp u; apply halo_spec.mpr ⟨z,t, (separation_triangle z y i).trans ?_⟩; rw [separation_comm y i]; omega)
lemma riseU(hv:j ≤ r)(p:i∉ a.dome (L+r*radiusB x))(h:Woven Φ A L k n σ C D): issued x j r Φ A a Z i= Φ Z i+dict (A Z) i:=by
 let V:=a.dome (r*radiusB x); have hp: i∉ V:=fun t=>p (farther (by omega) t); unfold issued; rw [if_neg (fun he=>hp (farther (Nat.mul_le_mul_right _ hv) he))]; apply congrArg (Φ Z i+·); unfold dict; refine congrArg₂ (·-·) (sum_congr rfl fun v _=> ?_) (sum_congr rfl fun v _=>?_)
 · unfold cClip; split; rfl; next he=> exact (not_not.mp (fun u=>he ⟨climb_W a.place p ((separation_comm ..).trans_le (h.dawn Z v i u)),hp⟩)).symm
 unfold cClip; split; rfl; next he=> exact (not_not.mp (fun u=>he ⟨hp,climb_W a.place p (h.dawn Z i v u)⟩)).symm
end
end YM.CF.Arena
