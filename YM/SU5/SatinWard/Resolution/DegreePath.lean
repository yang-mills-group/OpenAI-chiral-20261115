import YM.SU5.SatinWard.Resolution.SectionMag
set_option autoImplicit false
set_option synthInstance.maxSize 32000
noncomputable section
namespace Zephyr.Chern.IndexMag
open YM YM.Lattice YM.CF YM.Laurent CF.LitCurrent CF.LitCurrent.Chamber MeasureTheory Silk Filter Topology
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology Kronecker
attribute [local instance] opCStarAlgebra
open Tulip
variable {ι:Type*} {j:ℕ} {L:Filter ι}{X:Cross j L} {p:Stack} (d:Division)
-- pay selected trace before extension.W.Figure exact & asympt frequency.Pf.H hey anchor.
abbrev site_root (N:Side)(x:Cover)(D:Division)(F:Op (Single N)):ℂ:= ∑ i:RegionD D,F (tag N x (codeD D i)) (tag N x (codeD D i))
noncomputable abbrev harvest {N:Side}(F:Oil N)(D:Division)(x:Cover)(v:StemA N) (u:ℝ):= site_root N x D (F (profile (petals v u)))
lemma section_bill {a r e:ℝ} {N:Side}{F:Oil N}(h: Solo a r F e)(he:0<e)(A:StemA N)(x:Cover) : Bloom (harvest F d x A) (∑ i:RegionD d,tuft F A x x (codeD d i) (codeD d i)):=by
 simp only [tuft,(tap_wad h he ..).bud_eq, flag_sq, one_smul]; exact Bloom.sum _ fun _ _=> (solo_bud h he).bloom
lemma branch_formula (h:X.Relax p)(x:Cover): Tendsto (fun u=> bud (harvest (X.oil u) d x (stream _)) 2) L (𝓝 (seam 0 (moneyD d (p 2))).trace):=by
 have e (i:IS): Tendsto (fun u=> tuft (X.oil u) (stream _) x x i i 2) L (𝓝 (seam 0 (p 2) i i)):=by
    have p:=h.pulse 0 (-x) i i 2; rwa [neg_zero,zero_sub,neg_neg,show splice (pulseJet 0 (-x) i) _ 2= _ from ?_] at p; simp [pulseJet,ringlet,flux,splice,tip]
 obtain ⟨a,r,c,_,_,hc,H⟩:=X.oils
 refine (tendsto_finsetSum Finset.univ (fun i _=> e (codeD d i))).congr' ?_; filter_upwards [H] with i b; rw [(section_bill d b hc (stream _) x).bud_eq,Finset.sum_apply]
abbrev chargedChart (D:Division):ℤ:= 4* (∑ i∈ ((Finset.univ:Finset SU.Slot).filter fun i=> SU.charge i∈ D), (let x:SU.F→ℤ:=![1,-1,0,0,0]; (match i.2 with| .inl j=>x j.val.1+x j.val.2|.inr j=>-x j))^2)
private lemma amount : (homeWeight d*homeWeight d).trace= -(chargedChart d:ℂ):=by
 unfold chargedChart homeWeight; rw [Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]; push_cast; let f:=(![1,-1,0,0,0]:SU.F→ℤ); let s:=Finset.univ.filter (fun i:SU.Slot=>SU.charge i∈d); let q (i:SU.Slot):ℤ:=match i.2 with| .inl j=> f j.val.1+ f j.val.2|.inr j=> -f j
 change _= -(4*∑ i∈s,(q i:ℂ)^2); rw [Finset.sum_subtype s (p:=(·∈s)) (fun _=> Iff.rfl),Finset.mul_sum,←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _
 have ht(i:SU.F):(dye.val i:ℝ)=(↑(f i):ℝ):=by fin_cases i <;> norm_num [f,dye]
 have hb(i:SU.Slot):Kea.freqD dye i=(q i:ℝ):=by unfold q Kea.freqD; cases i.2 <;> simp only [ht, Int.cast_add, Int.cast_neg]
 unfold lock wgt; rw [hb]; push_cast; ring_nf; norm_num [pow_two]
open scoped Classical
abbrev medalD (D:Division):ℂ:= (↑(chargedChart D):ℂ)/(Real.pi:ℂ)^2
lemma priceD {L: Ultrafilter ι} (X:Cross j (L:Filter ι)): ∃ p, X.Relax p ∧ ∀ d:Division,(seam 0 (moneyD d (p 2))).trace=medalD d:=by
 obtain ⟨p,h⟩:=Cross.builds X; obtain ⟨r,e⟩:=looming X.yes; obtain ⟨u,f,V⟩:=e.passes X.yes L X.M
 refine ⟨p,h,fun D=>?_⟩; let A:=(6*(Real.pi:ℂ)^2)⁻¹; have he:Silk.τ (jac u)= A:= tendsto_nhds_unique_of_eventuallyEq (arrives_jac f|>.co 0) tendsto_const_nhds (Eventually.of_forall fun i=>topMap e X.yes _); rw [region_price D h _ (h.shade e f),he,amount]; unfold A medalD; field_simp
variable {N:Side}
theorem polarTest (t:1≤j)(x:Cover)(ε:ℝ)(z:0<ε):∃ v:ℕ,∀ {N:Side}, v ≤N.val → ∀ m:Tulip.Male, ‖ bud (harvest (funde j m N) d x (stream N)) 2-medalD d‖ < ε:=by
 by_contra! h
 choose n k1 M K2 using h; let L:= Ultrafilter.of (atTop:Filter ℕ); let Γ:= Ultrafilter.of_le (atTop:Filter ℕ); let A:= fun i:ℕ=>n i; let Y:Cross j (L:Filter ℕ):=⟨A,M,tendsto_atTop.mpr (fun x=> Γ ((eventually_ge_atTop x).mono fun i v=>v.trans (k1 i))),t⟩
 obtain ⟨U,p,u⟩:= priceD Y; have q:= branch_formula d p x; rw [u d] at q; obtain ⟨i,p⟩:= (Metric.tendsto_nhds.mp q ε z).exists; rw [dist_eq_norm] at p; exact p.not_ge (K2 i)
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
lemma factorsD : chargedChart {2}=72 ∧ chargedChart {4}=24 ∧ chargedChart {2,4}=96:=by decide +kernel
#print axioms priceD
#print axioms polarTest
#print axioms factorsD
end Zephyr.Chern.IndexMag
