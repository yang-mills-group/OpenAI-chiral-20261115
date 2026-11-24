import Zephyr.Chern.Vanish
import Zephyr.Chern.Vaulted
import Zephyr.Chern.Rime
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF YM.CF.Tulip Filter Topology


lemma color_weight : ∃ c:ℝ, 0<c ∧ (cab*cab).trace= -(c:ℂ) := by
  let f i:ℝ := 4* (Kea.freqD dye i)^2
  have p i:0≤ f i := by unfold f; positivity
  use ∑ i,f i
  constructor
  · let j:SU.Slot := (0, Sum.inr 0)
    have h:0<f j:=by norm_num [f,j,Kea.freqD,dye]
    exact lt_of_lt_of_le h (Finset.single_le_sum (fun i _=>p i) (Finset.mem_univ j))
  rw [cab,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.ofReal_sum,←Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _=>?_
  simp only [lock,wgt,f,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow]
  calc
    _ = Complex.I*Complex.I*(4*(Kea.freqD dye i:ℂ)^2):=by ring
    _ = _ := by rw [Complex.I_mul_I];ring

lemma Cross.inly {κ:Type*}{L:Ultrafilter κ}{s:ℕ} (X:Cross s (L:Filter κ)):
    ∃ p,X.Relax p ∧ 0<(seam 0 (p 2)).trace.re := by
  obtain ⟨p,h⟩:= Cross.builds X
  obtain ⟨r,q⟩:=looming X.yes
  obtain ⟨u,a,hu⟩:=q.passes X.yes L X.M
  have b:=hu.price
  refine ⟨p,h,?_⟩
  have j: Jet (p 0) (p 1) (p 2) (icolor cab):=h.toGains.jet
  rw [h.shade q a] at j
  obtain ⟨c,pc,eq⟩:=color_weight
  rw [j.receipt,eq, neg_mul_neg]
  simp only [Complex.mul_re,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
    Complex.ofReal_im, Complex.ofReal_re]
  ring_nf
  positivity

/-- Unnormalised single-site trace (- A subtraction is optional in
positive degree). Actual lifted sampling on per-height profiles. -/
def sprig {N:Side}(F: Oil N)(A:StemA N) (x:Cover)(t:ℝ):ℂ :=
    ∑ i:IS, drip F A (tag N x i) (tag N x i) t

variable {N:Side}{F:Oil N}{a r e:ℝ}
lemma solo_sprig (h:Solo a r F e)(he:0<e)(A:StemA N)(x:Cover):
    Bloom (sprig F A x) (∑ i:IS,wad F A (tag N x i) (tag N x i)) :=
  Bloom.sum _ fun _ _=> (solo_bud h he).bloom

lemma solo_sprout (h:Solo a r F e)(he:0<e)(A:StemA N)(x:Cover):
    Bloom (sprig F A x) (∑ i:IS,tuft F A x x i i):=by
  simp only [tuft, (tap_wad h he ..).bud_eq, flag_sq, one_smul]
  exact solo_sprig h he ..

variable {s:ℕ}

lemma Cross.Relax.imprint {κ:Type*}{L: Filter κ}{X: Cross s L}
    {p: Stack}(h:X.Relax p)(x:Cover):
    Tendsto (fun u=>bud (sprig (X.oil u) (stream _) x) 2) L (𝓝 (seam 0 (p 2)).trace):=by
  have e(i:IS): Tendsto (fun u=>tuft (X.oil u) (stream _) x x i i 2) L
      (𝓝 (seam 0 (p 2) i i)):=by
    have d:=h.pulse 0 (-x) i i 2
    have k: splice (pulseJet 0 (-x) i) (tip p 0 i i) 2=seam 0 (p 2) i i:=by
      simp [pulseJet,ringlet,flux,splice,tip]
    rwa [neg_zero,zero_sub,neg_neg,k] at d
  obtain ⟨b,r,c,_,_,hc,H⟩:=X.oils
  exact (tendsto_finsetSum Finset.univ (fun i _=>e i)).congr'
    (H.mono (fun u hu=>by 
      dsimp only;rw [(solo_sprout hu hc _ x).bud_eq,Finset.sum_apply]))

lemma germ (hs:1≤s) : ∃ v:ℕ,∀ {N:Side},v≤N.val→∀ m:Male,∀ A:StemA N,∀ x,
    Bud (sprig (funde s m N) A x):=by
  obtain ⟨a,r,e,h,t,v,w,S⟩:=funde_s s hs
  exact ⟨w,fun {N} m _ _ _=> (solo_sprig (S _ _ m) v ..).1⟩

/-- Exact quadratic Taylor test (plain coefficients, half 2nd derivative)
on a single matter site, the whole representation. Uniform in Male,
for fixed s indexing the projection (not RG height). -/
theorem deep_flux (hs:1≤s) (x:Cover):
    ∃ δ:ℝ,0<δ ∧ ∃ v:ℕ,∀ {N:Side}, v≤N.val→∀ m:Male,
    δ < (bud (sprig (funde s m N) (stream N) x) 2).re := by
  by_contra! j
  have h(n:ℕ) : ∃ N:Side,n≤N.val∧ ∃ m:Male,
      (bud (sprig (funde s m N) (stream N) x) 2).re ≤ 1/(n+1:ℝ):=j _ (by positivity) n
  choose n h m t using h
  let L:= Ultrafilter.of (atTop:Filter ℕ)
  have le : (L:Filter ℕ)≤atTop := Ultrafilter.of_le _
  have g : Tendsto (fun i=>(n i).val) (L:Filter ℕ) atTop := by
    refine tendsto_atTop.2 fun b=> ?_
    filter_upwards [(eventually_ge_atTop b).filter_mono le] with u v
    exact v.trans (h u)
  let Y : Cross s (L:Filter ℕ) := ⟨n,m,g,hs⟩
  obtain ⟨p,hr,v⟩:= Y.inly
  exact not_le.mpr v (le_of_tendsto_of_tendsto'
    ((Complex.continuous_re.tendsto _).comp (hr.imprint x)) (tendsto_one_div_add_atTop_nhds_zero_nat.mono_left le) t)
