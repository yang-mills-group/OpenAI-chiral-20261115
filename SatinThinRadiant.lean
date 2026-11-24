import SatinThinStellar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open CF CF.Lat CF.Cube CF.Onyx CF.Ember
open Stationary (Gaia)
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace Classical Matrix.Norms.Frobenius
variable {C σ:ℝ}
variable (F D: PlaqAxes)(q:Clip)(η:ℝ)(p:0 < σ)(w:0<C)
local notation "Pl"=> plaquette
variable {R:ℕ→ℝ}{L:ℕ→ℝ}{U W:ℕ→ Cover}{X: Gaia}
variable (s:∀ i,0<R i)(S:Tendsto R atTop atTop) (Z:Tendsto (fun i=> riseX (R i) (U i-W i)) atTop (𝓝 X)) (e:X≠0)
private lemma pewEarth (a:ℝ) : Tendsto (fun N:Side=> a*pinch (More N)) atTop (𝓝 0):=by
 have he:Tendsto (fun N:Side=>(More N).val) atTop atTop:=tendsto_atTop.mpr fun b=> by filter_upwards [eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with i p; change b+1≤(i:Side).val at p; change b ≤ (i:Side).val*2; omega
 have ht:= ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_natCast_atTop_atTop.comp he)).const_mul (a*Real.pi); simpa [pinch,Function.comp_def,div_eq_mul_inv,mul_assoc] using ht
open Etch Garland
variable {P:ℕ→Side}{M:ℕ→Bed}(p1:Yard P R)(v1:∀ i,(M i).covered σ C)(v2:∀ i, Floor (M i) q (P i) η C) (z:PlaqAxes→ℝ)
abbrev Starℓ (z:PlaqAxes→ℝ) (x y:Cover)(G:Gauge)(M:Bed) (n:Side) := wholeV z (fun i j=> duoPower G (pairR (wrap n x) (wrap n y) M i j))
def spectrumℓ (z:PlaqAxes→ℝ)(G:Gauge)(x:Gaia) := wholeV z fun i j=> spectrumColor i j G x
private lemma rise_const (q:Cover)(r:ℝ)(v:Cover): riseX r (q+v) = riseX r q+r⁻¹ • moor (fun i=> (v i:ℝ)):=by ext i; dsimp [riseX,moor,Stationary.exileE]; push_cast; ring -- tune maybe exileE opacity
include p1 v1 v2 Z e p w q η
lemma radiant :Tendsto (fun i=> (R i:ℂ)^4 * pairR (wrap (P i) (U i)) (wrap (P i) (W i)) (M i) F D) atTop (𝓝 (specter F D X)):=by
 let X'(i j:PlaqAxes)(v w:Tray)(N):= (R N:ℂ)^4 * singleBeam (wrap (P N) (U N)) (wrap (P N) (W N)) (M N) i j v w; let x:=specter F D X
 let point(i:PlaqAxes)(q:Tray):=(atTray q.1 q.2 i).offset
 have he(t u:Tray): Tendsto (X' F D t u) atTop (𝓝 x):=by
    let v:= point F t - point D u; let a(i):= U i-W i + v; have hp:Tendsto (fun i=> riseX (R i) (a i)) atTop (𝓝 X):=by
       have hV := Tendsto.smul (M:=ℝ) (tendsto_inv_atTop_zero.comp p1.high) (tendsto_const_nhds (x:=moor (fun i=> (v i:ℝ)))); unfold a; simp_rw [rise_const]; simpa only [zero_smul,add_zero,Function.comp_apply] using Z.add hV
    refine (mercury F D p1 hp e v1 v2 p w).congr (fun i=> ?_); unfold magnify X' singleBeam curlsW
    let N:= P i; let B':=M i; let x:= wrap N (point F t)+wrap N (U i); let y:=wrap N (point D u)+wrap N (W i); let z':=wrap N (a i)
    change _ * rimble N B' (z', Pl F) (0,Pl D)=_*rimble N B' (x,Pl F) (y,Pl D)
    refine congrArg ((R i:ℂ)^4 * ·) ((rimflare N B' z' 0 (a i) (sub_zero _) (Pl F) (Pl D)).trans (rimflare N B' x y (a i) (by unfold x y a; simp [v]; abel) (Pl F) (Pl D)).symm)
 let f(i:ℕ):= ∑ v:Tray,∑ w:Tray, X' F D v w i
 have h:Tendsto f atTop (𝓝 (∑ v:Tray,∑ w:Tray,x)):= tendsto_finsetSum _ fun j _=> tendsto_finsetSum _ fun i _=> he j i
 let g(i):=(4:ℂ)⁻¹*((4:ℂ)⁻¹*f i); have hx:Tendsto g atTop (𝓝 x):=by convert (h.const_mul (4:ℂ)⁻¹).const_mul (4:ℂ)⁻¹ using 2; simp [Tray] -- maybe order
 refine hx.congr fun i=>?_; unfold g f pairR X'; simp_rw [←mul_sum]; ring
lemma fledgling(G:Gauge): Tendsto (fun i=> (R i:ℂ)^8*Starℓ z (U i) (W i) G (M i) (P i)) atTop (𝓝 (spectrumℓ z G X)):=by
 let f(t u:PlaqAxes)(i:ℕ):= duoPower G ((R i:ℂ)^4 * pairR (wrap (P i) (U i)) (wrap (P i) (W i)) (M i) t u)
 have hc(t u:PlaqAxes): Tendsto (f t u) atTop (𝓝 (spectrumColor t u G X)):= (show Continuous (duoPower G) from (by unfold duoPower; fun_prop)).continuousAt.tendsto.comp (radiant t u q η p w Z e p1 v1 v2)
 let S(i:ℕ):= wholeV z fun t u=> f t u i; have hp:Tendsto S atTop (𝓝 (spectrumℓ z G X)):=tendsto_finsetSum _ fun j _=> tendsto_finsetSum _ fun i _=> (hc j i).const_mul _ -- tune
 refine hp.congr fun i=>?_ ; unfold S Starℓ wholeV; simp_rw [mul_sum]; refine sum_congr rfl fun j _=> sum_congr rfl fun q _=>(?_); unfold f duoPower; ring

omit p1 v1 v2
include s S
lemma radial_rate (ε:ℝ)(a:0<ε)(G:Gauge): ∀ᶠ i in atTop,∀ᶠ n: Side in atTop,∀ M:Bed,M.covered σ C → Floor M q (More n) η C → dist ((R i:ℂ)^8 * Starℓ z (U i) (W i) G M (More n)) (spectrumℓ z G X) ≤ ε:=by
 by_contra h; push Not at h; obtain ⟨d,v,A⟩:= extraction_of_frequently_atTop h; let T (i):= R (d i); let B(i:ℕ):= ((i:ℝ)+1)⁻¹
 have ht(i:ℕ):0<B i:=by unfold B; positivity
 let f(M:Bed)(i n):=(T i:ℂ)^8* Starℓ z (U (d i)) (W (d i)) G M (More n); let x:=spectrumℓ z G X; -- frequently!
 choose N M Mh Mu hN ψ using fun i=> (show ∃ (n:Side)(M:Bed), M.covered σ C ∧ Floor M q (More n) η C ∧ T i *pinch (More n) ≤ B i ∧ ε<dist (f M i n) x from by
   have he:∃ᶠ n:Side in atTop, ∃ M:Bed, M.covered σ C ∧ Floor M q (More n) η C ∧ ε < dist (f M i n) x:=by
     exact A i
   obtain ⟨n,⟨M,hx,S,F⟩,N⟩:= (he.and_eventually ((pewEarth (T i)).eventually (ge_mem_nhds (ht i)))).exists; exact ⟨n,M,hx,S,N,F⟩)
 let y:=T; let ν(i):=More (N i); let z'(i):= U (d i)-W (d i); have hc: Tendsto B atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:= (1:ℝ)))) -- tune
 have hE:Yard ν T:=⟨fun i=>s _,S.comp v.tendsto_atTop,squeeze_zero (fun i=> mul_nonneg (s _).le (Ember.pinch_pos _).le) hN hc,fun i=> by change Even ((N i).val*2); exact ⟨(N i).val, by omega⟩⟩
 have H' := fledgling (U:=U∘d) (W:=W∘d) q η p w (Z.comp v.tendsto_atTop) e hE Mh Mu z G
 obtain ⟨i,h⟩:= (Metric.tendsto_nhds.mp (show Tendsto (fun i=> f (M i) i (N i)) atTop (𝓝 x) from H') ε a).exists; exact (lt_asymm h (ψ i))
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.radial_rate
