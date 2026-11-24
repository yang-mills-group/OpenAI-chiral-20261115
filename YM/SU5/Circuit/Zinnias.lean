import YM.SU5.Circuit.Lieble
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
abbrev duoPower (G:Gauge)(y:ℂ):ℂ:= 2*Fintype.card G.ColorIndex*y^2
def spectrumColor (F D:PlaqAxes)(G:Gauge)(X:Gaia):ℂ:= duoPower G (specter F D X)
private lemma intoEarth (a:ℝ) : Tendsto (fun N:Side=> a*pinch (More N)) atTop (𝓝 0):=by
 have he:Tendsto (fun N:Side=>(More N).val) atTop atTop:=tendsto_atTop.mpr fun b=> by filter_upwards [eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with i p; change b+1≤(i:Side).val at p; change b ≤ (i:Side).val*2; omega
 have ht:= ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_natCast_atTop_atTop.comp he)).const_mul (a*Real.pi); simpa [pinch,Function.comp_def,div_eq_mul_inv,mul_assoc] using ht
include S s Z e w q η p
lemma monetary (ε:ℝ)(a:0<ε)(G:Gauge): ∀ᶠ i in atTop,∀ᶠ n: Side in atTop,∀ M:Bed,M.covered σ C → Floor M q (More n) η C → dist (duoPower G (magnify M (R i) (Pl F) (Pl D) (U i-W i) (More n))) (spectrumColor F D G X) ≤ ε:=by
 by_contra h; push Not at h; obtain ⟨d,v,A⟩:= extraction_of_frequently_atTop h; let T (i):= R (d i); let B(i:ℕ):= ((i:ℝ)+1)⁻¹
 have ht(i:ℕ):0<B i:=by unfold B; positivity
 let f(M:Bed)(i n):=duoPower G (magnify M (T i) (Pl F) (Pl D) (U (d i)-W (d i)) (More n)); let x:=spectrumColor F D G X; -- frequently!
 choose N M Mh Mu hN ψ using fun i=> (show ∃ (n:Side)(M:Bed), M.covered σ C ∧ Floor M q (More n) η C ∧ T i *pinch (More n) ≤ B i ∧ ε<dist (f M i n) x from by
   have he:∃ᶠ n:Side in atTop, ∃ M:Bed, M.covered σ C ∧ Floor M q (More n) η C ∧ ε < dist (f M i n) x:=by
     exact A i
   obtain ⟨n,⟨M,hx,S,F⟩,N⟩:= (he.and_eventually ((intoEarth (T i)).eventually (ge_mem_nhds (ht i)))).exists; exact ⟨n,M,hx,S,N,F⟩)
 let y:=T; let ν(i):=More (N i); let z'(i):= U (d i)-W (d i); have hc: Tendsto B atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:= (1:ℝ)))) -- tune
 have hE:Yard ν T:=⟨fun i=>s _,S.comp v.tendsto_atTop,squeeze_zero (fun i=> mul_nonneg (s _).le (Ember.pinch_pos _).le) hN hc,fun i=> by change Even ((N i).val*2); exact ⟨(N i).val, by omega⟩⟩
 have H' := mercury F D (z:=z') hE (Z.comp v.tendsto_atTop) e Mh Mu p w
 have U':Continuous (duoPower G):=by unfold duoPower; fun_prop
 obtain ⟨i,h⟩:= (Metric.tendsto_nhds.mp (show Tendsto (fun i=> f (M i) i (N i)) atTop (𝓝 x) from U'.continuousAt.tendsto.comp H') ε a).exists; exact (lt_asymm h (ψ i))
omit S s Z e
variable (G:Gauge)
variable {n:Side}{M:Bed}{A:PathData G}
omit w in
lemma properQuest {θ v a:ℝ}(B:A.Bounds q θ v a)(P:Attached M A)(b c:Cover)(x:M.covered σ C) (L:Floor M q (More n) η C) (y:ℝ)(hr:0<y)(t u:ℝ)(m:0<t)(h: |u| ≤2): let f:= blazing G F b t m; let g:= blazing G D c t m; let κ:=(magnify M y (Pl F) (Pl D) (b-c) (More n)); let α:=fun f:Etch G Unit=>Etch.muρ f q B P u (More n); ‖(y:ℂ)^8*((↑(Etch.muρ (f.radial g) q B P u (More n)-α f*α g)):ℂ)-(u:ℂ)^4*(duoPower G κ)‖≤ tollK q G*(y^8/t):=by -- tune `↑` parentheses
 intro f g κ α; let N:=More n; let r':=rimble N M (wrap N b, Pl F) (wrap N c,Pl D)
 have hn: Even (More n).val:=⟨n.val,by change n.val*2=_; omega⟩
 have he:κ=(y:ℂ)^4*r':=by unfold κ magnify; rw [rimflare (More n) M (wrap (More n) (b-c)) 0 (b-c) (sub_zero _)]; unfold r'; rw [rimflare N M (wrap N b) (wrap N c) (b-c) (map_sub (wrap N) b c).symm]
 let P':=(Etch.muρ (f.radial g) q B P u (More n)); let S':= 2*Fintype.card G.ColorIndex*(u:ℂ)^4*r'^2
 rw [he]; change ‖(y:ℂ)^8* (↑(P'-_):ℂ)-_‖ ≤ _
 rw [show (u:ℂ)^4*_= (y:ℂ)^8 * S' from ?_,←mul_sub,norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg hr.le]; swap; · unfold S' duoPower; ring
 exact (mul_le_mul_of_nonneg_left (regard B P L x p F D b c m hn h) (by positivity :0≤ y^8)).trans_eq (by ring)
variable (t:∀ i,0<L i)(hψ: Tendsto (fun i=> R i ^8 / L i) atTop (𝓝 0))
include S s Z e t hψ
lemma quoteV (ε:ℝ)(a:0<ε): ∀ᶠ i in atTop,∀ᶠ n:Side in atTop, ∀ (M:Bed)(p':M.covered σ C)(z:Floor M q (More n) η C)(X':PathData G){θ v a:ℝ}(B:X'.Bounds q θ v a)(P: Attached M X') (u:ℝ), |u| ≤ 2 → let f:= blazing G F (U i) (L i) (t i); let g:= blazing G D (W i) (L i) (t i); let α:=fun f:Etch G Unit=>Etch.muρ f q B P u (More n); ‖(R i:ℂ)^8*((↑(Etch.muρ (f.radial g) q B P u (More n)-α f*α g)):ℂ)-(u:ℂ)^4*spectrumColor F D G X‖ ≤ ε:=by
 have ht:Tendsto (fun i=> tollK q G*(R i^8/L i)) atTop (𝓝 0):=by simpa only [mul_zero] using hψ.const_mul (tollK q G)
 filter_upwards [monetary F D q η p w s S Z e (ε/32) (by positivity) G, ht.eventually (ge_mem_nhds (show 0<ε/2 by positivity))] with i f g; filter_upwards [f] with n h; intro M hq u' X' θ v a B P u χ f g' α
 let K:=duoPower G (magnify M (R i) (Pl F) (Pl D) (U i-W i) (More n)); let E:=(u:ℂ)^4; have hR:‖E‖≤ (2:ℝ)^4:=by unfold E; rw [norm_pow,Complex.norm_real]; exact pow_le_pow_left₀ (norm_nonneg _) χ _
 refine le_trans (norm_sub_le_norm_sub_add_norm_sub _ (E*K) _) ((add_le_add ((properQuest F D q η p G B P (U i) (W i) hq u' (R i) (s i) (L i) u (t i) χ).trans g) ?_).trans (b:= ε/2+(2:ℝ)^4*(ε/32)) (le_of_eq (by ring))) -- orientation p w params
 rw [←mul_sub,norm_mul]; exact mul_le_mul hR (by rw [←dist_eq_norm]; exact h M hq u') (norm_nonneg _) (by norm_num)
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.quoteV
