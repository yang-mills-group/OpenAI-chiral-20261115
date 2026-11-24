import YM.CF.BPress.Wealth.March
import YM.CF.BPress.Wealth.ErrorBudget
/-!
Flag localization in the Mark draws. VolB-gauge `all actual flag ... at threshold t` and verification that hypotheses can be queried just on adaptive fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge Net
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}{y:ℝ}{X:Bands s B} {U V:Micro s} {K:Bills X E}{κ D ζ:ℝ} (p:Mission X y K V U)(t:ToneNoise y V)(q: Dividend D κ ζ y)
-- PL reach isn't needed: here threshold ≤4 tang distance. strict. Mark-only charged units might cancel but don't presume. Need Mark supports paid.
def Lost (y:ℝ)(X:Bands s B)(U:Micro s) := ∀ i:X.Index,∀ p, touched p⊆ X.band i→ group.chord (faceValue U p)≤ temp y
include p t q
lemma sign_result (S:Lost y X U)(x:Site s)(p':x∈flags (temp y) U) : ∃ i:X.Index, x∈X.gap i ∧ ∃ b:Tri s, delta (Fin.tail x) b ≤ 4 ∧ (i,b)∈ chosen X κ y K:=by
 obtain ⟨k,t',b'⟩:=flags_spec ..|>.1 p'; have hk: retained X 1 (.inl k):= fun i f=> b'.not_ge (S i k f); obtain ⟨i,v⟩:= open_gap X 1 k hk; refine ⟨i,v t',?_⟩; by_contra h; apply b'.not_ge; rw [←show faceR 1 U k=faceValue U k from (by rw [faceR,pull_id])]; refine drawn_flag q 1 k fun u=>?_ ; rw [addr_id]; let j:=aperture k u; have he:=near_back κ y q.branch p t j (q:=i); have hp : j∈inside (X.gap i):= inside_le v (ap_limit ..); apply he _ (inside_le (halo_subset _ _) hp); intro a p d; have co:= key_housed X (time_zero X i _ ((time_Zone X i _|>.2 ((inside_iff ..).mp hp).1)) _) p; apply h; refine ⟨Fin.tail j.1,?_,co ▸ d⟩
 apply le_trans (tail_sep x j.1); apply le_trans (separation_triangle x k.1 _); exact add_le_add ((separation_comm ..).le.trans (Work.E01.sep_touched k x t')) (Work.E01.sep_touched k _ ((inside_iff ..).mp (ap_limit k u)).1)

omit p t q
variable {Φ : Sheet.Atlas}{L C C':ℝ}{a: ℕ}(F:Net s Φ L y C C' a)(z:X.Slates)(x:X.Sky)
lemma roll_coast (u: z∈ X.permit Φ y (X.atmospheric x))(i): z i∈ X.choices Φ y (F.roll X z x V) i:= by
 have h := Fintype.mem_piFinset.mp (show z∈ _ from u); rw [roll,play,X.choices_air Φ y (X.clear_air (X.atmospheric x) (chartH X F z (X.atmospheric x)*V))]; exact h _ -- tune
lemma lost_support (p:0< y)(v: xi y≤1)(u: z∈X.permit Φ y (X.atmospheric x))(hD:∀ i∈X.dc,∀ U, BPress.dirichlet (X.band i) y U≠0→ ∀ k, touched k⊆ X.band i→ group.chord (faceValue U k) ≤ temp y)(hN:∀ i∈X.nc, ∀ U:Micro s,∀ p∈ Φ.pairs y ((X.mark i).reads U), F.markN (X.mark i) U p≠0→ ∀ k,touched k⊆ X.band i→ group.chord (faceValue U k)≤ temp y) (t:ToneNoise y V) : Lost y X (F.roll X z x V):=by
 let U:= F.roll X z x V; intro i k q; let h:= see (T:=Φ) (y:=y) X z U i; have e : F.takeN X U i h≠0:= (F.play_ne X z (x:=X.atmospheric x) (u:=V) (xi_pos p) v (fun j _=>t j) i).ne'; by_cases g:i∈X.dc; · exact hD i g U (by rw [←takeN_D F X U g h]; exact e) k q
 have ht:= roll_coast (V:=V) F z x u i; unfold takeN at e; rw [if_neg g] at e; apply hN i (mem_sdiff.mpr ⟨mem_univ _,g⟩) U h ?_ e k q; rw [← X.choices_B Φ y U g]; exact mem_image_of_mem _ ht

lemma list_flags (G:GapSize) (Φ: Sheet.Atlas)(C C':ℝ)(t:0<C)(u:0<C'): ∀ᶠ L in atTop, ∀ᶠ y in atTop, ∀ (s:Side)(a:ℕ)(F:Net s Φ L y C C' a)(X:Bands s (G.select y)), ∀ (x:X.Sky)(z:X.Slates)(V:Micro s), z∈X.permit Φ y (X.atmospheric x)→ ToneNoise y V → Lost y X (F.roll X z x V) :=by
 obtain ⟨K,l,f⟩:= BPress.dirichlet_support; have he := npl_xi.drop; filter_upwards [flags_N G Φ C C' t u] with L p; filter_upwards [eventually_gt_atTop (0:ℝ), f, (m_sub.const_mul K).drop.eventually (ge_mem_nhds zero_lt_one), p.2, he.eventually (ge_mem_nhds zero_lt_one)] with y w r k' v P s a F X x z V g t
 refine lost_support F z x w P g (fun i _ U h k p=>?_ ) (fun i _ U z p v' k g=> (v s a F X i U z p v' k g).trans (half_le_self (temp_pos w).le)) t; apply (r s (X.band i) U h _ p).trans; apply (div_le_one (temp_pos w)).mp; rw [mul_div_assoc]; exact k'
end YM.CF.BPress.Wealth
