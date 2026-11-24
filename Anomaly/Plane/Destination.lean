import Anomaly.Plane.Track
import Anomaly.Plane.Ruby
import SatinThinRadiant
/-! XL Variant of ThinRadiant.rates for pre-Ward comparisons.
Positions in gauge Cover translated via wrap. Incidences CAN vary freely
in all their observation budgets.
-/
set_option autoImplicit false
set_option maxHeartbeats 670000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.Pier
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open CF CF.Lat CF.Cube CF.Onyx CF.Ember
open Stationary (Gaia)
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace Classical Matrix.Norms.Frobenius
variable {C σ:ℝ}
variable (F D: PlaqAxes)(q:Clip)(η:ℝ)(p:0 < σ)(w:0<C)
local notation "Pl"=> plaquette
variable {R:ℕ→ℝ}{Q:ℕ→ℕ}{U W:ℕ→ Cover}{X: Gaia}
variable (s:∀ i,0<R i)(S:Tendsto R atTop atTop) (Z:Tendsto (fun i=> riseX (R i) (U i-W i)) atTop (𝓝 X)) (e:X≠0)
-- elementary unwrap chosen at each size
lemma selected {N:Side}(X:Cover){x:Site N}{r:ℕ}(h:separation (wrap N X) x ≤ r):∃ u:Cover,u∈ Lattice.box r ∧ wrap N (X+u)= x:=by
 rw [separation_comm] at h; let a:= Lattice.lift (x-wrap N X)
 have ht(i): -(r:ℤ) ≤ a i ∧ a i ≤ r:=by have hx:(a i).natAbs≤r:= (component_le _ i).trans h; omega
 exact ⟨a,box_test.mpr ⟨fun i=>(ht i).1,fun i=>(ht i).2⟩, by unfold a; rw [map_add,Lattice.wrap_lift]; exact add_sub_cancel ..⟩ -- theorem tune
-- copied perspective. tolerance tending to zero at any rate. only moment vector costs need uniform constant (cp4). if such costs polynomial in b maybe requires rate expression; not here
private lemma pewTheater (a:ℝ) : Tendsto (fun N:Side=> a*pinch (More N)) atTop (𝓝 0):=by
 have he:Tendsto (fun N:Side=>(More N).val) atTop atTop:=tendsto_atTop.mpr fun b=> by filter_upwards [eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with i p; change b+1≤(i:Side).val at p; change b ≤ (i:Side).val*2; omega
 have ht:= ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_natCast_atTop_atTop.comp he)).const_mul (a*Real.pi); simpa [pinch,Function.comp_def,div_eq_mul_inv,mul_assoc] using ht
include s
lemma zeroMovie (h:Tendsto (fun i=> (Q i:ℝ)/R i) atTop (𝓝 0))(g:∀ i,U i∈ Lattice.box (Q i)):
 Tendsto (fun i=> riseX (R i) (U i)) atTop (𝓝 0):=by
 have hu(j:Axis): Tendsto (fun i=>(U i j:ℝ)/R i) atTop (𝓝 0):=by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun i=>-((Q i:ℝ)/R i)) ?_ h ?_ ?_ -- tactic
    · simpa only [neg_zero] using h.neg
    · intro i; have ht:= (box_test.mp (g i)).1 j; dsimp; rw [←neg_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast ht) (s i).le
    intro i; have ht:= (box_test.mp (g i)).2 j; exact div_le_div_of_nonneg_right (by simpa using (show ((U i j:ℤ):ℝ) ≤ ((↑(Q i):ℤ):ℝ) from Int.cast_le.mpr ht)) (s i).le
 exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hu : Tendsto (fun i j=>(U i j:ℝ)/R i) atTop (𝓝 (fun i:Axis=>(0:ℝ))))
include Z S e p w
lemma matchedF (h:Tendsto (fun i=> (Q i:ℝ)/R i) atTop (𝓝 0))(ε:ℝ)(a:0<ε): ∀ᶠ i in atTop,∀ᶠ n:Side in atTop, ∀ M:Bed,M.covered σ C→ Floor M q (More n) η C →∀ x y:Site (More n),separation (wrap (More n) (U i)) x≤Q i→separation (wrap (More n) (W i)) y≤ Q i→ ‖(R i:ℂ)^4*rimble (More n) M (x,Pl F) (y,Pl D)-specter F D X‖ ≤ ε:=by
 by_contra g; push Not at g; obtain ⟨d,v,A⟩:= extraction_of_frequently_atTop g; let T (i):= R (d i); let B(i:ℕ):= ((i:ℝ)+1)⁻¹; let f(N:Side):=More N
 have ht(i:ℕ):0<B i:=by unfold B; positivity
 let ℓ (i) (N:Side) (M:Bed) (x y:Site (More N)) :=(T i:ℂ)^4*rimble (More N) M (x,Pl F) (y,Pl D); let z:=specter F D X
 choose N M Mh Mu hN u V uQ vQ ψ using fun i=>(show ∃ (N:Side)(M:Bed), M.covered σ C ∧ Floor M q (More N) η C ∧ T i *pinch (More N) ≤ B i ∧ ∃ (u V:Cover),u∈Lattice.box (Q (d i))∧ V∈Lattice.box (Q (d i))∧ε<‖ℓ i N M (wrap (More N) (U (d i)+u)) (wrap (More N) (W (d i)+V))-z‖ from by
    obtain ⟨n,⟨M,Ma,Mr,x,y,pX,pY,he⟩,hp⟩:=(Frequently.and_eventually (A i) ((pewTheater (T i)).eventually (ge_mem_nhds (ht i)))).exists
    obtain ⟨u,v,rfl⟩:= selected _ pX; obtain ⟨V,t,rfl⟩:= selected _ pY
    exact ⟨n,M,Ma,Mr,hp,u,V,v,t,he⟩)
 let ν(i):=More (N i)
 have hc : Tendsto B atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:= (1:ℝ))))
 have hE:Yard ν T:=⟨fun i=>s _,S.comp v.tendsto_atTop,squeeze_zero (fun i=> mul_nonneg (s _).le (Ember.pinch_pos _).le) hN hc,fun i=> by change Even ((N i).val*2); exact ⟨(N i).val, by omega⟩⟩
 let m i:= U (d i)+u i-(W (d i)+V i); have hx:Tendsto (fun i=> riseX (T i) (m i)) atTop (𝓝 X):=by
    have hb:Tendsto (fun i=> ((Q∘d) i:ℝ)/T i) atTop (𝓝 0):= h.comp v.tendsto_atTop
    have hh:= (Z.comp v.tendsto_atTop).add ((zeroMovie hE.pos hb uQ).sub (zeroMovie hE.pos hb vQ)); simp only [sub_zero,add_zero] at hh; refine hh.congr fun i=> ?_; ext j; simp only [Function.comp_apply,T,riseX,moor,Pi.add_apply,m,Int.cast_add,Int.cast_sub,Pi.sub_apply,PiLp.add_apply,PiLp.sub_apply]; simp; ring
 have hw:=mercury F D hE hx e Mh Mu p w
 obtain ⟨i,hi⟩:=(Metric.tendsto_nhds.mp hw ε a).exists
 apply lt_asymm (ψ i); rw [dist_eq_norm] at hi; refine lt_of_eq_of_lt (?_) hi; unfold ℓ z magnify; let I:= ν i; let n:= N i; let X':=U (d i)+u i; let Y':=W (d i)+V i; let Q:= M i; let P:=wrap (ν i)
 rw [rimflare (More n) Q (P X') (P Y') (X'-Y') (P.map_sub ..|>.symm : _-_=P _), rimflare (ν i) Q (P (m i)) 0 (m i) (sub_zero _)] -- P smth reducibility
include q η in
lemma university (h:Tendsto (fun i=> (Q i:ℝ)/R i) atTop (𝓝 0))(ε:ℝ)(a:0<ε): ∀ᶠ i in atTop,∀ᶠ n:Side in atTop, ∀ (F D:PlaqAxes)(M:Bed),M.covered σ C→ Floor M q (More n) η C →∀ x y:Site (More n),separation (wrap (More n) (U i)) x≤Q i→separation (wrap (More n) (W i)) y≤ Q i→ ‖(R i:ℂ)^4*rimble (More n) M (x,Pl F) (y,Pl D)-specter F D X‖ ≤ ε:=by
 have hx(F D:PlaqAxes) := matchedF F D q η p w s S Z e h ε a;
 filter_upwards [eventually_all.mpr (fun i=> eventually_all.mpr (hx i))] with i h; exact eventually_all.mpr fun F=>eventually_all.mpr fun D=>h F D
end YM.Regis.Circuit.Pier
