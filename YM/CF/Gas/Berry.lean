import YM.CF.Gas.League
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Lattice Branch Tenant Petal Palot Stilo Corona RG Push.AbsoluteSums Trees Ursell Relation Graph
open scoped Topology Classical BigOperators
variable {ι A D G E:Type}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][NormedCommRing E][NormOneClass E][NormedAlgebra ℝ E][CompleteSpace E][TopologicalSpace D]
variable {n:Side}
variable{w:Y n→ℝ}{W:Y n→ D→E}{a d γ δ r:ℝ}{L:Lodge (Site n) E D G}{X:ι→Y n}
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
section price
-- already multiplied perturbation by aux weight. Bring nonunitary dilation only under Assets.
variable {M:ℕ}{ρ:ℕ→ℝ}(B:E→ₐ[ℝ] E)(p:Continuous B)(t:Ready stern 0 w a γ δ d)(h:0≤a)(l:∀ i,creditS i (W i) (w i) L)
variable (u:∀ i:ℕ,0 < ρ i)(hu:∀ i:ℕ, ρ i ≤1)(hp: Antitone ρ)(q:Y n)
variable {V:F→D}{S:Set F}(s:IsOpen S)(hS:∀ j:Y n,∀ x∈S,Assets M (fun x=> B (W j (V x))) x (ρ (j.val.card)) (w j))
include B p t h u hu hp hS s q l
lemma ascent_s (x:F)(g:x∈S): Assets M (fun i=>B (Fiscal W q (V i))) x (ρ (q.val.card)) (sumTax w q):=by
 let J:=ρ (q.val.card); have he(z)(x)(g:x∈S): Assets M (fun i=>B (strictX z q W (V i))) x J (wageA z q w):=by
    by_cases e:q=tideU z; swap; · simp_rw [strictX,wageA,if_neg e,map_zero]; exact Assets.fixed _ norm_zero.le
    have ht(J:SongQ z.1):(z.2 J).val⊆q.val:= e.symm ▸ κc z J
    unfold wageA strictX; simp_rw [if_pos e, guava,map_smul,map_prod]; unfold clusters; rw [mul_div_right_comm]; refine ((Assets.prodF (u _).le univ (f:=fun j i=> B (W (z.2 j) (V i))) (fun i _=> (hS (z.2 i) x g).cheaperA (u q.val.card).le (hp (card_le_card (ht i))))).smB (u _).le _).monoL ?_
    rw [norm_div,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity)]
 let m₁(i):= wageA i q w; have hz:=τ_w q t h
 let P : E →L[ℝ] E:=⟨B.toLinearMap,p⟩ -- tune
 have hv(x): B (Fiscal W q (V x))=∑' z:Clusters (Y n),B (strictX z q W (V x)):=by
    let U(z):=strictX z q W (V x); have hq:Summable U:=Summable.of_norm_bounded hz (fun z=>(L.normF _).trans ((dues q z l).owns _)); exact P.map_tsum hq
 simp_rw [hv]; let I:=Clusters (Y n); letI : MeasurableSpace I:=⊤; letI : MeasurableSingletonClass I:= ⟨fun _=> trivial⟩; letI : TopologicalSpace I:=⊥; letI : DiscreteTopology I:= ⟨rfl⟩; exact sum_assets (I:=I) (s:=s) (f:=fun z x=>B (strictX z q W (V x))) g (u _ ) (hu _) he hz
end price
variable {w':ι→ℝ}{W':Finset ι→D→ E}
abbrev Xi (X:ι→Y n)(W': Finset ι→D→ E)(p:Y n)(u:D):E:= bankB X (fun i=>W' i u) p
def PathsX(X:ι→Y n)(F: Finset ι→D→ E)(w':ι→ℝ)(L:Lodge (Site n) E D G):Prop:=∀ T:Finset ι,Token L (T.biUnion fun i=>(X i).val) (F T) (heavy w' T) (fun _=>True)
lemma credit_u(i:Y n) (u:∀ i,w' i≠0→Grove (terr _) (X i).val)(p:PathsX X W' w' L): creditS i (Xi X W' i) (CoinX X w' i) L:=by
 rw [show Xi X W' i=(fun x=>∑ j∈slateF X i,W' j x) from funext fun x=> bank_p ..]; have he : Token L i.val _ (CoinX X w' i) (fun _=>True):= Token.mass (slateF X i) W' (heavy w') (fun T t=>(coverB t) ▸ p T)
 exact { he with shape:=coin_heat w' u i}
variable {M:ℕ}{β:ℕ→ℝ}{Z:F→D}
lemma credit_jet (x:F)(B:E→ₐ[ℝ] E)(q:Y n)(t:0≤β q.val.card)(h:∀ T: Finset ι,Assets M (fun i=>B (W' T (Z i))) x (β (roof (fun i=> (X i).val) T).card) (heavy w' T)): Assets M (fun i=> B (Xi X W' q (Z i))) x (β (q.val.card)) (CoinX X w' q):=by
 simp only [Xi,bank_p,map_sum]; exact Assets.tot t (slateF X q) (fun i l=>(show roof (fun i=>(X i).val) i=q.val from coverB l) ▸ h i)
end YM.CF.Gas
