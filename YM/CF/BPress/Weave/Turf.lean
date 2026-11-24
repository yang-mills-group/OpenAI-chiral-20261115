import YM.CF.BPress.Weave.Aura
import YM.CF.BPress.Weave.Bridge
/-! connected only *within each gap*. range costs both row and col. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s: Side}{B:BandWidth}(X : Bands s B)
def grass : Branch.Field X.Hcols:=⟨fun x y=>Grid.delta x.2 y.2,fun i=>delta_same _,fun i j=>delta_comm ..,fun i j k=>delta_triangle ..⟩
def Turf (S:Seal X.Hcols):Prop:= Grove (grass X) S ∧ ∀ u∈S,∀ v∈S,u.1=v.1
lemma turf_union {S T : Seal X.Hcols}(p:Turf X S)(q:Turf X T){v}(a:v∈S)(b:v∈T): Turf X (S∪T):=by
 have he(x:X.Hcols)(h:x∈ S∪T): x.1=v.1:= (mem_union.mp h).elim (fun z=>p.2 _ z _ a) (fun z=>q.2 _ z _ b); exact ⟨p.1.unite q.1 a b,fun x a y b=> (he x a).trans (he y b).symm⟩ -- tune
-- DecidableEq as Type class in Centr.perp not defeq physical; exact with convert using inst irr
private def centrPerp : Centr X.Hcols (Axon X):= {home:=zSite X,trunkP:= Turf X,perp:=fun p q u v=> by convert turf_union X p q u v using 1; congr 2; exact Subsingleton.elim _ _} -- tune Class.dec
abbrev soils:= centrPerp X
lemma turfed (u:X.Hcols) (r:ℕ) : Turf X (columnBall X u r):=by
 let F:=grass X; refine ⟨trunk (column_self u r) (fun y v=>?_ ),fun x a y b=> (column_eq.mp a).1.trans (column_eq.mp b).1.symm⟩
 induction r generalizing y with
 | zero => obtain ⟨p,h⟩:= column_eq.mp v; have hx:y=u:= Prod.ext p (eq_of_delta _ _ (Nat.eq_zero_of_le_zero h)).symm; subst y; exact .refl
 | succ n ih=>
   obtain ⟨p,e⟩:= column_eq.mp v; obtain ⟨z,g,c⟩:= decrease_bay u.2 y.2 e; let t:X.Hcols:=(u.1,z); let K:= columnBall X u n; have hc:t∈K:=column_eq.mpr ⟨rfl,g⟩; exact .tail (orig_sub (ih t hc) (column_mono X u (Nat.le_succ _))) ⟨ (column_mono X u (Nat.le_succ n)) hc,v,c⟩
lemma turf_lim (S:Seal X.Hcols)(h:Turf X S)(u:X.Hcols)(v:u∈S): S⊆ columnBall X u S.card :=fun i w=> column_eq.mpr ⟨h.2 i w u v,(h.1.lim u v i w).le⟩
-- PL pop
abbrev taxArea (r:ℕ):=(4*r+1)^3
lemma cost_bay (u:X.Hcols)(r:ℕ) : (columnBall X u r).card≤ taxArea r:=by
 let K:= bay (Grid.field 3 s) u.2 r; have he:K.card ≤ taxArea r:= local_count (one_dvd _) K u.2 (by change _ ⊆ bay _ _ (r*1); rw [mul_one]) (fun i _=> fun j : Fin 3 => one_dvd _) (by norm_num); refine le_trans (card_le_card_of_injOn (fun i:X.Hcols=>i.2) (s:=columnBall X u r) (t:=K) ?_ ?_) he -- tune
 · exact fun i h=> (bay_mem _).mpr (column_eq.mp h).2
 exact fun i h j p e=> Prod.ext (((column_eq.mp h).1).trans (column_eq.mp p).1.symm) e
abbrev n_ang (D:ℕ):= D*3* (SU.group.lieDim) -- IMPORTANT =24
abbrev Reveal := Fin B.D × SpatialDir -- (X omitted)
def fiberZ (x:Axon X) : Reveal (B:=B) × group.ColorIndex:= (x.1.2,x.2)
def coverPrice (X:Bands s B) (K:Seal X.Hcols):= univ.filter fun i=> zSite X i∈K
lemma cover_count (K:Seal X.Hcols): (coverPrice X K).card= n_ang B.D*K.card:=by
 unfold coverPrice n_ang; rw [card_filter]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; -- tune easier product predicate group
 change ∑ i:X.Hcols, ∑ j:Reveal (B:=B), ∑ l:group.ColorIndex,(if i∈K then 1 else 0)=_
 simp only [sum_const, card_univ,nsmul_eq_mul]; rw [← mul_sum,←mul_sum,←sum_filter]; simp [Reveal,SpatialDir,ColorIndex]; ring -- tune
-- all near
variable {X}{F: Fare X}{r:ℕ}{a k:ℝ}
lemma charge_bay (h:Connect X F r)(u:0≤k)(p:∀ S, ‖F S‖≤ k)(t:0≤a): Aura (soils X) a ((n_ang B.D*taxArea r:ℝ)*Real.exp (a*(taxArea r))*k) (fun S=> rowM X (F S)):=by
 let C:= n_ang B.D*taxArea r; let P:=Real.exp (a*taxArea r)*k; let V(i):=columnBall X (zSite X i) r; let H(i j):Prop:= zSite X j ∈ V i; let W:=fun (i:Axon X)(S:Seal X.Hcols)=> Matrix.of fun (j l:Axon X)=> if j=i then rowM X (F S) j l else 0; let w:= fun (i j l : Axon X)=> if j=i∧ H i l then k else 0
 have hv (i:Axon X) : rent a (V i) * k ≤ P:= mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cost_bay X _ r)) t)) u; have hC(i): (coverPrice X (V i)).card ≤ C:=(cover_count X _).le.trans (Nat.mul_le_mul_left _ (cost_bay X _ _)); have hP:0 ≤ P:= by unfold P; positivity
 have H' (i j) : H i j ↔ j∈coverPrice X (V i):= by simp [H,coverPrice]
 have spent(i) : ∑ j, (if H i j then P else 0)≤(↑(n_ang B.D):ℝ)* (taxArea r)*Real.exp (a*(taxArea r))* k:=by rw [←sum_filter]; rw [show univ.filter (H i)=coverPrice X (V i) by ext1; simp [H']]; simp only [sum_const,nsmul_eq_mul]; exact le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hC i)) hP) (Eq.le (by unfold P C; push_cast; ring))
 refine Aura.pack V w W ?_ (by positivity) ?_ ?_ ?_ -- tune cast C: result expression elaborates Nat or ℝ? set
 · intro i; refine ⟨ fun j l p=>?_,fun j l A B u=> ?_,fun j l T=>?_⟩
   · unfold w at p; split at p; next x=> exact ⟨turfed X _ _,(show zSite X j∈ V i from x.1 ▸ column_self ..), x.2⟩
     contradiction
   · dsimp only [W,Matrix.of_apply]; split; next x=> subst j; exact h.sees _ _ _ u _
     rfl
   unfold W w; simp only [Matrix.of_apply]; by_cases v:j=i; subst j; simp only [↓reduceIte,and_true,true_and]; split; exact (entry_cap X (F T) i l).trans (p T); next v=> simp [h.reaches T i l v]
   simp [v]
 · intro S; ext i j; simp [Matrix.sum_apply,W,eq_comm]
 · intro i; unfold w; simp_rw [mul_ite,mul_zero,ite_and]; suffices h: (∑ x, if H i x then rent a (V i) * k else 0) ≤ (↑(n_ang B.D):ℝ)* (taxArea r)*Real.exp (a*(taxArea r))* k from (by simpa using h); apply le_trans _ (spent i); apply sum_le_sum; intro j _; split_ifs; exact hv i; rfl -- tune metavars
 · intro i; unfold w; simp_rw [mul_ite,mul_zero,ite_and]; suffices h: (∑ x, if H x i then rent a (V x) * k else 0) ≤ (↑(n_ang B.D):ℝ)* (taxArea r)*Real.exp (a*(taxArea r))* k from (by simpa using h); apply le_trans _ (spent i); refine sum_le_sum fun j _=>?_ ; have he : H j i↔H i j:=column_sym; split_ifs <;> first | exact hv _| rfl | tauto
end YM.CF.BPress.Weave
