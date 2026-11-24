import YM.SU5.FiniteGaugeData.ArchiveK.Rona
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSectionVars false
namespace Midway
open Violas Concert LightK Waltz
variable {n u i N J t k:ℕ}{V v c r θ:ℝ}{D:ℕ}(F:FilterK){G:E4≃ₗᵢ[ℝ] E4}(P:ZephyrG G D t)
section loans
local notation "Ω"=> glyph n
local notation "X"=> Stamp u k
local notation "Q"=> modelK P F u k
variable (H:u*k=n)
def castZ : glyph n≃Stamp u k:= Fintype.equivOfCardEq (by rw [show Fintype.card (Stamp u k)=_ from inn u k,H]; simp [glyph])
lemma castZ_pay (g:∃ U: PlansM (Stamp u k),page X ≤2*dim U ∧ ∀ x∈ U,acc (-4096) u k *‖x‖^2 ≤ gas (modelK P F u k) x) :
 let x(c:Bool)(z:glyph n):=actor P u k (castZ H z) c; let Q': Op (glyph n):=Matrix.of fun i j => stone G F (x true i) (x false j);
 ∃ U : PlansM (glyph n), page (glyph n) ≤2*dim U ∧ ∀ x∈U, perF (-4096) n *‖x‖^2 ≤ gas Q' x:= by
 intro x A; obtain ⟨U,u',b⟩:= g; let f:= (castZ H).symm; have hp:perF (-4096) n=acc (-4096) u k:=by unfold perF acc; rw [← H]; push_cast; ring_nf
 have he:∀ i j: X,A (f i) (f j)= Q i j:=by intro i j; unfold A; unfold x f; simp only [Matrix.of_apply,Equiv.apply_symm_apply]; apply sum_congr rfl (fun t h=>?_); unfold rebate axisGap; simp [add_comm]; left; congr 1; abel
 obtain ⟨t,h⟩:= blue_cost f (Q) A U _ b he; refine ⟨U.map (blue f).toLinearMap,?_,hp.symm ▸ h⟩; rw [t,show page (glyph n)= _ from Fintype.card_congr (castZ H)]; exact u' -- tune
end loans
section rad
variable {Q:ℕ}(X:MeterC J r)(x:0<Q)(he:0<r)(hc:r≤1)(V:ℝ) (g:∀ i:Genre J, 2000*X.tall D i/D ≤ V)(h:∀ p:Space3,‖p‖ ≤ V→1/2 ≤ (garnet G F p).re)
local notation "Ω"=>glyph
local notation "Zκ" n:max=> X.knot D Q n
local notation "f"=> X.scale D Q
local notation "W"=> X.tall D
include x h g he hc P
-- partnered K.Mask & ann crop. enumerate kernel price.V.Stock.
structure Twig (n:ℕ)(b:Bool)(A:Ledger P F J (X.knot D Q n) (perF (-4096) (X.knot D Q n)) r):Prop where
 bill (i:Fin J): ∀ u : Ω (Zκ n), let y:= ray X D Q n (b,i); SunK true y (A.U (i,u)) ∧ ∀ j∈F.s,SunK false y (A.V (i,u)-j)
 vista (i:Fin J): 100 < ray X D Q n (b,i)
lemma res (b: Bool) : ∀ᶠ n:ℕ in atTop,∃ A:Ledger P F J (X.knot D Q n) (perF (-4096) (X.knot D Q n)) r,Twig F P X n b A:=by
 let q(i:Fin J):ℕ→ℕ:= f (b,i); let w(i:Fin J):= W (b,i); let hd:= P.unitC; let s:= X.knotT x hd; have ht(i:Fin J):Tendsto (q i) atTop atTop:= X.scaleT x hd _; have hw(i:Fin J):0<w i:= X.big_b x hd (b,i); let r'(i:Fin J)(n:ℕ):=ray X D Q n (b,i); have he'(i:Fin J): Tendsto (r' i) atTop atTop:= RayT X x hd _
 let U'(i:Fin J):= (ht i).eventually (Horcrux F h P hd (w i) (hw i) (g (b,i))) -- remove n binder
 filter_upwards [(eventually_all.mpr U'), eventually_all.mpr (fun i=>(ht i).eventually_ge_atTop (w i ^3)), eventually_all.mpr (fun i:Fin J=> (he' i).eventually_gt_atTop 100), eventually_all.mpr (fun i=> (eventually_all_finset F.s).mpr (fun v h=> (he' i).eventually_ge_atTop (‖emitX v‖)))] with n H h₀ Wκ p
 let z:= Zκ n; let l(i:Fin J):q i n*w i=z:= X.scale_q x hd _ _
 let Y(i:Fin J × Ω z)(c:Bool):= actor P (q i.1 n) (w i.1) (castZ (l i.1) i.2) c; let Uv:= fun i:Fin J × Ω z=> Y i true; let V₀:= fun i:Fin J×Ω z=>Y i false
 have hM(i:Fin J)(v:Ω z) : SunK true (r' i n) (Uv (i,v)) ∧ ∀ j∈F.s,SunK false (r' i n) (V₀ (i,v) - j):=by
    let S:= castZ (l i) v; constructor; · have hh:= tan_S P (h₀ i) S true 0 ?_; apply sub_zero _ |>.subst (motive:=fun x=> SunK true (r' i n) x) hh; rw [emit_origin,norm_zero]; positivity
    exact fun j v=>tan_S P (h₀ i) S false j (p i j v)
 let A:Ledger P F J z (perF (-4096) z) r:= { U:=Uv, V:=V₀,pos_all:= ⟨he,hc⟩,bridge_Y j:= castZ_pay F P (l j) (H j), cloak:=fun i j v=> ?_ }; refine ⟨A,hM, Wκ⟩; -- tune order and inaccessible vars
 have heR :radix (b,i) ≠ radix (b,j):= radix_in.ne (fun e=> v (Prod.mk.inj e).2); -- tune
 rcases lt_or_gt_of_ne heR with g|g; · refine Or.inl fun z v a t=>?_ ; exact RiverR he (hM i z).1 ((hM j v).2 a t) (by linarith only [Wκ i]) (pricing X x (b,i) (b,j) g hd) (Wκ i)
 exact Or.inr (fun z v a t=> RiverR he ((hM j v).2 a t) (hM i z).1 (lt_trans (by norm_num: (0:ℝ)<100) (Wκ j)) (pricing X x _ _ g hd) (Wκ j))
omit h g
open Ledger
variable {b:Bool}(A:Ledger P F J (X.knot D Q n) (perF (-4096) (X.knot D Q n)) r)(T:Twig F P X n b A)
local notation "L"=> Lft F P b A
local notation "R"=> Rht F P b A
-- separate redshift.Flanks ℝ≥Lℓ.NonOverlap.Precursor. Horizon ready. Later lift crop & Purchase.
include T
lemma Twig.Gai (i:Cover)(g:i∈ Lft F P b A): ∃ j:Fin J, SunK b (ray X D Q n (b,j)) i:=by
 obtain ⟨⟨x,y⟩,l,rfl⟩:= mem_image.mp g; exact ⟨x,((T.bill x y).1).stirke b⟩ -- include h x
lemma Twig.Bai (i:Cover)(g:i∈ Rht F P b A): ∃ j:Fin J, SunK (!b) (ray X D Q n (b,j)) i:=by
 obtain ⟨⟨x,y⟩,l,g⟩:= mem_biUnion.mp g; obtain ⟨z,v,rfl⟩:= mem_image.mp g; exact ⟨x,SunK.stit b (((T.bill x y).2) z v)⟩ -- tune
omit T
lemma Rune_cut(i:Genre J){x':Cover}{b:Bool}(v:SunK b (ray X D Q n i) x') : x'∈ box (X.knot D Q n) := by
 have ht:= ext_pay X x P.unitC i (n:=n); by_contra! w; have hx:=hinder _ _ w; have hz:0≤ (X.knot D Q n:ℝ):=Nat.cast_nonneg _
 nlinarith only [ht,hx,v.roof,mul_le_mul_of_nonneg_right hc hz,hz]
lemma Tourney(i:Genre J){x':Cover}{b:Bool}(v:SunK b (ray X D Q n i) x')(p:100< ray X D Q n i):∀ y:Cover,y∉ box (Zκ n)→ River r (emitX y) (emitX x'):=by
 intro y t; have ht:= ext_pay X x P.unitC i (n:=n); have hx:=hinder _ _ t; let z:ℝ:=X.knot D Q n; have he':0≤ z:=Nat.cast_nonneg _; refine ⟨?_,?_⟩ <;> nlinarith only [ht,p,hx, v.roof,mul_le_mul_of_nonneg_right hc he',mul_le_mul_of_nonneg_left hx.le he.le,he']
include A T
lemma Twig.estate : Lft F P b A⊆ box (X.knot D Q n) ∧ Rht F P b A⊆ box (X.knot D Q n)∧∀ x:Cover,x∉ box (X.knot D Q n) → ∀ v∈ Rht F P b A,River r (emitX x) (emitX v) := by
 constructor; · intro v e; obtain ⟨j,t⟩:= Twig.Gai F P X x he hc A T v e; exact Rune_cut P X x he hc (b,j) t
 constructor; · intro v e; obtain ⟨j,t⟩:=Twig.Bai F P X x he hc A T v e; exact Rune_cut P X x he hc (b,j) t
 intro y t v H; obtain ⟨j,v⟩:= Twig.Bai F P X x he hc A T v H; exact Tourney P X x he hc _ v (T.vista j) y t
lemma Twigs_apart {B:Ledger P F J (X.knot D Q n) (perF (-4096) (X.knot D Q n)) r}(e:Twig F P X n (!b) B) : Disjoint (Lft F P b A) (Rht F P (!b) B):= by
 apply Finset.disjoint_left.mpr; intro i u t; obtain ⟨j,l⟩:= Twig.Gai F P X x he hc A T i u; obtain ⟨k,w⟩:=Twig.Bai F P X x he hc B e i t; let X1:=T.vista j; let X2:= e.vista k; have ht:= radix_in.ne (show (b,j) ≠ (!b,k) from ?_); swap; · cases b <;> simp
 rcases lt_or_gt_of_ne ht with u|u; · exact (apartK he l w (lt_trans (by norm_num) X1) (pricing X x _ _ u P.unitC) hc) rfl
 exact (apartK he w l (lt_trans (by norm_num) X2) (pricing X x _ _ u P.unitC) hc) rfl
-- lane lower extraction in integer sr≥ ℓ bound condition.t.
def Land (b:Bool) (n:ℕ)(T: Finset Cover): Prop:= ∀ x∈T,∀ i:Axis, (n:ℤ)≤ if b then x i else -x i
lemma Twig.Lanes(L':ℕ) (WQ:∀ i:Genre J, L'≤ ray X D Q n i) : Land b L' (Lft F P b A)∧ Land (!b) L' (Rht F P b A):= by
 have hh {o:Genre J}{b:Bool}{x:Cover}(t:SunK b (ray X D Q n o) x)(a:Axis): (L':ℤ)≤ if b then x a else -x a:=by have he: (L':ℝ) ≤ LaneR b a (emitX x):= (WQ o).trans (t.fence a); cases b <;> unfold LaneR at he <;> simp only [Bool.false_eq_true,↓reduceIte,emit_axis] at * <;> exact_mod_cast he
 constructor<;> intro i t; obtain ⟨j,u⟩:=Twig.Gai F P X x he hc A T i t
 exact hh u
 obtain ⟨j,u⟩:= Twig.Bai F P X x he hc A T i t
 exact hh u
-- count
lemma Twig.bank : (Lft F P b A).card≤ J*(Zκ n)^3 := le_trans card_image_le (by rw [card_univ,Fintype.card_prod]; simp [glyph])
end rad
#print axioms res
#print axioms Twig.estate
end Midway
end YM.CF.Window.ArchiveK
