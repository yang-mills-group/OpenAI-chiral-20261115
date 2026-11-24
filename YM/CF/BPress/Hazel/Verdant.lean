import YM.CF.BPress.Hazel.Taper
import YM.CF.BPress.Spin.Entry
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch Clipγ Letter
abbrev rangP := Music.bought.choose
lemma capZ : 0<rangP ∧ rangP <1 ∧ ∀(k:Fin 5){v:ℝ},v∈Hotel→ ‖tap k v-till k‖≤ rangP:=by have he:=Music.bought.choose_spec; exact ⟨he.1,he.2.1,fun k {v} x=> he.2.2 k v x⟩
variable {X:Bands s B}{W:Rental}{R:Hangar s}{A:Letter X}{S:Seal (SiteX X R)}{U: Micro s}{K:Tiling s}{g h l c m:ℝ}
variable {p:Grip X W R S A U g h c}(t:Stopped A K p l m) {x y:Site s}
-- parameter derivative $C^1$ for pieces; don't require those Holder path in argument $U$.
def primeC (f:ℝ→Paint s)(v:ℝ) (i: Site s): Op Slot := deriv (fun v=> f v i) v
lemma dprimeC (f:ℝ→Paint s)(h:∀ x:Site s, ContDiff ℝ ∞ (fun t=> f t x)) (t:ℝ): HasDerivAt f (primeC f t) t:=hasDerivAt_pi.mpr (fun i=> ((h i).differentiable (by norm_num) t).hasDerivAt)
lemma dconC (f:ℝ→Paint s)(h:∀ x:Site s, ContDiff ℝ ∞ (fun t=> f t x)): Continuous (primeC f):= continuous_pi fun i=>(h i).continuous_deriv (by norm_num)
lemma pegged (f:ℝ→Paint s)(p:∀ x:Site s, LipschitzOnWith priceTone (fun t=> f t x) Meadow.active) (x:Site s) (u:ℝ)(h:u∈ Set.Icc (0:ℝ) 2) : ‖primeC f u x‖≤ priceTone:= norm_deriv_le_of_lipschitzOn (Icc_mem_nhds (lt_of_lt_of_le (by norm_num) h.1) (lt_of_le_of_lt h.2 (by norm_num))) (p x) -- possible scop
include t
namespace Stopped
local notation "C" => Kactual W R S A K U
-- Pref collar geometry
lemma patch (f:¬ Welkin X x)(u: Good X R S 4 (panel X x))(v: separation x y≤ W.P+1):
     y∈ halo (W.P+1) (X.gap (town X x)) ∧ y∈safe X R W S ∧ Good X R S 3 (panel X y)∧ A.color x=A.color y:=by
 let q:=p.power; let k:=W.P+1; set i:= town X x; have he:x∈ halo 0 (X.gap (town X x)):=halo_subset _ _ (noWel X f) -- tune
 obtain ⟨g',t,v'⟩:= packet p.power (touched_s.mpr (fun _=>good_m u (by norm_num))) he (Nat.zero_le _) v u (by have hy:=W.pu.trans W.um; omega); rw [zero_add] at g'; have hk:= W.pu.trans W.um; refine ⟨g',t,v', carriedP p.settle (good_m u (by norm_num)) ?_ ((tail_sep ..).trans (v.trans (hk.trans p.power.yieldr)))⟩; exact (moment_p X (hk.trans (p.power.summer.trans halfway)) g').symm
-- capsule on any micro site; give path set, radius vs till, and anchor near B. Keep $μH` cost for comparison.
lemma venue (f:¬ Welkin X x)(g': Good X R S 4 (panel X x))(v: separation x y≤ W.P+1): let z:=A.color x; (‖C 1 y-Music.basis‖≤ μH*c) ∧ ∀ u:ℝ,1≤u → ∃ a∈Hotel, ‖C u y-tap z a‖ ≤ μH*c:=by
 intro z; obtain ⟨a,b,b',v⟩:= t.patch f g' v; simp_rw [(t.groomed (good_retained p.power y b')).2]; rw [show z=A.color y from v]; let e:= μH*c; have he:0≤e:= mul_nonneg (mul_nonneg (by norm_num) sphereRate_cost.positive.le) p.credit
 by_cases q: Welkin X y; swap; · let T:= zoneD (X:=X) y; have ht:T∈Hotel:= age_t X (noWel X q); simp_rw [Hmiss W A q]; rw [edge_1 _ ht]; refine ⟨by simpa using he,fun i u=>?_⟩; rw [pathII _ ht u]; have h0:= mid_bound T; have h1:= mid_bound (i-1); exact ⟨_,⟨mul_nonneg h0.1 h1.1,mul_le_one₀ h0.2 h1.1 h1.2⟩,by simpa using he⟩ -- tune name
 obtain ⟨i,v⟩:=q; by_cases k:i∈ X.dc
 · simp_rw [Hclan0 W A p.tint v k]; rw [al1,shape_cost.tail]; refine ⟨by simpa using he,fun t u=> ⟨0,H0,?_⟩⟩; rw [alpha_final (show 1/2≤t from le_trans (by norm_num) u),shape_cost.tail]; simpa only [open_t,sub_self,norm_zero] using he
 let w:=W.P+1; have hL:w ≤ W.M:= W.pu.trans W.um; have hx:= buriesS X v (hL.trans (p.power.summer.trans halfway)) a; have hz:= (hL.trans p.power.summer); have q:= Amendment A W (A.color y) p.tint v k (hx.trans hz) rfl (p.nSeat _ (good_m b' (by norm_num))); rw [Clipγ.dark ((Nat.mul_le_mul_right 8 hx).trans W.obscured)] at q; simp_rw [neon_face] at q; refine ⟨(edge_1 (A.color y) H1 ▸ q 1),fun u h=>?_⟩; exact ⟨_,mid_bound _,edge_upper (A.color y) h ▸ q u⟩ -- tune rw at dep binder gamma possible
end Stopped
-- Spin.Looks. prefix.
section ferm
variable {N:Side}{X:Bands (More N) B}{W:Rental}{A:Letter X}{R:Hangar (More N)}{S:Seal (SiteX X R)}{U:Micro (More N)}{K:Tiling (More N)}{p:Grip X W R S A U g h c}(Y:Stopped A K p l m)
omit t
include Y
variable {σ δ τ :ℝ}
abbrev zoneμ := Set.Icc (0:ℝ) 2
theorem shake (x:c≤δ)(a:μH*c≤δ)(z:μH*c+rangP≤τ)(w:3 ≤ σ) : let P:= Picks X R S; let T:= Kactual W R S A K U; Looks U P T (primeC T) W.P τ σ m δ:=by
 intro P T; let K:= More N; let L:= Hole.wings P; let u:=Y.on_torus; let B(x:Site N):= panel X (node x); let c'(x:Site N):=A.z (B x); have ht (x: Site (More N)) (v:x∈L) :¬ Welkin X x∧ Good X R S 6 (panel X x):=by obtain ⟨xx,vy,kx⟩:= mem_image.mp v; rw [← kx]; exact (mem_filter.mp (show xx∈P from vy)).2
 refine ⟨?_,fun v _ => Y.Kplan v,fun v t x iX=> Y.Kmark (x,iX) v ⟨t.1.trans' (by norm_num), t.2.trans (by norm_num)⟩,?_,fun v t x i=>?_ ,fun u _=> dprimeC T Y.Ksmooth u,(dconC T Y.Ksmooth).continuousOn⟩ -- tune
 · intro i v u; obtain ⟨x',v',a'⟩:=halo_spec.mp (show i.1∈_ from v); let j:= town X x'; let z:=i.1; have hp:=ht _ v'; obtain ⟨p',t',a,tz⟩:= Y.patch hp.1 (good_m hp.2 (by norm_num)) (a'.trans (Nat.le_succ _)); obtain ⟨y,k,_,z₀⟩:=Y.patch hp.1 (good_m hp.2 (by norm_num)) (show separation x' (endAt i)≤W.P+1 from (separation_triangle _ i.1 _).trans (Nat.add_le_add a' (Lat.oneTouch ..))); refine (p.uSeat i j (inside_cov (Corona.halo_mono (W.pu.trans (W.um.trans (p.power.summer.trans halfway))) le_rfl) ((inside_iff ..).mpr ⟨p',y⟩)) ((inside_iff ..).mpr ⟨t',k⟩) (good_m a (by norm_num))).trans x
 · refine ⟨Music.basis, le_trans ?_ w, ?_⟩; rw [norm_κ _ basis_acts]; norm_num; intro v h; obtain ⟨k,l,f⟩:=halo_spec.mp h; obtain ⟨t,u⟩:=ht k l; exact ((Y.venue t (good_m u (by norm_num)) (f.trans (Nat.le_succ _))).1).trans a -- careful ; norm_num parser tactic
 obtain ⟨x',u⟩:= ht x i; refine ⟨till (A.color x),(till_norm ..).trans w,fun y _ h'=>?_⟩; obtain ⟨a,h,p'⟩:=(Y.venue x' (good_m u (by norm_num)) (h'.trans (Nat.le_succ _))).2 v t.1; exact (norm_sub_le_norm_sub_add_norm_sub _ (tap (A.color x) a) _).trans ((add_le_add p' (capZ.2.2 _ h)).trans z)
end ferm
end YM.CF.BPress.Hazel
