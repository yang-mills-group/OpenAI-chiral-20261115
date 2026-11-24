import YM.SU5.Diva.SPF
/-! Adaptation of Fluxion,Audition,Duet. Testing ALL clans, same enrollment.
 Two tolerance orders: take R large first. The internal evaluation estimate
 is on the true spin/color/momentum form, invoked on auxiliarily-chosen sequences
 (does not need a continuum limit for these volumes). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{j:ℕ}
open Py.Rate.LocalLimit.Papal (Weaver)
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
namespace Twah
open Lead (Clan)
open YM.Stationary (Gaia)
open Lamour.Bridge
variable {b n w p:ℕ} {I:Type*} (Y:I→Twah)
-- admitted UV compound labels finite:
def apron (b:ℕ)(T:Twah):Prop:= T.birth∈box b∧ T.death∈box b∧ T.traceV.length ≤32*b
private def Bucket (b:ℕ) := {T:Twah//apron b T}
instance (b) : Finite (Bucket b):= by
 classical
 letI:Finite Lattice.Step:=Finite.of_injective (fun i:Lattice.Step=>(i.dir,i.neg)) (by rintro ⟨a,x⟩ ⟨b,y⟩ h; simpa using h)
 let W:= {x :Walk| x.length ≤32*b}
 haveI :Finite W:= (List.finite_length_le Lattice.Step (32*b)).to_subtype
 let f(B:Bucket b):((box b) × (box b))×DirSpin×W:= ((⟨B.val.birth,(show _ from B.property.1)⟩,⟨B.val.death,B.property.2.1⟩),actualSpin B.val,⟨B.val.traceV,B.property.2.2⟩)
 apply Finite.of_injective f; rintro ⟨⟨a,d,u,v,V,h⟩,t⟩ ⟨⟨a',d',u',v',V',h'⟩,t'⟩ he; simp only [f,Prod.mk.injEq,Subtype.mk.injEq, actualSpin] at he; obtain ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩,rfl⟩:= he; rfl
-- budgets. the margin allowed in props is in *fermion spacings at this observed level divided by R*! for comparing with measured cap grain via higher-level work later.
abbrev Lid (p:ℕ):ℝ:=(p:ℝ)+1
abbrev keyV(p:ℕ):ℝ:=(Lid p)⁻¹
def Outfit (p R:ℕ)(F:I→Twah): Prop:= Spill F (Lid p) (keyV p) R ∧ ∀ v, apron ((p+2)*R) (F v)
variable (p R w :ℕ)
abbrev Alphabet:= {A:Fin w→Twah//Outfit p R A}
instance : Finite (Alphabet p R w):= by
 let f(x:Alphabet p R w): Fin w→Bucket ((p+2)*R):=fun i=> ⟨x.val i,x.property.2 i⟩; exact Finite.of_injective f (fun x y h=> Subtype.ext (funext (fun i=> congrArg (fun z: Bucket ((p+2)*R)=> z.val) (congrFun h i))))
instance : Fintype (Alphabet p R w):= Fintype.ofFinite _
abbrev Parts := Σ (w:Fin (p+1)),(Alphabet p R w.val) × (Fin w.val→ Clan) -- includes val 0
abbrev letters (w:ℕ) := List.finRange w
namespace Parts
variable {p R} (S: Parts p R)
def craft : Weaver:= plait S.2.1.val S.2.2 (letters _) R
def sites := paper ((letters _).map S.2.1.val)
def depiction := Twah.witness S.2.2 (letters _) (nearPoints R S.2.1.val) (bodyF S.2.1.val)
lemma song: YM.CF.Lamour.Bridge.Celeste.Voice S.craft S.sites:= lovely ..
end Parts
lemma aroused (ε:ℝ)(t:0<ε) : ∀ᶠ R:ℕ in atTop,∀ x:Parts p R, Clarity (Py.Rate.LocalLimit.Papal.meanF x.craft x.depiction) 4 ε:=by
 have ht:= Filter.eventually_all.mpr (fun w:Fin (p+1)=> Filter.eventually_all.mpr (fun v:Fin w.val→ Clan => Filter.eventually_all.mpr (fun q:Fin w.val→ DirSpin=> aroma (u:= keyV p) 4 v (letters _) q (by decide) ε (by unfold keyV Lid; positivity) (Lid p) t)))
 exact ht.mono (fun R h x=> h x.1 x.2.2 (bodyF x.2.1.val) x.2.1.val x.2.1.property.1 rfl)
theorem keyV_positive :0<keyV p:=by unfold keyV Lid; positivity
theorem keyV_go : Tendsto keyV atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
variable {p R w} [Fintype I] (B:I→Twah)(s:ℕ→ℕ) -- tag astronomy
-- reaching blanket statement for *every real point & overlap locus*. First any arrays with bounded length, coordinates converge with rigid intersections no splitting at equal. Then provide construction.
variable {Y} (D:Cellz I→Gaia)(A:ℕ→I→Twah)(u:riseUp A s D) (v:plateau A D)(h:StrictMono s)
include u v
lemma spill_ticket :∀ᶠ n in atTop, Spill (A n) (Lid n) (keyV n) (s n):=by
 let g(n:ℕ):= nearPoints (s n) (A n); have hp(i:Cellz I): ∀ᶠ n in atTop, dist (g n i) 0 ≤ Lid n:=by
    filter_upwards [(u i).norm.eventually (ge_mem_nhds (show ‖D i‖ < ‖D i‖ + 1 from lt_add_one _)), tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖D i‖] with n e hx; rw [dist_zero_right]; exact e.trans (add_le_add_left hx _)
 have he(i j: Cellz I):∀ᶠ n:ℕ in atTop, sitesX (A n) i ≠ sitesX (A n) j→ keyV n ≤ dist (g n i) (g n j):=by
   by_cases hz:D i=D j
   · filter_upwards [v i j hz] with n h p; exact False.elim (p h)
   exact (keyV_go.eventually_lt ((u i).dist (u j)) (dist_pos.mpr hz)).mono fun i h _=> h.le
 exact (Filter.Eventually.and (Filter.eventually_all.mpr hp) (Filter.eventually_all.mpr (fun i=> Filter.eventually_all.mpr (he i)))) -- type notation
omit v
lemma horizon (i:Cellz I) (v:0 < R) (p: dist (nearPoints R Y i) 0 ≤ Lid n): sitesX Y i∈box ((n+2)*R):=by
 let x:= sitesX Y i; let B:= nearPoints R Y i; have he(j): ‖(B j:ℝ)‖ ≤ Lid n:= (PiLp.norm_apply_le B j).trans (by rwa [dist_zero_right] at p) -- lemma name
 have hh:0<(R:ℝ):=by exact_mod_cast v
 have hx(j): -(((n+2)*R:ℕ):ℤ) ≤ x j ∧ x j ≤ ((n+2)*R:ℕ):=by
    specialize he j; rw [Real.norm_eq_abs] at he; change |_ / (R:ℝ)| ≤ _ at he; obtain ⟨hL,hX⟩:= abs_le.mp he; unfold Lid at hX hL;
    constructor
    · apply (Int.cast_le (R:=ℝ)).mp; push_cast; nlinarith only [hh,(le_div_iff₀ hh).mp hL]
    apply (Int.cast_le (R:=ℝ)).mp; push_cast; nlinarith only [hh,(div_le_iff₀ hh).mp hX]
 exact box_test.mpr ⟨fun i=>(hx i).1,fun i=>(hx i).2⟩
include h v
lemma cape_given (p:∀ᶠ n in atTop,∀ i, (A n i).traceV.length ≤ 32*((n+2)*s n)): ∀ᶠ n in atTop, Outfit n (s n) (A n) := by
 filter_upwards [spill_ticket s D A u v, p,h.tendsto_atTop.eventually_gt_atTop 0] with n w p hr; exact ⟨w,fun i=> ⟨horizon s D A u (Y:=A n) (i,false) hr (w.1 _),horizon s D A u (Y:=A n) (i,true) hr (w.1 _),p i⟩⟩
omit h u v
-- theorem actually restrict path length approx support; using physical spacing ×2 and R. Any order allowed.
def placeF(x y:Cover)(c:DirSpin)(k:Lattice.Order):Twah:= ⟨x,y,c.1,c.2,Lattice.route (nodeC x) (nodeC y) k,Lattice.route_end ..⟩
private lemma routeLengthF(x y:Cover)(a b:Fin 2)(k:Lattice.Order)(n:ℕ)(h:x∈box n)(ht:y∈box n): (placeF x y (a,b) k).traceV.length ≤ 32*n:=by
 apply (Cube.route_size _ _ k (4*n) (fun i=>?_)).trans; · omega
 obtain ⟨hv,H⟩:= box_test.mp h; obtain ⟨hu,S⟩:= box_test.mp ht; let N:ℤ:=n; specialize H i; specialize hv i; specialize S i; specialize hu i; change ((nodeC y i - nodeC x i):ℤ).natAbs ≤ _; simp [nodeC]; omega
-- round to nearest integer below.
abbrev discrete (r:ℕ)(x:Gaia):Cover:=fun i=> ⌊(r:ℝ)*x i⌋
def homestead (s:ℕ) (i:I)(W:I→DirSpin):= placeF (discrete s (D (i,false))) (discrete s (D (i,true))) (W i) 1
-- actual includes duplicates at indices; preserve
lemma installed_home (W:I→DirSpin)(n:ℕ)(i:Cellz I): sitesX (fun i=>homestead D n i W) i=discrete n (D i):=by rcases i with ⟨i,b⟩; cases b <;> rfl
include h
lemma riseHome (W:I→DirSpin): riseUp (fun n i=> homestead D (s n) i W) s D:= by
 intro i; let Lx (n:ℕ):Gaia:=nearPoints (s n) (fun i=> homestead D (s n) i W) i; have ht:= tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp h.tendsto_atTop
 let y(n):ℝ:=s n; have hT(i):∀ᶠ n in atTop, ⌊y n *(D i 0:ℝ)⌋ ≤ y n* (D i 0:ℝ):=by filter_upwards with k using Int.floor_le _ -- remove
 have he(a:Axis): Tendsto (fun n=> Lx n a) atTop (𝓝 (D i a)) := by
    let b:= D i a; let Z(x:ℕ):= b- (y x)⁻¹; have hq:Tendsto Z atTop (𝓝 b):=by simpa only [Z, Function.comp_apply, sub_zero,y] using (tendsto_const_nhds (x:=b)).sub (tendsto_inv_atTop_zero (𝕜:=ℝ)|>.comp ht)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hq (tendsto_const_nhds (x:=b))
    · filter_upwards [ht.eventually_gt_atTop 0] with k u; change 0< y k at u; change b - (y k)⁻¹ ≤ (sitesX (fun i=>homestead D (s k) i W) i a:ℝ)/(y k); rw [installed_home]; apply (le_div_iff₀ u).2; rw [sub_mul,inv_mul_cancel₀ u.ne']; linarith only [Int.sub_one_lt_floor (y k*b)]
    filter_upwards [ht.eventually_gt_atTop 0] with k u; change (sitesX (fun i=>homestead D (s k) i W) i a:ℝ)/ y k ≤ b; rw [installed_home]; exact (div_le_iff₀ u).2 ((Int.floor_le _).trans_eq (mul_comm ..))
 exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr he)
omit h
lemma homeHave (W:I→DirSpin): plateau (fun n i=> homestead D (s n) i W) D:=by
 intro x y p; filter_upwards with k; exact (installed_home ..).trans ((congrArg (discrete (s k)) p).trans (installed_home ..).symm)
include h
theorem cottage (W:I→DirSpin):∀ᶠ n in atTop, Outfit n (s n) (fun i=> homestead D (s n) i W):=by
 let A (n) (i:I):=homestead D (s n) i W; have he:=riseHome s D h W; have hx:=homeHave s D W; apply cape_given s D A he hx h
 filter_upwards [spill_ticket s D A he hx,h.tendsto_atTop.eventually_gt_atTop 0] with n p q i; let g(j):=horizon (n:=n) s D A he j q (p.1 j); exact routeLengthF _ _ _ _ _ _ (g (i,false)) (g (i,true)) -- tuple eta
end Twah
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Twah.cottage
