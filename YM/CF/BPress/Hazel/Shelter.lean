import YM.CF.BPress.Hazel.Stitch
import YM.CF.BPress.Hazel.Reserve
import YM.CF.Skye.Pine
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {B:BandWidth}
open RG Filter Pressure Weave Port Letters Letter Grid Wealth Locale Tunnel Bands Branch Clipγ Skye
variable {N: Side}{X:Bands (More N) B}{T: BPress.Sheet.Atlas}{Lf C C' y:ℝ}{a:ℕ}{A L D κ η:ℝ}{F:Net (More N) T Lf y C C' a}{R:Hangar (More N)}{K:Fare X}
variable {U:Micro (More N)}{W:Rental}{S:Seal X.Hcols}{v:Quarters X} {w:X.Slates}
namespace Reserve
variable {P:Weave.Budget}(Z:Reserve X K S v w U y κ T) (t:Plenty T P B D κ η A y)(sK:Summer X K P.upper (P.low y) (P.reach y) (P.chunks y)) (u:P.reach y≤ R.L.val) 
variable {r:ℕ}{e d g h:ℝ}{Y:Orbit N→ Pane N}(f:Dusk B R W)(V: Roof N e d r Y) (uV:temp y≤e) (dP:r+6≤ W.U)(k:Lost y X (field X F K S v w U))
local notation "X₁" => field X F K S v w U
local notation "S₁" => bawl X R y S (Prod.fst v)
include Z t sK u k
lemma flags_early (a: Site (More N))(h:a∈ flags (temp y) X₁) : ∃ i:X.Index, a∈X.gap i∧∃ b:Tri (More N), delta (Fin.tail a) b≤4 ∧ (i,b)∈ S:=by
 have he:= Z.mission t sK u (F:=F); have ht:= sign_result he Z.u t.grant k _ h; simpa only [show chosen X κ y (centerSky X K S v y)=S from Z.eye] using ht -- tune
include f dP
lemma stormB {p q: Site (More N)}(h:p∈flags (temp y) X₁)(t':separation p q ≤r+1) : NearBlock X W.U q ∧ Near X R S₁ 1 q:=by
 obtain ⟨i,hp,b,z,h⟩:= flags_early Z t sK u k _ h; have ht: q∈ halo W.U (X.gap i):=halo_spec.mpr ⟨p,hp,(t'.trans (by omega))⟩; have he:= moment_p X (W.um.trans (f.summer.trans halfway)) ht; have hv: delta b (Fin.tail q)≤R.L.val:=by apply (delta_triangle _ (Fin.tail p) _).trans; refine (Nat.add_le_add ((delta_comm ..).le.trans z) ((tail_sep ..).trans t')).trans ?_; have he:=W.um.trans f.yieldr; omega
 refine ⟨near_gap ht, own X R (i,b),hurt_m (i:=(i,b)) (Or.inl h),he, tang_rad R _ _ hv⟩ -- tune existential notation
include uV
lemma unsafe_re (l:Link (More N))(h:¬Disjoint (flags e X₁) (win r l)) : let U':= Danger X R W S₁; l.1∈U' ∧ endAt l∈ U':=by
 obtain ⟨i,q,u0⟩:= not_disjoint_iff.mp h; have hp:i∈ flags (temp y) X₁:=by obtain ⟨a,x,w⟩:=flags_spec ..|>.1 q; exact (flags_spec ..).2 ⟨a,x,uV.trans_lt w⟩
 have hc(x)(p:x∈ends l):x∈ Danger X R W S₁:=by
    obtain ⟨j,ju,b⟩:=halo_spec.mp u0; have ht: separation j x≤1:= by rcases mem_insert.mp ju with h|h <;> rcases mem_insert.mp p with k|k <;> (try simp only [mem_singleton] at *) <;> subst j x <;> first| (solve|simp)| exact Lat.oneTouch ..| exact le_trans (Eq.le (separation_comm ..)) (Lat.oneTouch ..)
    have f:= stormB Z t sK u f dP k hp (le_trans (separation_triangle i j x) (add_le_add ((separation_comm ..).le.trans b) ht)); exact mem_filter.mpr ⟨mem_univ _,f.1,local_m f.2 (by norm_num)⟩
 exact ⟨hc _ (by simp),hc _ (by simp [endAt])⟩ -- tune orientation names
include V
lemma stays (v':Ids N)(i:Link (More N))(p:i∈inside (safe X R W S₁)) : Y (X₁,v') i = X₁ i:= V.lamp _ _ _ (Classical.byContradiction fun h=> (mem_compl.mp ((inside_iff ..).1 p).1) (unsafe_re Z t sK u f uV dP k _ h).1)

-- Mark progress and heat. no new requirement on d,Y. op prechoices separate. valid every input.
lemma shelter (m:Tiling (More N))(v':Ids N)(q:∀ i:X.Index, let p':= knot (T:=T) (y:=y) X w X₁ i; F.takeN X X₁ i p' ≠0→ (i∉X.dc→p'∈ T.pairs y ((X.mark i).reads X₁)) → Grains (X.band i) X₁ ((PortLetter X F K S v w U m).plant i) ((PortLetter X F K S v w U m).brush i) g h): Grip X W R S₁ (PortLetter X F K S v w U m) (Y (X₁,v')) g h (price_p A η y):=by
 let X':= PortLetter X F K S v w U m; have hx:= t.grant.young; have ht:=price_p A η y; have he: A*(heigh y)⁻¹^2≤ price_p A η y:=le_add_of_nonneg_left (add_nonneg (temp_pos hx).le (mul_nonneg t.grant.posC.le (aA_positive hx).le)); refine ⟨Letters.bottle X F m w _ (F.roll_hold X w _ _),f,(mul_nonneg t.desires (sq_nonneg _)).trans he,fun x f=> (Z.park t sK u m (F:=F) f).trans he, fun i x p r vv=>?_ , Z.steady t sK u F,fun i=> ?_ ⟩ -- tune F δ
 · rw [stays Z t sK u f V uV dP k v' _ r]; exact Z.gold t sK u p vv
 let Mx:=knot (T:=T) (y:=y) X w X₁ i; have hr: Grains (X.band i) X₁ (X'.plant i) (X'.brush i) g h:= q i (by exact ((F.play_ne X w (x:=X.atmospheric (centerSky X K S v y)) (xi_pos hx) t.Xi (fun i _=> Z.u i) i)).ne') (fun p=> Z.permitted i p); let p:=Y (X₁,v'); refine ⟨fun i t=>?_ ,fun x u i t=>?_⟩ -- rename tunes
 · unfold urgent; rw [stays Z ‹_› sK u f V uV dP k v' i (inside_cov inter_subset_right t)]; exact hr.grow _ (inside_cov inter_subset_left t)
 unfold fare; rw [stays Z ‹_› sK ‹P.reach y≤ R.L.val› f V uV dP k v' i (inside_cov inter_subset_right t)]; exact hr.timing x u _ (inside_cov inter_subset_left t)
end Reserve
end YM.CF.BPress.Hazel
