import YM.CF.BPress.Meadow.Season
import YM.CF.BPress.Locale.Cubus
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands
variable (X:Bands s B){x y:Site s} {i j:X.Index}{u v k r :ℕ}
abbrev town(x:Site s):=moment X (x 0)
lemma absone(x:Site s): 0 ≤ separation x x:=Nat.zero_le _
abbrev Welkin (X: Bands s B) (x:Site s): Prop:=∃ i, x∈X.band i
def citizen (x:Site s)(p:Welkin X x):=p.choose
lemma citizen_t (h:x∈ X.band i) (p:Welkin X x): citizen X x p=i:= Classical.byContradiction (fun t=> disjoint_left.mp (X.band_disjoint t) p.choose_spec h) -- tune
lemma noWel (h:¬ Welkin X x) : x∈X.gap (town X x):=by obtain ⟨i,p⟩:= X.cover x; have ht:=p.resolve_left (fun p=>h ⟨i,p⟩); rw [town,ditch_ride X i _ ((time_Zone ..).2 ht)]; exact ht
-- useful sufficiency tests
lemma corner_rank {W:Tunnel s}(p:x∈W.mem):corner W x≤W.n.val:= Tent.corner_rank W x p
lemma buriesN {k:ℕ}(p:x∈X.band i) (t:k ≤ Wealth.cloak B)(h:burial (X.mark i) x≤k): x∈halo k (X.gap (town X x)) :=by
 let W:=X.mark i; have ht:x 0=W.rise (corner W x):= Tent.corner_path W x; set n:= corner W x; have hL:n ≤ B.marked.val:=corner_rank p; let j:= town X x; have hx:town X x = if n ≤ W.cut then i-1 else i:=by unfold town; conv_lhs=> rw [ht]; exact band_time X i hL
 rw [hx]; change min n (B.marked.val-n)≤k at h
 split; next v=>
    change n≤ B.marked.val/2 at v; have h' : n≤k:=by omega
    rw [zone_of_halo]; refine ⟨X.start i,?_,?_⟩ -- placeholder
    · have heq:(X.ditch (i-1)).rise B.D=X.start i:=by change (X.ditch (i-1)).last=_; rw [X.ditch_last]; simp
      exact ⟨_,le_rfl, heq.symm⟩
    · rw [ht]; exact (delta_nat ..).trans h'
 next v=>
    change ¬ n≤ B.marked.val/2 at v; have h' : B.marked.val-n≤k:=by omega
    rw [zone_of_halo]; refine ⟨X.stop i,⟨0,Nat.zero_le _,by simp⟩,?_⟩; have he: X.stop i=x 0+↑(B.marked.val-n):=by rw [ht, Nat.cast_sub hL]; change _= X.start i+n+((B.marked.val:Per s)-(n:Per s)); unfold Bands.stop; abel
    rw [d_sym,he]; exact (delta_nat ..).trans h' -- tune
lemma death_gap (p:x∈ X.band i)(h:x∈ X.gap j): burial (X.mark i) x=0:=by
 rcases (X.at_overlap h).mp p with ⟨g,r⟩|⟨g,r⟩
 · subst j; simp [burial_rise (X.mark i) le_rfl (show x 0=(X.mark i).last from r),distanceQ]
 subst i; rw [burial_rise (X.mark (j+1)) (Nat.zero_le _) (p:= by rw [r]; simp)]; simp [distanceQ] -- tune
lemma buriesS (p:x∈X.band i) (t:r ≤ Wealth.cloak B)(h:x∈ halo r (X.gap j)): burial (X.mark i) x≤ r:=by
 have ht:= (zone_of_halo X j r x).1 h; have hu:2*r<B.marked.val:= by have he:= cloak_lt B; omega
 rcases photo_collar X j hu ht with q|⟨k,l,m,f⟩|⟨k,l,m,f⟩; · rw [death_gap X p ((time_Zone X j x).1 q)]; omega
 · unfold fall at f; have hk: x∈ X.band j:= (X.mark j).internal _|>.mpr ⟨_,Nat.sub_le ..,f⟩; rw [← citizen_t X p (p:=⟨_,hk⟩), citizen_t X hk, burial_rise (X.mark j) (Nat.sub_le ..) f]; change min (B.marked.val-k) (B.marked.val-(B.marked.val-k))≤r; omega
 have hv:k≤ (X.mark (j+1)).n.val:= by change k≤ B.marked.val; omega
 have hz:x∈ X.band (j+1):=(X.mark (j+1)).internal _|>.mpr ⟨_,hv,f⟩; rw [← citizen_t X p (p:=⟨_,hz⟩), citizen_t X hz, burial_rise _ hv f,distanceQ]; omega
lemma moment_p (t:r≤ Wealth.cloak B)(p:x∈ halo r (X.gap i)): town X x=i:=collar_ride X ((zone_of_halo ..).1 p) t
lemma moment_gap (h:x∈ X.gap i): town X x=i:= ditch_ride X i _ ((time_Zone ..).2 h)
lemma crew_eq (p:separation x y≤r)(t:x∈ halo v (X.gap i)): y∈halo (v+r) (X.gap i):=by obtain ⟨a,t,h⟩:=halo_spec.mp t; exact halo_spec.mpr ⟨a,t, (separation_triangle _ x y).trans (Nat.add_le_add h p)⟩
lemma life_m (t:x∈ X.band i)(q:y∈X.band i)(r':burial (X.mark i) x≤r)(s':r+v≤ Wealth.cloak B)(x':separation x y≤v): town X x=town X y:= (moment_p X s' (crew_eq X x' (buriesN X t (le_trans (Nat.le_add_right ..) s') r'))).symm -- tune argument t

abbrev eraBound (u:ℝ)(x:Site s): Prop:=False -- drop
-- interpolation across gaps
abbrev age(i:X.Index)(x:Site s):= let k:=corner (X.ditch i) x; if X.Dmark i then k else B.D-k
def adult(i:X.Index)(x:Site s):ℝ:= age X i x/B.D -- coer tune
lemma age_p (p:x∈X.gap i) : age X i x≤B.D:=by dsimp only [age]; split; exact corner_rank p; exact Nat.sub_le ..
lemma age_t (p:x∈X.gap i): adult X i x∈ Hotel:=⟨by unfold adult; positivity, (div_le_one (show (0:ℝ)< B.D from Nat.cast_pos.mpr B.D_pos)).mpr (Nat.cast_le.mpr (age_p X p))⟩
lemma age_time (p:x∈ X.gap i): x 0=X.depth i (age X i x):=by
 let W:=X.ditch i; simp only [age,depth]; split; exact Tent.corner_path W x; next h=> unfold Tunnel.fall; rw [X.ditch_n,Nat.sub_sub_self (show corner W x ≤ B.D from corner_rank p)]; exact Tent.corner_path W x
-- face at any x∈ both; choose D or N from mark. Bake.
lemma on_face {k:ℕ}(t:x 0=X.depth j k)(p:k ≤ B.D)(q:x∈ X.gap j): age X j x=k:= X.depth_inj (age_p X q) p ((age_time X q).symm.trans t)
lemma at_face (t:x∈X.gap j)(p:x∈ X.band i): age X j x=if i∈X.dc then 0 else B.D:=by
 obtain ⟨a,f⟩|⟨a,f⟩:=(X.at_overlap t).mp p
 · subst j; simp only [X.dc_index]; split; next h=> exact on_face X (f.trans (by rw [X.depth_zero,if_pos h])) (Nat.zero_le _) t
   next h=> exact on_face X (f.trans (by rw [X.depth_D,if_neg h])) le_rfl t
 subst i; simp only [X.dc_index, X.prev_next]; split; next h=> exact on_face X (f.trans (by rw [X.depth_zero,if_neg h])) (Nat.zero_le _) t
 next h=> exact on_face X (f.trans (by rw [X.depth_D,if_pos (not_not.mp h)])) le_rfl t

lemma age_link (l:Link s)(h:l∈inside (X.gap i)): |adult X i l.1-adult X i (endAt l)|≤(B.D:ℝ)⁻¹:=by
 have hv:(0:ℝ)<B.D:=Nat.cast_pos.mpr B.D_pos; unfold adult; rw [←sub_div, abs_div,abs_of_pos hv, ←one_div]; apply div_le_div_of_nonneg_right _ hv.le
 let W:= X.ditch i; rcases link_cases l with ⟨x,v⟩|v <;> rw [v] at h ⊢
 · simp only [age,corner,endAt,fl,event_across,event_time]; simp
 obtain ⟨k,f,q⟩:= W.normal_in _ |>.1 h; have hf: k<B.D:= f; rw [q]; let x:= Fin.tail l.1; have hu:endAt (vl (W.rise k) x)=event (W.rise (k+1)) x:=by simp [vl,endAt]; -- tune
 change |(age X _ (event _ x):ℝ)-(age X _ (endAt (vl _ x)):ℝ)|≤1; rw [hu]; simp only [age]; change |↑(if X.Dmark i then corner W (event (W.rise k) x) else B.D-corner W (event (W.rise k) x)) - (↑(if X.Dmark i then corner W (event (W.rise (k+1)) x) else B.D-corner W (event (W.rise (k+1)) x)):ℝ)| ≤ 1; rw [Tent.corner_co W x f, Tent.corner_co W x f.le]; split; next h=> push_cast; simp; -- indent
 next h=> push_cast [show k≤B.D by omega,Nat.cast_sub f]; push_cast [Nat.cast_sub hf.le, Nat.cast_sub hf]; apply abs_le.mpr; constructor <;> linarith -- tune
end YM.CF.BPress.Hazel
