import YM.CF.BPress.Bias.Sails
import YM.CF.BPress.Locale.Depth
/-! Concrete micro taper. Needs MARK widths after operation budget; evenness not needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Laurent Bloch Next.Free Cube Fir Lat Spin Paint Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial Eye Pf Branch Grid Wealth Locale Bands Mag Tunnel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N: Side} {j:ℕ} {M:Jill.Male} {F C:Op (Single N)} (Z:Paint (More N)) {B:BandWidth} (X:Bands (More N) B)
def nodeT {N:Side}(u:Per N): Per (More N):=node (event u 0) 0
@[simp] lemma nodeT_v (u:Per N) : (nodeT u).val=2*u.val+1:=RP.val_node .. -- tune
lemma node_κ(x:Site N)(i:Axis):node x i=nodeT (x i):= ZMod.val_injective _ (by rw [nodeT_v,RP.val_node])
lemma nodeT_κ(u:Per N)(n:ℕ): nodeT (u+(n:Per N)) = nodeT u+(↑(2*n):Per (More N)):=by
 induction n with
 | zero=> simp
 | succ n ih=>
   have he(x:Per N): nodeT (x+1)=nodeT x+2:=by
      unfold nodeT; rw [← event_up,after]; simp only [Pi.add_apply,step_apply,ite_true]; ring
   rw [step_time,he, ih,add_assoc, mul_add,Nat.cast_add,mul_one, Nat.cast_ofNat] -- tune
lemma find_node(u:Per (More N)) : ∃ (i:Per N)(b:ℕ), b≤1 ∧ u=nodeT i+(b:Per (More N)):=by
 by_cases h:u.val=0; swap
 · let t:=u.val-1; let k:= t/2; let a:=2*k+1; have hu: (More N).val=N.val*2:= rfl; have ht:= ZMod.val_lt u; have he:a≤u.val∧u.val≤a+1:=by unfold a k; unfold t; omega
   have hp:k<N.val:=by unfold k t; omega
   let i:Per N:=k; have hi:i.val=k:= ZMod.val_natCast_of_lt hp
   refine ⟨i,u.val-a,by omega,?_⟩; nth_rw 1 [← ZMod.natCast_zmod_val (nodeT i)] -- tune occurrence
   rw [nodeT_v,hi,← Nat.cast_add, show 2*k+1+(u.val-a)=u.val by unfold a at *; omega,ZMod.natCast_zmod_val]
 let k:=N.val-1; have hp:0<N.val:=N.property; let i:Per N:=k; have hi:i.val=k:= ZMod.val_natCast_of_lt (by dsimp only [k]; omega)
 refine ⟨i,1,by decide,?_⟩; rw [← ZMod.natCast_zmod_val (nodeT i),nodeT_v,hi,←Nat.cast_add, show 2*k+1+1=(More N).val by rw [natM]; unfold k; omega, ZMod.natCast_self]; rwa [ZMod.val_eq_zero] at h
-- actual time bands
abbrev burn (i:X.Index) (u:Per N): Prop:= event (nodeT u) 0∈ X.band i
lemma marking (i:X.Index)(x:Site N) : node x∈X.band i ↔ burn X i (x 0):=by rw [burn,Bands.band, arc_mem]; rw [arc_mem,node_κ, event_time] -- tune
abbrev vacant0:= (univ:Finset (Per N)).filter fun u=>∀ i:X.Index,¬burn X i u
lemma vacant_t(x:Site N):x∈Lower (vacant0 X) ↔ ∀ i:X.Index,node x∉X.band i:=by simp [Lower,vacant0,marking]
lemma vacant_dark : Dark X (Lower (vacant0 X)):= ⟨fun x h => (vacant_t X x).mp h⟩
lemma burn_out {u:Per N}(i:X.Index)(h:burn X i u): u∉vacant0 X:= fun t=> ((mem_filter.mp t).2 i) h
lemma apart_b {x:Per N}{i j:X.Index}(h:burn X i x)(p:burn X j x): i=j:=by by_contra g; exact disjoint_left.mp (X.band_disjoint g) h p
-- Temporal part of B geometry
abbrev portal (i:X.Index)(u:Per N):= delta1 (More N) (nodeT u) (X.start (i+1))
lemma b_exists (i:X.Index)(p: 3≤B.marked.val) : ∃ (y:Per N) (n:ℕ), n ≤ B.D+2 ∧ burn X i y ∧ burn X (i+1) (y+(n:Per N)) ∧ portal X i (y+(n:Per N)) ≤3:=by
 obtain ⟨w,k,h,hk⟩:=find_node (X.stop i); let n:=(B.D+2)/2; have hg:= B.D_pos; have hy : B.D+k≤ 2*n ∧ 2*n≤ B.D+k+2:=by unfold n; omega
 let d:= 2*n-(B.D+k); have hd:d≤3:=by unfold d; omega
 let t:= X.start (i+1); let u:=w+(n:Per N); have h₀:nodeT w=(X.mark i).fall k:=by
    apply add_right_cancel (b:= (k:Per (More N))) -- tune
    rw [← hk]; unfold Tunnel.fall; change X.stop i=X.start i + ↑(B.marked.val-k) + _; rw [add_assoc, ←Nat.cast_add, Nat.sub_add_cancel (by omega : k≤B.marked.val)]; rfl
 have h₁: nodeT u=t+(d:Per (More N)):=by
    unfold u t; rw [nodeT_κ,← X.stop_next,hk, add_assoc,add_assoc,←Nat.cast_add,←Nat.cast_add,show k+(B.D+d)=2*n by unfold d; omega]
 refine ⟨w,n,by unfold n; omega,?_,?_,?_⟩
 · exact (X.mark i).internal _|>.mpr ⟨B.marked.val-k,Nat.sub_le ..,h₀⟩
 · exact (X.mark (i+1)).internal _|>.mpr ⟨d,hd.trans p,h₁⟩
 change delta1 _ (nodeT u) t ≤3; rw [h₁]; exact (delta_nat ..).trans hd
abbrev gazeSet(i:X.Index)(r:ℕ):= (univ:Finset (Per N)).filter fun u=> ZoneNear X i r (nodeT u)
lemma home_dark (i:X.Index){r:ℕ}(p:2*r<B.marked.val){x:Per N} (u:x∈gazeSet X i r) {j:X.Index} (h:burn X j x) : i=j ∨ j=i+1:=by
 let y:=event (nodeT x) (0:Tri (More N)); have hy:= (X.mark j).internal y; obtain ⟨k,v,e⟩:= (Fest X i r p).internal y|>.mp ((z_iff ..).mp ((zone_of_halo ..).mpr ((mem_filter.mp u).2)))
 by_cases f:k≤r; · rw [case_left X i p f] at e; exact Or.inl (apart_b X (j:=j) (i:=i) ((X.mark i).internal y|>.mpr ⟨B.marked.val-(r-k),Nat.sub_le ..,e⟩) h)
 by_cases g:r+B.D≤k; · rw [case_right X i p g] at e; exact Or.inr (apart_b X (i:=j) (j:=i+1) h ((X.mark (i+1)).internal y|>.mpr ⟨k-(r+B.D),by change k ≤ B.D+2*r at v; change _ ≤ B.marked.val; omega,e⟩))
 have hx:y∈X.gap i:=(X.ditch i).internal y|>.mpr ⟨k-r, by change k-r≤ B.D; omega,e.trans (case_ditch X i p (by omega))⟩; exact ((X.at_overlap hx).mp h).imp And.left And.left
lemma portal_in (i:X.Index){x:Per N}{r:ℕ}(h:portal X i x≤r) : x∈gazeSet X i r:= mem_filter.mpr ⟨mem_univ _,X.start (i+1),⟨B.D,le_rfl,X.ditch_last i|>.symm⟩,h⟩
-- activated taper, supports only matter-time, not micro. copy radius head plateau three micro.
local notation "η0"=> (3:ℝ)
namespace Taper
def shell (X:Bands (More N) B)(i:X.Index)(r:ℕ)(u:Per N):ℝ:=max 0 (min 1 (1-( (portal X i u:ℝ)-η0)/r))
lemma clipped (i:X.Index)(n:ℕ)(u:Per N):0≤shell X i n u∧shell X i n u ≤1:=⟨le_max_left ..,max_le zero_le_one (min_le_left ..)⟩
lemma plateau (i:X.Index)(n:ℕ)(u:Per N)(h: portal X i u≤3) : shell X i n u=1:=by
 unfold shell; have hx: (portal X i u:ℝ)≤ η0:= by exact_mod_cast h
 rw [min_eq_left (b:=1-_) (by linarith [div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (Nat.cast_nonneg (α:=ℝ) n)]),max_eq_right zero_le_one]
lemma cutoff (i:X.Index){n:ℕ} (h:0<n)(u:Per N)(p:shell X i n u≠0) : portal X i u≤3+n:=by
 contrapose! p; unfold shell; apply max_eq_left; apply min_le_of_right_le; simp only [sub_nonpos]; rw [le_div_iff₀ (Nat.cast_pos.mpr h),one_mul, le_sub_comm]; -- tune
 have hx: (3:ℝ)+n < portal X i u:= by exact_mod_cast p
 linarith
private lemma limiter (a b:ℝ):|max 0 (min 1 a)-max 0 (min 1 b)| ≤ |a-b|:=by grind
lemma slope {m n: ℕ}{q:ℝ}(h:0<n)(p:(m:ℝ)≤ q*n)(i:X.Index)(x y: Per N)(v:delta1 (More N) (nodeT x) (nodeT y)≤m) : |shell X i n x-shell X i n y|≤ q:=by
 let a:=portal X i x; let b:=portal X i y; have he : a≤ b+m:=by unfold a; apply (d_one_triangle (nodeT x) (nodeT y) (X.start (i+1))).trans; exact ((add_le_add v (le_refl b)).trans_eq (add_comm m b)); -- tune orientation?
 have hg : b≤ a+m:=by unfold b; apply (d_one_triangle (nodeT y) (nodeT x) (X.start (i+1))).trans; exact (add_le_add ((d_sym ..).le.trans v) le_rfl).trans_eq (add_comm ..)
 have hx:|(b:ℝ)-a|≤m:=by
   apply abs_le.mpr; have he₁: (a:ℝ) ≤ b+m:=by exact_mod_cast he
   have he₂ : (b:ℝ) ≤ a+m:=by exact_mod_cast hg
   constructor <;> linarith -- tune
 unfold shell; apply (limiter ..).trans; change |1-((a:ℝ)-_)/_- (1-((b:ℝ)-_) / _)| ≤ q; rw [show (1:ℝ)- (a-η0)/n-(1-(b-η0)/n)=(b-a:ℝ)/n by ring,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n), div_le_iff₀ (Nat.cast_pos.mpr h)]; exact hx.trans p
-- choose q later similar depths. PAINT all Mark H and two color poles exactly.
def lamp (i:X.Index)(r:ℕ)(u:Per N):= if burn X (i+1) u then shell X i r u else 0
lemma bounded (i:X.Index)(r:ℕ)(u:Per N):0≤lamp X i r u∧lamp X i r u ≤1:=by unfold lamp; split; exact clipped ..; exact ⟨le_rfl,zero_le_one⟩
end Taper
end YM.CF.BPress.Bias
