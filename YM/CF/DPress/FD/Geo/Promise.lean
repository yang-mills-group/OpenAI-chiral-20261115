import YM.CF.DPress.FD.Geo.Petty
/-!
 Use max-barycentric box mesh variant. Unlike the Delaunay version,
 interpolate on all weight vectors of candidate nearby≤4-simplexes (can even
 buy the full extension data for all such site centres), not simplices selected by
 affine/co-spherical tests. Box jitter takes a hyperplane separation test only.
 Uniformly:
  - map query x ↦ integer max-simplex weights.
  - for any neighboring x,y the combined memberships land in
    one ≤4-dimensional simplex of nearby centres.
  - discrete Lipschitz bound there.
  - every reach constant after paying the mesh scale only.
 This gives all needed scale/extension properties on probes of the mesh. Symmetry in law;
 no shared shift conditioning.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue Ramp Geo
open scoped Topology BigOperators ENNReal NNReal Classical
variable {I:Type*}[Fintype I]{n:Side}{m l r F:ℕ}
structure Plan (V:Vision n r I)(l m:ℕ) where
 β : I→ Site n → leafL n m
 lives : ∀ i x, Live (β i x)
 dims : ∀ i x y,separation x y ≤1 → (supportT (β i x) ∪ supportT (β i y)).card ≤ 5
 prox : ∀ i x y,separation x y ≤1 → ∀ j∈ supportT (β i x) ∪ supportT (β i y), separation x j ≤4*l
 cost : ∀ i x y,separation x y ≤1→ Ramp.d (β i x) (β i y) ≤2
 consults : ∀ x, V.idT (fun i=>β i x) (cell n x r)
 rot : Signed → Site n→ Equiv.Perm I
 ward : ∀ s x,Chooses V.c (rot s x)
 act : ∀ s i x y u, β (rot s i u) x y = β u (aura s i x) (aura s i y)
namespace Geo
variable {k d:ℕ}(v: WinsC m l k) (p:sizeQ≤ d)
local notation "D"=> s10 l
local notation "Q"=> Hue.Koran d D
local notation "S"=> Site n
abbrev TrueD(d l:ℕ):= Fintype.card (Vcolor d (s10 l))
local notation "Tx" => TrueD d l
abbrev load(d l:ℕ):= Hue.Koran d (s10 l)+TrueD d l*l+TrueD d l*s10 l+5*l
variable (t:2*Koran d (s10 l)< n.val)
include p
abbrev cU (i:Theatre t) : ColorT (TrueD d l) n:= fun x=> Fintype.equivFin _ (kappa t p i x)
lemma tickU (i:Theatre t) : Tight (cU p t i) l:= fun x y t' u e=> different t p i x y t' u ((Fintype.equivFin _).injective e)
-- Protect reduction of closed huge palette args when applied to specific l.
omit p
lemma tul {aρ B':ℕ}{c:I→ ColorT aρ n}(tc:∀ i,Tight (c i) l)(v:WinsC m l k)(hz:2*s10 l<n.val)(hp : B'+aρ*l+aρ*s10 l+5*l ≤ r)(V:Vision n r I)(F:Signed → Site n→Equiv.Perm I)(u:∀ y:Site n,V.idT (fun i=>c i y) (cell n y B'))(φ:∀ s x, Chooses V.c (F s x))(P: ∀ s i x y,c (F s x i) y=c i (aura s x y)):Nonempty (Plan V l m):=by
 let H(x):= pics (c x) l aρ; let g(x):=jitter (H x) (c x) l m aρ; let β(x):=hits (H x) (c x) (g x) m; have hx(i): Lonely (H i) l:= growP _ (tc i) _; have he(i): UBook l (H i) (g i) := fun y h=> (advise_end (c i) (H i) y v (hx i) (c i y).isLt).1
 refine ⟨{β:=β,lives:= fun i x=> born _ _ _ v.1 v.2.1 (he i) (Geo.full (c i) x l), dims:= fun i x y P=> overlap (he i) P (tc i) hz (fun _ u1 _ u2 N L=>agree_end _ _ v (hx i) (tc i) u1 u2 N L hz), prox:= fun i x y P j t=> (tard (he i) P t).1, cost:=fun i x y P=>(cost_m (H i) (c i) (g i)).trans ((Nat.mul_le_mul_left 2 P).trans_eq (by rw [mul_one])), consults := ?_, rot:= F, ward:=φ, act:= ?_}⟩ -- Petty name nonexistent use inline. u explicit
 · intro x i j p'; let A:=aρ*l; let B:= aρ*s10 l; let R:=5*l; let W:= cell n x (A+(B+R)); have h:Set.EqOn (c i) (c j) W:=by
     intro y hy; apply u y _ _; apply V.le _ _ _ _ _ p'; refine Finset.Subset.trans (closer ((cellP y x (A+(B+R))).1 hy)) (scene _ _ ?_); change B'+(A+(B+R)) ≤ r; change B'+A+B+R≤r at hp; omega
   have hh{y}: y ∈ cell n x (B+R)→ (y∈H i ↔ y∈ H j):= by
     intro hy; apply ticket; exact h.mono (Finset.coe_subset.mpr (closer (s:=A) ((cellP ..).1 hy)))
   let e:cell n x R⊆ cell n x (B+R):=scene _ _ (by omega); apply hits_j (H i) (H j) (c i) (c j) _ _ (he i) (he j) (fun x y=> hh (e y))
   · intro y p; let s:cell n y B⊆ cell n x (B+R):= closer ((cellP ..).1 p); exact jitterP _ _ _ _ _ (fun i p=> hh (s p)) (h.mono (Finset.coe_subset.mpr (s.trans (scene _ _ (by omega))))) -- tune
   exact h.mono (Finset.coe_subset.mpr (scene _ _ (by omega)))
 intro s x y u i; let T:=F s x i; let a:=aura s x; have he:c T=c i ∘ a:= funext fun y=>P s i x y; have ht(i'): i'∈H T↔ a i'∈ H i:=sweep _ _ a he (around s x) aρ l i'; exact hits_r _ _ _ _ _ _ s x u y he ht (funext fun i=> (jitterR (c T) _ _ _ aρ s x hz he ht))
private lemma smallQ (p:0<d):D ≤ d*D:=Nat.le_mul_of_pos_left D p
private lemma reprU(d l B r:ℕ)(p:d*s10 l≤ Hue.Koran d (s10 l))(h: Hue.Koran d (s10 l)+B*l+B*s10 l+5*l ≤ r):d*s10 l+B*l+B*s10 l+5*l≤r:=by omega
private lemma reprL(d l:ℕ):d*s10 l≤ Hue.Koran d (s10 l):=by unfold Koran; omega
private lemma reprB(d l:ℕ)(n:Side)(v:s10 l≤d*s10 l)(t:2*Koran d (s10 l)<n.val):2*s10 l<n.val:=by have hv:=reprL d l; omega
lemma costU (p:sizeQ ≤ d)(u:Q ≤ r) (hp : load d l ≤ r) (t:2*Koran d (s10 l)< n.val) {k:ℕ}(v: WinsC m l k) : Nonempty (Plan ((Moon t).rearm u) l m):=by
 exact tul (tickU p t) v (reprB _ _ _ (smallQ (size_p.trans_le p)) t) (reprU d l _ r (reprL d l) hp) ((Moon t).rearm u) (role t) (fun y i j p'=>congrArg (Fintype.equivFin _) (readκ t p i y j p')) (γ_m t) (fun s i x y=> congrArg (Fintype.equivFin _) (movement t p i s x y))
lemma feeD(p:sizeQ ≤ d)(t:2* Koran d (s10 l) < n.val) (v:WinsC m l k) : ∃ (I:Type)(_f:Fintype I)(V:Vision n (load d l) I), Nonempty (Plan V l m):= by
 have he:Q ≤ load d l:=by unfold load; omega
 exact ⟨Theatre t,inferInstance,(Moon t).rearm he,costU p he le_rfl t v⟩
-- purchase aspect ratio B.t enough. Can choose any l=L*m with L sufficiently large.
def RatioT (L:ℕ):Prop:= 0<L∧∃ k:ℕ,∀ (m:ℕ),0<m→ WinsC m (L*m) k
lemma earn :∃ k:ℕ,∀ L:ℕ,k<L→RatioT L:=by
 refine ⟨8*(pack 10*Fintype.card Ask),fun L h=> ?_⟩; have hp:L>0:= Nat.zero_lt_of_lt h; refine ⟨hp,pack 10,fun m t=>⟨t,Nat.le_mul_of_pos_left m hp,le_rfl,Nat.mul_le_mul_right m h.le⟩⟩
lemma Proto {l:ℕ}(v:RatioT l)(t:0<m):∃ r s:ℕ,∀ n:Side,s<n.val→∃ (I:Type)(_f:Fintype I)(V:Vision n r I), Nonempty (Plan V (l*m) m):=by
 obtain ⟨d,p⟩:∃ d:ℕ,sizeQ≤d:= ⟨sizeQ,le_rfl⟩; obtain ⟨k,h⟩:=v.2; exact ⟨load d (l*m),2*Koran d (s10 (l*m)),fun n t'=>feeD p t' (h m t)⟩
end Geo
end YM.CF.DPress.FD
