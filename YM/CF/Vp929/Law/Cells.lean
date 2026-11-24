import YM.CF.Vp929.Law.FaceGauge
import YM.CF.Vp929.Law.Sill
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mesa Cube Lat WalkBound
open scoped Topology Classical Matrix.Norms.Frobenius NNReal
abbrev Realms := Edge Cover → SU.E
namespace Mos
variable {L:Set Rooms}{r:Rooms→ℕ} {K:ℝ}{A:Realms}{g:Elm}{C:Side}{x y z I:Rooms}{a:Cover}{i:Axis}{B:ℕ}
variable (h:Canopy L r (B*C.val))
def Seal (x:Rooms)(A:Realms)(C:Side)(g:Elm)(K:ℝ):Prop:=∀ x' i, zone (x',i)≤x→ GDist (g x'*A (x',i)) (g (x'+step i)) ≤ K/C.val
def wellF (x:Rooms)(A:Realms)(C:Side)(K:ℝ):=∃ g:Elm,Seal x A C g K
def Veil (x:Rooms)(A:Realms)(C:Side)(g:Elm)(K:ℝ):Prop:=∀ x' i, (zone (x',i)).boundary x → GDist (g x'*A (x',i)) (g (x'+step i)) ≤ K/C.val
abbrev Knoll(L:Set Rooms)(r:Rooms→ℕ)(x:Rooms) := Rooms.BlockQ r L x.dim x
def TrailX(L:Set Rooms)(r:Rooms→ℕ)(x y:Rooms):Prop:= Knoll L r x ∧ Knoll L r y∧ x.dim < y.dim ∧ x ≤ y
lemma Seal.up {F:ℝ}(u:Seal x A C g K)(t:F≥ K): Seal x A C g F:= fun a i k=> (u a i k).trans (div_le_div_of_nonneg_right t (by positivity))
lemma Veil.up {F:ℝ}(u:Veil x A C g K)(t:F≥ K): Veil x A C g F:= fun a i k=> (u a i k).trans (div_le_div_of_nonneg_right t (by positivity))
protected lemma Seal.low (p:x ≤ y)(q:Seal y A C g K):Seal x A C g K := fun a i e=> q a i (e.trans p)
protected lemma Seal.restrict (u:Seal x A C g K)(t:TrailX L r y x): Seal y A C g K:= Seal.low t.2.2.2 u
lemma grows {v:Elm}(e:Seal x A C g K)(p:∀ z∈x.marks,g z=v z): Seal x A C v K:=by intro y i h; obtain ⟨u,w⟩:= spanFits.mp h; rw [←p _ u,←p _ w]; exact e y i h
lemma TrailX.trans (p:TrailX L r x y)(u:TrailX L r y z):TrailX L r x z:=⟨p.1,u.2.1,p.2.2.1.trans u.2.2.1,p.2.2.2.trans u.2.2.2⟩
include h
def wetted (C:Side)(r:Rooms→ℕ)(L:Set Rooms):Prop:=∀ X,Knoll L r X→Wide C.val X
lemma wound(p: TrailX L r x y):boundary x y:=by
 let k:= p.2.2; obtain ⟨t,u,a,e⟩:=tiny_at x; have f:= cards h _ p.2.1.1; have w:= p.2.2.1; obtain ⟨j,F⟩:∃ j:ℕ,4-x.dim=4-y.dim+j+1:=⟨y.dim-x.dim-1,by omega⟩; exact inheritB h _ j p.2.1.1 (F ▸ p.1.1) u (inside_of_plane a e) (a.trans k.2)
lemma reflex (t:Rooms)(v:t.Tiny)(u:t.boundary x)(p:Knoll L r x): ∃ y,TrailX L r y x∧ t.inside y:=by
 obtain ⟨j,h',z,v,hz,hK⟩ := slice h t v u.1 (4-x.dim) p.1
 refine ⟨z,⟨from_batch h _ v,p,?_,hK⟩,hz⟩
 by_contra! H; have e:= dim_no h hK; have he:= plane_of_dim hK (le_antisymm e H); exact u.2 (fun i=>by
    have ht:=hz i; by_cases tu:(x i).win
    · obtain ⟨u,v⟩:=ht.2 ((he.win _).2 tu); obtain ⟨q,t⟩:=Wall.full (hK i); exact ⟨(ht.1.trans (hK i)),fun _=> ⟨u.trans_le t,q.trans_lt v⟩⟩
    exact ⟨ht.1.trans (hK i),fun v=>(tu v).elim⟩)
lemma apart (p:Knoll L r x)(q:Knoll L r y)(d:x.dim<y.dim)(u:z ≤ x)(t:z ≤ y): z.boundary y:=by have H:=cards h _ q.1; apply flatCap h (4-y.dim) (y.dim-x.dim-1) q.1 ((show 4-x.dim= (4-y.dim)+(y.dim-x.dim-1)+1 by omega) ▸ p.1) u t
lemma equalLevel (p:Knoll L r x)(q:Knoll L r y)(d:x.dim=y.dim)(v:z.inside x)(u:z≤y):x=y:= (Rooms.setEq h (4-x.dim) (d ▸ q.1) p.1 u v).symm
lemma trail_of {t:Rooms} (p: Knoll L r y)(a:Tiny t)(v:t.inside x)(z:t≤y)(u:Knoll L r x): x≤y:= rising h u p a z v
omit h
lemma fuse {u:Seal y A C g K} {p:ℝ}{t:Elm}(v:TinyStep C t y p) : Seal y A C (t*g) (p+K) :=by
 intro x i hx; have w:= spanFits.mp hx
 let z:=x+step i; let a:=A (x,i); change GDist ((t x* g x)*a) (t z*g z)≤_
 rw [mul_assoc, add_div]; apply (dist_triangle _ (SU.group.mat (t z*(g x*a))) _).trans; rw [bolt,bolt']; exact add_le_add (v _ _ w.1 w.2) (u x i hx)
lemma differs{g':Elm}{K':ℝ}(p:Seal x A C g K)(q:Veil x A C g' K'):WalkBound.Trail x C (g'*g⁻¹) (K'+K):=by
 intro y v a i e f; let z:= a+step i; let A':= A (a,i); let t:boundary (zone (a,i)) x:= boundary_mono (proper v) (spanFits.mpr ⟨e,f⟩)
 change GDist (g' a*(g a)⁻¹) (g' z*(g z)⁻¹) ≤ _; rw [show g' a*(g a)⁻¹=(g' a*A')*(g a*A')⁻¹ by group, add_div]; apply (dist_triangle _ (SU.group.mat (g' z*(g a*A')⁻¹)) _).trans; rw [bolt,bolt',bolt_inv]; exact add_le_add (q a i t) (p a i t.1)

lemma glean(n B:ℕ)(K:ℝ)(hK:0≤K): ∃ L:ℝ,∃ N:ℕ,0 ≤ L ∧∀ C:Side,N≤ C.val→∀ (L':Set Rooms)(r:Rooms→ℕ), Canopy L' r (B*C.val)→ wetted C r L' →∀ x,Knoll L' r x →∀ A:Realms, (∀ y,TrailX L' r y x→ wellF y A C K) →∃ v:Elm,∀ y,TrailX L' r y x→ y.dim<n → Seal y A C v L:=by
 classical
 induction n with
 | zero=> exact ⟨0,0,le_rfl,fun _ _ _ _ _ _ _ _ _ _ => ⟨1,fun _ _ v=> by omega⟩⟩
 | succ n ih=>
    obtain ⟨L,N,e,H⟩:=ih; obtain ⟨R,F,t,G⟩:= strength_All B (L+K) (add_nonneg e hK)
    refine ⟨max L (F+K),max N R, le_trans e (le_max_left ..),fun C q Lk r h w x v A g=>?_⟩
    obtain ⟨z,hZ⟩:=H C ((le_max_left ..).trans q) Lk r h w x v A g
    let S(y:Rooms):Prop:= TrailX Lk r y x ∧ y.dim=n
    have hQ(y:Rooms)(e:S y):∃ v:Elm,Seal y A C v (F+K) ∧ ∀ X,(here X).boundary y → v X=z X:=by
       obtain ⟨Q,l⟩:=g y e.1; have ht:=cards h _ v.1; have hL:= e.1.2.2.1
       have hv: Veil y A C z L:= by intro a i b; obtain ⟨y',v',w⟩:= reflex h (zone (a,i)) (span_fixed a i) b e.1.1; exact hZ y' (TrailX.trans v' e.1) (v'.2.2.1.trans_eq e.2) _ _ (place w)
       obtain ⟨w',v',l'⟩:=G C ((le_max_right ..).trans q) y (by omega) (shoulder h _ e.1.1.1) (w y e.1.1) _ (differs l hv)
       exact ⟨w'*Q,fuse (u:=l) v',fun i h=>by rw [Pi.mul_apply,l' i h]; simp⟩
    choose! a' g' t using hQ
    let v'(i:Cover):= if h:∃ y,S y∧ here i ≤ y then a' h.choose i else z i
    have A0(T:Rooms)(v:TrailX Lk r T x)(e:T.dim<n)(i:Cover)(s:here i ≤ T):v' i=z i:=by unfold v'; split; rename_i H; exact t H.choose H.choose_spec.1 i (apart h v.1 H.choose_spec.1.1.1 (e.trans_eq H.choose_spec.1.2.symm) s H.choose_spec.2); rfl
    refine ⟨v',fun y t' T=>?_⟩; rcases lt_or_eq_of_le (b:=n) (by omega : y.dim≤n) with p|p
    · exact grows ((hZ y t' p).up (le_max_left ..)) (fun i H=> (A0 y t' p i H).symm)
    refine grows ((g' y ⟨t',p⟩).up (le_max_right ..)) (fun i e=>?_)
    have H:∃ z:Rooms,S z∧ here i≤z:=⟨y,⟨t',p⟩,e⟩; unfold v'; rw [dif_pos H]
    by_cases v:y=H.choose; rw [v]; let d:= H.choose_spec; refine Eq.trans (t y ⟨t',p⟩ i ⟨e,fun v'=>v (equalLevel h t'.1 d.1.1.1 (p.trans d.1.2.symm) v' d.2)⟩) (t _ d.1 i ⟨d.2,fun v'=>v (equalLevel h d.1.1.1 t'.1 (d.1.2.trans p.symm) v' e).symm⟩).symm
lemma united(B:ℕ)(K:ℝ)(hK:0≤K) :∃ L:ℝ,∃ N:ℕ,0 ≤ L ∧∀ C:Side,N≤ C.val→∀ (L':Set Rooms)(r:Rooms→ℕ), Canopy L' r (B*C.val)→ wetted C r L' →∀ x,Knoll L' r x →∀ A:Realms,(∀ y,TrailX L' r y x→ wellF y A C K)→∃ v:Elm, Veil x A C v L:=by
 obtain ⟨L,N,e,P⟩:= glean 5 B K hK; refine ⟨L,N,e,fun C q Lk r h w x v A g=>?_⟩; obtain ⟨z,t⟩:=P C q Lk r h w x v A g; refine ⟨z,fun i j u=>?_⟩; obtain ⟨t',e,h'⟩:=reflex h (zone (i,j)) (span_fixed i j) u v; exact t t' e (by have h:= cards h _ e.1.1; omega) i j (place h')
end Mos
end YM.CF.VolumeCape
