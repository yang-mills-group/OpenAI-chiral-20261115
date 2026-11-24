import YM.CF.BPress.Bias.Starlife
/-! §lem:B-bias/f_z. Actual free history projector family symbol, all the time-neighborhood orientations and collars. Keywords PU. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Laurent Bloch Next.Free Cube Fir Lat Spin Paint Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial Eye Pf Branch Grid Wealth Locale Bands Tunnel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N: Side} {j:ℕ} {M:Jill.Male} {F C:Op (Single N)} (Z:Paint (More N)) {B:BandWidth} (X:Bands (More N) B)
namespace Taper
variable (U V:Op Slot)
/-- actual homogeneous comparison uses the first matrix in D, second in N -/
def Signed : Prop:= ∀ i:X.Index,∀ x:Site N,node x∈X.band i→ Z (node x)=if X.Dmark i then U else V
variable {q:ℝ}{m n:ℕ}
private lemma near_carried (i:X.Index)(x y:Per N)(h:y∈gazeSet X i n)(b:delta1 (More N) (nodeT x) (nodeT y)≤m): x∈gazeSet X i (n+m):= mem_filter.mpr ⟨mem_univ _,zone_add X i ((mem_filter.mp h).2) ((d_sym ..).le.trans b)⟩ -- tune
lemma comp_C (i:X.Index)(p:0<n)(s:2*(3+n+m)<B.marked.val)(u:0<q)(h:Signed Z X U V)(r:(m:ℝ) ≤ q*n) : ColorR Z V U (lamp X i n) q m (vacant0 X) (gazeSet X i (3+n+m)):=by
 let f:=lamp X i n; let t:= 3+n; let F0:=gazeSet X i (t+m); constructor
 · intro x y; obtain ⟨a,b⟩:=bounded X i n x; obtain ⟨p,q⟩:=bounded X i n y; exact abs_le.mpr ⟨by linarith,by linarith⟩ -- issue f abbreviations
 intro x y d f1 f2 k; let C (x:Single N):= Z (node (penX x)); let g(x:Single N)(y:Single N):Prop:= (C x=U ∧ C y=V)∨(C x=V ∧ C y=U); change fog x∈F0 ∧ fog y∈F0 ∧g x y
 have hc(i j:Single N):delta1 (More N) (nodeT (fog i)) (nodeT (fog j))≤distH i j:=by unfold distH fog; have he:=delta_at (node (penX i)) (node (penX j)) 0; rw [node_κ,node_κ] at he; exact he
 let D(a b:Single N):=delta1 (More N) (nodeT (fog a)) (nodeT (fog b)); let u0(x:Single N):=burn X (i+1) (fog x); let u1(x:Single N):=shell X i n (fog x); have hu1(x:Single N):f (fog x)=if u0 x then u1 x else 0:=rfl; change q< |f (fog x)-f (fog y)| at k; rw [hu1,hu1] at k
 have he(a b:Single N)(p0:u0 a)(p1:¬u0 b)(u':fog b∉vacant0 X)(ν:u1 a≠0) (d:D a b ≤m): fog a∈F0∧fog b∈F0∧g a b :=by
    let y:=penX b; have hx:= cutoff X i p (fog a) ν; have e:= portal_in X i (hx.trans (Nat.le_add_right (3+n) m)); have ht:=near_carried X i (fog b) _ (portal_in X i hx) ((d_sym ..).le.trans d); simp only [vacant0,mem_filter,mem_univ,true_and, not_forall,not_not] at u'; obtain ⟨j,hj⟩:=u'; have hT : burn X i (fog b):=(home_dark X i s ht hj|>.resolve_right (fun h=>p1 (show burn X (i+1) (fog b) from h ▸ hj)))|>.symm ▸ hj
    refine ⟨e,ht,?_⟩; have tu1:=h (i+1) (penX a) ((marking X (i+1) (penX a)).2 p0); have tu0:=h i y ((marking X i y).2 hT); change C b=_ at tu0; change C a=_ at tu1; unfold g; rw [tu0,tu1,X.prev_next]; by_cases f:X.Dmark i<;>simp [f] -- split
 have hm:= (hc x y).trans d; split_ifs at k with a b b
 · exact False.elim ((not_lt.mpr (slope X p r i _ _ hm)) k)
 · refine he x y a b f2 (fun n=>?_ ) hm; rw [n,sub_zero,abs_zero] at k; linarith
 · have hv:u1 y≠0:=by intro t; rw [t,sub_zero,abs_zero] at k; linarith
   obtain ⟨l,r,c⟩:= he y x b a f1 hv ((d_sym ..).le.trans hm); exact ⟨r,l,(Or.comm.mp (c.imp And.symm And.symm))⟩ -- tune
 rw [sub_zero, abs_zero] at k; linarith
end Taper

-- terminal expression: really real part of f_z. variant works for ALL implicit position choices by signed lift. nominal cost into `r`, bound at one time for each tangent cell.
variable {H:Support N}
abbrev netdark(j:ℕ)(M:Jill.Male)(H:Support N):=ramp (loose H) (pos H) (nativeX j M N)
abbrev fareF(j:ℕ)(M:Jill.Male)(H:Support N)(Z:Paint (More N)) :=billZ (Locks H true) (Locks H false) (nativeX j M N) 0 (coupling Z)
lemma refFare {v:ℝ}(U:Pass (pos H) (Hole.neg H) (loose H) (nativeX j M N) v): fareF j M H Z=(1/4:ℝ) • loss (netdark j M H) (coupling Z):=by unfold fareF billZ mood; rw [Spin.tiltT _ U.a]; rw [show shun (Single N) (Locks H true) (Locks H false)= loose H from U.l0.symm]; rfl
lemma zero_Fare {v r:ℝ} {Z:Paint (More N)}(h:1≤j)(U:Pass (pos (Lower (vacant0 X))) (Hole.neg (Lower (vacant0 X))) (loose (Lower (vacant0 X))) (nativeX j M N) v)(A:Op Slot)(w:∀ x:Site N,x∉ Lower (vacant0 X)→ Z (node x)=A)(b:Bore (screen j M (vacant0 X)) (coupling Z) r): fareF j M (Lower (vacant0 X)) Z=0:=by
 let S:=vacant0 X; let P:=screen j M S; let C:Paint (More N):=fun _=>A; let Q:= Lower S; let L:=loose Q; let V:=Z-C; have he: coupling V*L=0:=shadowed (S:=Q) V (fun x p=> by unfold V C; rw [Pi.sub_apply,w x p]; simp); -- tune unfold order
 have hv:L*coupling V=0:= (loose_lock _).symm.trans he; have hx:P*coupling Z=P*coupling C:=sub_eq_zero.mp (by rw [←mul_sub, ←coupe_sub]; change P*coupling V=0; nth_rw 1 [←(show P*L=P from across U.toEmpties.r U.ramp_star U.ramp_L)]; rw [mul_assoc,hv,mul_zero])
 have hg:P*coupling Z*(1-cc P)=0:=by rw [hx, toll_r S M v h U A,mul_assoc,(ccProj b.p).mul_one_sub_self,mul_zero] -- tune name
 rw [refFare Z U]; change _ • loss (screen j M (vacant0 X)) _=0; rw [loss, b.portion,hg,zero_mul]; simp [pencil]


-- constant transfer from support and recovery
lemma screen_appear (j:ℕ)(h:1≤j) (P:Pledge)(v:ℝ)(u:0<v):∃ T:Pledge,∀{d:ℝ}(p:0≤d)(N:Side)(K:Shelf N d j P)(M:Jill.Male)(t:Finset (Per N)), let H:=Lower t; Pass (pos H) (Hole.neg H) (loose H) (nativeX j M N) v→ Appear (screen j M t) T:=by
 let A:= Paint.stream 1; let W:= unary.plus (A.plus A); obtain ⟨T,K⟩:=Basement.funding A A W P u Tenant.quota Form.paid; refine ⟨T,?_⟩; intro d p N K' M t H r
 let F: Form N Unit:= Form.init (fun _=> (1:Bkg (More N))); let P0:=pos H; let Q:=Hole.neg H; let g:=fun _:Unit=> H; let i:=fun _:Unit=> (⟨1, guard0 p⟩ : OpenW N d); let b:=F.stage
 have ht(u:Bool):A.Costs b (fun _=> Lock H u):=trackprice (U:=g) F (by intro _ _ _ _ _ v; exact False.elim ((or_self_iff ..).mp v|>.elim fun a b=>b a)) (fun i=> by dsimp only [g]; by_cases h:i∈H <;> simp [h]) u -- tune
 let L:=loose H; have hs:W.Costs b (fun _=>L):=by unfold L; rw [r.l0]; exact Costs.sub Costs.one (Costs.plus (ht true) (ht false))
 have hp:P.Costs b (fun _=>nativeX j M N):=by rw [nativeEq h]; exact Form.pulls (K'.entries M) i continuous_const (fun _ _ _=> le_rfl)
 refine ⟨F,(K (b:=b) (fun _=>P0) (fun _=>Q) (fun _=>L) _ (fun _=>1) F.full (fun _=> r) (ht true) (ht false) hs hp ?_ ).rump⟩
 refine ⟨fun _=>by simp,one_pos,continuous_const,fun S x x' p=>?_⟩; simp [b.pos] -- tune
lemma B_bias {d:Side} (P:Pledge)(h:1≤j)(U B:Op Slot)(g:U ≠ B): ∃ (r m:ℕ)(c:ℝ), 0<c ∧∀ (M:Jill.Male)(N:Side), m≤ N.val →∀ (b:BandWidth)(e:b.D=d.val)(X:Bands (More N) b), r≤ b.marked.val →∀ (Z:Paint (More N)), Sails.Plane Z → Taper.Signed Z X U B → ∀ {a v:ℝ}, let t:=vacant0 X; let H:=Lower t; Pass (pos H) (Hole.neg H) (loose H) (nativeX j M N) a→ Bore (screen j M t) (coupling Z) v → Appear (screen j M t) P → ∀ i:X.Index, ∀ k:Tri N, ∃ u: Per N, let x:=event u k; u∈gazeSet X i r ∧ x ∉ H ∧ ash x (fareF j M H Z) ≤ -c:=by
 obtain ⟨n,m,q,c,hq,hc,V⟩:=fencing j (d.val+2) h P U B g -- result ColorR Z B? argument f returns T U? inspect
 obtain ⟨r,s⟩:=exists_nat_gt ((m:ℝ)/q+1); have hr:0<(r:ℝ):=lt_trans (by positivity) s; have hr':(m:ℝ)≤ q*r:=by linarith [(div_lt_iff₀ hq).mp (by linarith : (m:ℝ)/q<r)]; -- indent
 let v:= 3+r+m; let y:=2*v+1; have ht:v≤y:=by unfold y; omega
 refine ⟨y,n,c/4,by positivity,?_⟩; intro M N t B' e X h0 Z H HZ a b t P hP Bc p i k -- t ambiguity
 have hu :3≤B'.marked.val:=by unfold y v at h0; omega
 let hq₁(i:X.Index)(x₀:Per N):=(Taper.bounded X i r x₀); obtain ⟨u,k',hh,t0,j',hp⟩:= b_exists X i hu; let f:=Taper.lamp X i r
 have he := Taper.comp_C Z X U B i (by exact_mod_cast hr) (by unfold y v at h0; omega) hq HZ hr'; let C:= lost (screen j M (vacant0 X)) (coupling Z); have hu1:f u=0:=if_neg fun p=> X.next_ne i (apart_b X p t0); let z:=u+(k':Per N); have hp1:f z=1:=by unfold f Taper.lamp; rw [if_pos j', Taper.plateau X i r z hp]
 obtain ⟨x,f1,f2,pf⟩:= V M N (by assumption) f Z (vacant0 X) (gazeSet X i v) u k' (by rw [←e]; exact hh) (burn_out X i t0) (burn_out X (i+1) j') hu1 hp1 he _ _ hP Bc p
 let s':=x 0; let x':=event s' k; suffices he:ash x' (fareF j M (Lower (vacant0 X)) Z) ≤ -(c/4) by
    refine ⟨s', ?_,mt (fun g:x' ∈ P=> (mem_filter.mp g).2) f1,he⟩
    obtain ⟨a,t,h⟩:= (mem_filter.mp f2).2; exact mem_filter.mpr ⟨mem_univ _, _,t,h.trans ht⟩ -- underscore tune
 change c≤ash x C at pf; rw [←Sails.ash_orientation Z x x' rfl _ hP H Bc] at pf
 rw [refFare Z hP]; have hv: loss (screen j M (vacant0 X)) (coupling Z) ≤ -C:=Pf.Helm.below Bc.PSD (Pf.Issued.normL Bc); let w:=1/4; apply (ash_ord (smul_le_smul_of_nonneg_left hv (show (0:ℝ)≤1/4 by norm_num)) x').trans; rw [show ash x' ((1/4:ℝ) • (-C))= -(ash x' C/4) from ?_]; linarith
 unfold ash; rw [show book x' x' ((1/4:ℝ) • (-C))=(1/4:ℝ) • -book x' x' C from rfl, Matrix.trace_smul,Matrix.trace_neg]; simp; ring
end YM.CF.BPress.Bias
#print axioms YM.CF.BPress.Bias.B_bias
