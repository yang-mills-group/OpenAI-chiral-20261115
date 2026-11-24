import YM.CF.Proa.Uta
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
set_option synthInstance.maxSize 8000
open Acorn
open MeasureTheory Jet Phase.Sample
variable {U D Y n ι:Type}{b d r h a e:ℝ}
section
variable {E Y n D:Type}[TopologicalSpace D][TopologicalSpace E][Fintype Y][DecidableEq Y][LinearOrder n][Fintype n]{X:Master D Y}{Z: Master E Y}{O:n→Y}{S:Seal Y}{F:D→Op n}{v:D→ Wave n}{x y:E→D}{A:E→ FC n}
abbrev fruitF(v:D→Wave n)(F:D→Op n)(x:D):Wave n:= acts (exp (dg (F x))) (v x)
lemma climb(q:S.Nonempty)(u:Grove Z.frame S)(hn:0≤ d)(he:0<a)(hm:1≤h)(H:Plum X O (fun x=> cue false true (F x)) a d)(k:Cop X Z x)(g:Cop X Z y)(t:∀ R,Disjoint S R→∀ i,X.moves R (y i) (x i))(W: Carries Z O S a (Fume Z.k a (d+d) h) A b)(v':∀ i, F i*F i=0)(hp:∀ i,acts (A i) (v (x i))=v (y i)):∃ P:E→FC n,Carries Z O S a h P (Acorn.worth Z.k*b*Real.exp (3*(Acorn.worth Z.k*(2*DriftX a h (d+d) (S.card*(2*d)) Z.k)))) ∧ ∀ i,acts (P i) (fruitF v F (x i))=fruitF v F (y i):=by
 let C (i:E):=dg (F (y i)); let V(i:E):=dg (F (x i)); let T(i:E):=cue false true (F (y i))-cue false true (F (x i))
 have hx(i):UnitR (C i):=held _ (v' _); have hv:0≤h:=zero_le_one.trans hm
 have hc(v:I n): Drop Z O a v (fun i=> unitL (C i) (Acorn.pen v)) (d+d):=by
    have hp:=Drop.seam v H g; unfold C; simp_rw [brass_X]; exact hp
 have hu:=peal (p:=g) (q:=k) u t H he.le
 have hY:Carries Z O S a h (fun i=>exp (C i)*exp (-V i)) _:= earned_t (A:=C) (B:=-V) (F:=T) q u he.le hv (add_nonneg hn hn) hx (by funext i; unfold Function.comp T; rw [mix_less,←brass_X,←brass_X]; rfl) hu hc fun i=> (unit_negR _ (held (F (x i)) (v' _))).exhaust
 refine ⟨_, (fumeC hx (add_nonneg hn hn) hc he.le hv W).product hY q he.le hv,fun i=>?_⟩
 have hs(x:FC n):exp (-x)* exp x=1:=mul_eq_one_comm.mp (wind_inv _)
 change acts ((exp (C i)*A i*exp (-(C i)))*(exp (C i)*exp (-(V i)))) (acts (exp (V i)) (v (x i)))= acts (exp (C i)) (v (y i))
 rw [←mul_assoc, mul_assoc _ (exp (-(C i))) (exp (C i)),hs,mul_one,←act_mul,mul_assoc _ (exp (-(V i))) (exp (V i)),hs,mul_one,act_mul,hp]
end
variable {L:Side}{j:ℕ}{ho: Odd L.val}{ι:Type*}
abbrev aer (P:ι→(n:Side)→Aim n)(i n):= Moire.bloom (P i n)
-- grant uses threshold post history allowance. true physical responses.
omit L ho
include j
lemma claimE (k:Even j)(hj:1≤j)(K:WG ι)(H:Lively K)(p:∀ i n,K i n 1=0)(M:ι→Male)(N:ℕ)(Z:ℝ)(hk:1≤Z):∃ c a y:ℝ, 0<c∧ 0<a∧0<y∧∃ d:ℕ,∀ e:ℝ,0<e→ e≤ c → ∀ B m:Side,d≤(CSide m B).val→let G:=idrat (CSide m B);∀ i, let X(x:CapX m B e):=prime j K M i G (unionP (x.val,x.val)); Plum (newX (Spire.soar m B e) (aether N Z e m B) N) (tempo G 1).home (fun x=>cue false true (X x)) a y∧∀ x,X x*X x=0:=by
 let L:= (1:Side); have ho:Odd L.val:=odd_one; obtain ⟨a,v,e,h,hv,g,w,W⟩:= (prism_s L ho _ k hj _ H p M).1
 obtain ⟨c,v',n,C⟩:= massive j L ho k hj _ (canUse j L ho) true
 obtain ⟨η,m,H⟩:= victoria N Z a v e (zero_le_one.trans hk) g h hv
 refine ⟨min e c,a/2,η,lt_min g v',half_pos h,m,max w n,fun e₀ h' b B m f=>?_⟩; intro G i X; have hl:e₀≤e:=b.trans (min_le_left ..); have ht:e₀≤ c:=b.trans (min_le_right ..)
 refine ⟨H m B e₀ h' hl _ (W i G rfl ((le_max_left ..).trans f)),fun x=>?_⟩
 let Y:=jointly x.val (x.property.shrink ht) v'
 let T:=C G rfl ((le_max_right ..).trans f) (M i) (x.val,x.val) Y; exact (tag_g _ T.lead).nil
lemma exhale (a v t K:ℝ)(u:ℕ)(ha:0<a)(ht:0<t)(p:0<v)(h:0<K):∃ w:ℝ,0<w∧∀ n:ℕ,0<n→∀ z:ℝ,1≤z→
 Acorn.worth u*Real.exp (t*n*(Fume u a (v+v) z)^2)*Real.exp (3*(Acorn.worth u*(2*DriftX a z (v+v) (n*(2*v)) u))) ≤ Real.exp (w*n*z^2):=by
 let p:=Acorn.worth u; have he:1≤p:=one_w _
 let w:=t*(Fume u a (v+v) 1)^2+ 6*(p*DriftX a 1 (v+v) (2*v) u); have hw:0≤w:=by unfold w Fume DriftX; positivity
 refine ⟨p+w,by positivity,fun n v z l=>?_⟩; let u:=z*z
 have hs:1≤(n:ℝ):=by exact_mod_cast v
 rw [mul_assoc,← Real.exp_add]; have hx:p≤ Real.exp p:=by linarith [Real.add_one_le_exp p]
 apply le_trans (mul_le_mul_of_nonneg_right hx (Real.exp_pos ..|>.le)); rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
 have hy:p ≤ p*n*z^2:=le_trans (le_mul_of_one_le_right (zero_le_one.trans he) hs) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ l))
 unfold w Fume DriftX p; unfold p at hy; linarith only [hy]
include L ho

variable (L ho)
lemma shop(T:Pricing j L ho (Thread j))(Y:Stamped j L ho T)(k:Even j)(hj:1≤j)(K:WG ι)(H:Lively K)(p:∀ i n,K i n 1=0)(M:ι→Male)(N:ℕ)(Z:ℝ)(hk:1≤Z)(r:Repair j):∃ e:ℝ,0<e∧ ∃ d:ℕ,∀ {e' B} (P: Grasp T B e'),0 < e'→ Pearl P→ e'≤e→ P.baseline ≤ r.d→∃ a C :ℝ,0<a ∧ 0<C∧∀ {m:Side},max d P.roundZ≤(CSide m B).val→let G:=idrat (CSide m B);∀ (S:Broc.Table m B),Grove (terr _) S →∀ i,∀ z:ℝ,1≤z→∃ A:Castle m B e' S→ FC (Iota G),Carries (landX N Z S e') (tempo G 1).home S a z A (Real.exp (C*S.card*z^2))∧ ∀ x,let F(y:Skin m B):= acts (exp (dg (prime j K M i G (unionP (y,y))))) (graft G P y (M i)); acts (A x) (F (x.val false)) = F (x.val true):=by
 obtain ⟨e,a,b,he,ha,hb,d,H⟩:= claimE k hj K H p M N Z hk
 refine ⟨min e r.d,lt_min he r.pd,max d r.n,fun {c B} P g y h Y'=>?_⟩
 have hp:= h.trans (min_le_left ..); obtain ⟨l,v,hl,hv,U⟩:= endeavor y Y g hj r N Z hk (h.trans (min_le_right ..)) Y'
 let t:=min a l; have ht:0<t:=lt_min ha hl; obtain ⟨w,hw,V⟩:= exhale (j:=j) t b v 1 N ht hv hb one_pos -- j explicit?
 refine ⟨t,w,ht,hw,fun {m} v'=>?_⟩; intro G S q i z h'
 have hx:= (le_max_left ..).trans v'; obtain ⟨P',W⟩:= H c g hp B m ((le_max_left ..).trans hx) i
 let L:=Fume N t (b+b) z; have hL:1 ≤ L:=by unfold L Fume; exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_w _)) ((Real.one_le_exp ht.le).trans (le_add_of_nonneg_right (by positivity)))) h' -- tune
 obtain ⟨A,hf,hT⟩:= U m ((le_max_right ..).trans hx) ((le_max_right ..).trans v') (M i) S q L hL
 let X:=newX (Spire.soar m B c) (aether N Z c m B) N; let Z':= landX N Z S c; let Y(i:Bool)(x:Castle m B c S): CapX m B c:=⟨x.val i,x.property.1 i⟩; have he(i): Cop X Z' (Y i):=⟨rfl,rfl,((continuous_apply _).comp continuous_subtype_val).subtype_mk _,fun S x y t=> t _,fun E _ _ _ V h f t x p=>t x p _⟩
 have hk:T=T:=rfl
 have hv:S.Nonempty:=by cases q<;> simp
 let J(x:CapX m B c):= graft (m:=m) G P x.val (M i); have hS:∀ R,Disjoint S R→∀ x,X.moves R (Y true x) (Y false x):=by
    intro R h x; change Agrees (↑R:Set (Site (Domain m B))) (x.val true) (x.val false); have he:R⊆Sᶜ:=Disjoint.le_compl_left h; exact fun i g p=> (x.property.2 i (he g) (he p)).symm
 obtain ⟨A,p,u⟩:= climb (v:=J) (h:=z) hv q hb.le ht h' (P'.weak le_rfl (min_le_left ..)) (he false) (he true) hS (narV _ _ _ _ _ t _ _ (min_le_right ..) (zero_le_one.trans hL) hT) W hf
 exact ⟨A,p.more (V S.card (card_pos.mpr hv) z h'),u⟩
end YM.CF.Proa
