import YM.SU5.FiniteGaugeData.Jadot.Menton
import YM.SU5.FiniteGaugeData.Nine.Oat
import Mathlib.Topology.ContinuousMap.Weierstrass
/-! # Prebudgeted uniform local repair radii. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window.Presidio
open Parcel.Tanin Fock Fock.Reduction Reduction.Hutch Reduction.Drama Reduction.Drama.Pack Reduction.Jersey -- tune resolution
open Reduction.Dinar Reduction.Rheims Reduction.Verna Reduction.Dijon
open Next.Free Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision Tree Finset Exterior
open Lat Rush Cube Scroll SU Peaks Dial Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Cour Fir Ember Aroma Cascade Gall
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
open Pivot Fock.Brique
attribute [local instance] opCStarAlgebra
namespace Gato
open LinearMap Disjoint -- tune
variable {N : Side}{k:ℕ}{a d b e μ s r:ℝ}{M:Male}
variable {A B X:Op (Single N)}
lemma monograph (S:Finset (Single N)): Commute (tickA N) (cutM S):=by
 show _*_=_*_; rw [touchP N, cut_meet, cut_meet,inter_comm]
lemma displace : Neighbor 0 (tickA N):=by rw [touchP]; exact neighProj _
lemma negPos(p:Neighbor k A):Neighbor k (-A):= neighbor_entry fun i j t=>by rw [Matrix.neg_apply,neighbor_iff p i j t,neg_zero]
lemma helios(h:Neighbor k A)(p:Neighbor k B): Neighbor k (A+B):=neighbor_entry fun i j t=> by rw [Matrix.add_apply, neighbor_iff h i j t, neighbor_iff p i j t]; simp
lemma loft{u:ℕ}(p:Neighbor k A)(h:k≤u):Neighbor u A:=neighbor_entry fun _ _ l=> neighbor_iff p _ _ (lt_of_le_of_lt h l)
lemma bliss(p:Neighbor k A)(c:ℝ):Neighbor k (c • A):=neighbor_entry fun _ _ t=>by rw [Matrix.smul_apply,neighbor_iff p _ _ t,smul_zero]
lemma liq_add (h:Liquid k A a)(p:Liquid k B b):Liquid k (A+B) (a+b):=by
 obtain ⟨S,g,h⟩:=h; obtain ⟨T,v,p⟩:=p; refine ⟨S+T,helios g v,by rw [show S+T-(A+B)=(S-A)+(T-B) from by abel]; exact (norm_add_le ..).trans (add_le_add h p)⟩
lemma liq_grow{u:ℕ}(p:Liquid k A a)(h:k≤u)(v:a≤b):Liquid u A b:=by obtain ⟨S,g,e⟩:=p; exact ⟨S,loft g h,e.trans v⟩
lemma liq_negA(p:Liquid k A a):Liquid k (-A) a:=by obtain ⟨S,h,p⟩:=p; exact ⟨-S,negPos h,by rw [neg_sub_neg,norm_sub_rev]; exact p⟩
lemma liq_mulA {u:ℕ}(h:Liquid k A e)(p:Liquid u B e)(v:‖A‖≤ a)(t:‖B‖≤b):Liquid (k+u) (A*B) ((a+e)*e + b*e):=by
 obtain ⟨S,g,h⟩:=h; obtain ⟨T,l,p⟩:=p; have he:‖S‖≤a+e:=by nth_rw 1 [←sub_add_cancel S A]; exact (norm_add_le ..).trans ((add_le_add h v).trans_eq (add_comm ..))
 refine ⟨_, neigh_mul g l,?_⟩; rw [show S*T-A*B=S*(T-B)+(S-A)*B from by noncomm_ring, mul_comm b]; exact (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul he p (norm_nonneg _) ((norm_nonneg _).trans he))) ((norm_mul_le ..).trans (mul_le_mul h t (norm_nonneg _) ((norm_nonneg _).trans h))))
-- algebraic permit in arbitrary dimension sequence
section
variable {ι:Type*}{m:ι→ Side} {X Y P Z:∀i:ι,Op (Single (m i))}
structure Hemi (m:ι→Side)(X:∀i:ι,Op (Single (m i))):Prop where
 Bound : ∃ b:ℝ,0≤b∧∀ i, ‖X i‖≤b
 work(ε:ℝ)(p:0<ε):∃ k,∀ i,Liquid k (X i) ε
namespace Hemi
lemma none (h:∃ b:ℝ,0≤b∧∀i,‖X i‖≤ b)(k:ℕ)(t:∀i, Neighbor k (X i)): Hemi m X:=⟨h,fun _ he=>⟨k,fun i=>⟨_,t i,by rw [sub_self,norm_zero]; exact he.le⟩⟩⟩
variable (h:Hemi m X)(t:Hemi m Y)
include h
omit h in
lemma conV (m:ι→ Side)(p:ℝ):Hemi m (fun i=> Canon (Single (m i)) p):=by
 apply none _ 0 (fun i=> bliss (neighOne _) p); exact ⟨_,norm_nonneg p,fun i=> (show ‖Canon (Single (m i)) p‖≤‖p‖ from by unfold Canon; rw [norm_smul,norm_one,mul_one])⟩
lemma add_f(t:Hemi m Y):Hemi m (fun i=> X i + Y i):=by
 obtain ⟨a,l,p⟩:=h.Bound; obtain ⟨b,u,k⟩:=t.Bound; refine ⟨⟨_,add_nonneg l u, fun i=> (norm_add_le ..).trans (add_le_add (p i) (k i))⟩,fun ε v=>?_⟩
 obtain ⟨i,e⟩:=h.work (ε/2) (by positivity); obtain ⟨j,f⟩:=t.work (ε/2) (by positivity); exact ⟨max i j,fun y=>liq_grow (liq_add (liq_grow (e y) (le_max_left i j) le_rfl) (liq_grow (f y) (le_max_right ..) le_rfl)) le_rfl (le_of_eq (by ring))⟩ -- tune
lemma neg_f:Hemi m (fun i=> -X i):= by
 obtain ⟨a,l,p⟩:=h.Bound; exact ⟨⟨a,l,fun i=>(norm_neg _).trans_le (p i)⟩,fun ε v=> let k:= (h.work ε v).choose; ⟨k,fun i=> liq_negA ((h.work ε v).choose_spec i)⟩⟩
lemma subVH(t:Hemi m Y):Hemi m (fun i=> X i-Y i):=by simp only [sub_eq_add_neg]; exact h.add_f t.neg_f
lemma stE : Hemi m (fun i=> star (X i)):=by
 obtain ⟨a,l,p⟩:=h.Bound; refine ⟨⟨a,l,fun i=> (norm_star _).trans_le (p i)⟩,fun ε v=> ?_⟩; obtain ⟨k,e⟩:=h.work ε v; refine ⟨k,fun i=>?_⟩; obtain ⟨S,z,u⟩:=e i; exact ⟨_, Window.Brique.Neighbor.adj z, by rw [←star_sub,norm_star]; exact u⟩
lemma mult_f(t:Hemi m Y) : Hemi m (fun i=>X i*Y i):=by
 obtain ⟨a,l,p⟩:=h.Bound; obtain ⟨b,u,k⟩:=t.Bound; refine ⟨⟨_,mul_nonneg l u,fun i=> (norm_mul_le ..).trans (mul_le_mul (p i) (k i) (norm_nonneg _) l)⟩, fun ε v=> ?_⟩
 let x:ℝ→ℝ:=fun t=>(a+t)*t + b*t; have h0:ContinuousAt x 0:=by unfold x; fun_prop
 obtain ⟨u,hk,hb⟩:= (((h0.tendsto.mono_left (y:=nhdsWithin 0 (Set.Ioi 0)) nhdsWithin_le_nhds).eventually (gt_mem_nhds (show x 0 <ε from by simpa [x] using v))).and self_mem_nhdsWithin).exists
 obtain ⟨j,s⟩:= h.work u hb; obtain ⟨i,e⟩:=t.work u hb; exact ⟨j+i,fun y=>liq_grow (liq_mulA (s y) (e y) (p y) (k y)) le_rfl hk.le⟩
lemma scale_r (c:ℝ): Hemi m (fun i=>c • X i):= by simpa only [canon_left] using (conV m c).mult_f h
omit h in
lemma one_c (m:ι→Side): Hemi m (fun i=> (1:Op (Single (m i)))):=by simpa only [Canon,one_smul] using (conV m 1)
lemma power_r(k:ℕ): Hemi m (fun i=>X i ^k):=by
 induction k with | zero=> simp_rw [pow_zero]; exact one_c m | succ k ih=> simp_rw [pow_succ]; exact ih.mult_f h
open Polynomial in
lemma poly (c:Polynomial ℝ) : Hemi m (fun i=> aeval (X i) c):=by
 induction c using Polynomial.induction_on' with
 | add _ _ x y=> simp only [map_add]; exact x.add_f y
 | monomial i p=> simp_rw [aeval_monomial,←canon_map,canon_left]; exact (power_r h i).scale_r p -- tune
end Hemi
end
-- polynomial approximation independent of d
section
variable {n:Type*}[Fintype n][DecidableEq n]{H:Op n}{B':ℝ}{w:ℝ}
open Polynomial
lemma spectral_evalR (U:UNI n)(D:n→ℝ)(p:Polynomial ℝ): aeval (spectral U D) p = spectral U (fun i=> p.eval (D i)):=by
 induction p using Polynomial.induction_on' with
 | add p q h t=> rw [map_add,h,t,spectral_add]; congr 1; ext i; rw [eval_add]; rfl
 | monomial i p=> rw [aeval_monomial,spectral_pow,←canon_map,canon_left,spectral_smul]; exact congrArg (spectral U) (funext (fun j=>by rw [eval_monomial]; rfl))
abbrev rt(x:ℝ):ℝ:=Real.sqrt x⁻¹ -- parsing! √(x⁻¹)
lemma flight_t{P:Polynomial ℝ}(t:0<a)(v:Canon n a≤ H)(w:H≤Canon n b)(h:lit H)(p:0≤e)(g:∀ x∈ Set.Icc a b, |P.eval x-rt x|≤ e): ‖aeval H P - tangle H‖ ≤ e:=by
 obtain ⟨U,d,T⟩:= spectral_exists H h.isSelfAdjoint
 let r(i:n):=a; let f(i:n):=rt (d i); have hh(x:ℝ):Canon n x=spectral U (fun _=>x):=by unfold Canon; rw [← spectral_one U,spectral_smul]; exact congrArg _ (funext (fun i=> mul_one x))
 have hv(i:n): d i∈ Set.Icc a b:=by rw [T,hh,spectral_le] at v w; exact ⟨v i,w i⟩
 have hx: tangle H=spectral U f:=by
    apply CFC.sqrt_unique
    · apply Eq.symm; apply inv_red h; rw [T,spectral_mul,spectral_mul, ←spectral_one U]; apply congrArg; funext i; have hp:0<d i:=t.trans_le (hv i).1; change d i*(rt (d i)*rt (d i))=1; rw [←sq,show rt (d i)^2=(d i)⁻¹ from Real.sq_sqrt (by positivity),mul_inv_cancel₀ hp.ne'] -- tune orientation
    rw [←spectral_zero U,spectral_le]; exact fun i=> Real.sqrt_nonneg _
 rw [hx,T,spectral_evalR,spectral_sub,spectral,twist_norm,Matrix.l2_opNorm_diagonal]; exact pi_norm_le_iff_of_nonneg p|>.mpr (fun i=> (by rw [Complex.norm_real]; exact g _ (hv i))) -- tune Real.norm abs defin.`pi`
lemma License_s (a b e:ℝ)(p:0<a)(t:0<e):∃ p: Polynomial ℝ,∀ x∈ Set.Icc a b, |p.eval x-rt x|≤ e:=by
 obtain ⟨P,Q⟩:= exists_polynomial_near_of_continuousOn a b rt (ContinuousOn.sqrt (continuousOn_id.inv₀ (fun x h=>(p.trans_le h.1).ne'))) e t; exact ⟨P,fun x h=>(Q x h).le⟩ -- maybe namespace ContinuousMap
end
section
variable {ι:Type*}{m:ι→Side} {X Y P W Z:∀i:ι,Op (Single (m i))}
local notation "ν" i:max=> tickA (m i)
lemma lumiWork(h:Hemi m P)(p:0<μ)(t:μ≤1): Hemi m (fun i=> Lumi (tickA (m i)) (P i) μ):=by
 let A(i):= (ν i) * P i; let G(i):= Rheims.frost (ν i) (P i) μ; have he:Hemi m (fun i=> ν i):= Hemi.none ⟨1,zero_le_one,fun i=>(plus_P (m i)).norm_le _⟩ 0 (fun _=> displace)
 have hA:Hemi m A:= he.mult_f h; have ht:Hemi m G:= (Hemi.add_f (hA.mult_f hA.stE) ((Hemi.one_c m).subVH he)).add_f (he.scale_r μ); obtain ⟨D,z,g⟩:= ht.Bound
 have hl(i): lit (G i):=cosy (plus_P _) p t (A i); have hy(i): ‖tangle (G i)‖ ≤ (Real.sqrt μ)⁻¹:= tangle_power (plus_P _) p t (A i)
 refine ⟨⟨(Real.sqrt μ)⁻¹,by positivity,hy⟩, fun ε v=>?_⟩; obtain ⟨Q,K⟩:= License_s μ D (ε/2) p (by positivity); obtain ⟨w,H⟩:= (ht.poly Q).work (ε/2) (by positivity); refine ⟨w,fun i=> ?_⟩; obtain ⟨X,u,c⟩:=H i; let U:= Polynomial.aeval (G i) Q; have he:‖U-tangle (G i)‖ ≤ ε/2:= flight_t p (cozy_floor (plus_P _) p t _) (by rw [canon_map]; exact (CStarAlgebra.norm_le_iff_le_algebraMap _ z (hl i).1).mp (g i)) (hl i) (by positivity) K
 exact ⟨X,u,by change ‖X-tangle (G i)‖ ≤ ε; exact (norm_sub_le_norm_sub_add_norm_sub X U _).trans ((add_le_add c he).trans_eq (add_halves _))⟩ -- check syntax
lemma lumiPair(h:Hemi m P)(p:0<μ)(t:μ≤1) : Hemi m (fun i=> Zami (tickA (m i)) (P i) μ):=by
 have he:Hemi m (fun i=> ν i):= Hemi.none ⟨1,zero_le_one,fun i=> (plus_P (m i)).norm_le _⟩ 0 fun _=> displace
 exact Hemi.mult_f ((lumiWork h p t).mult_f (he.mult_f h)) ((Hemi.one_c m).subVH he)
end
-- project & heat. Should not round regulator with density! Floors on € fixed compatibility.
local notation "Q"=> tickA N
lemma pinch_neighL {A:Op (Single N)} (h:Neighbor k A): Neighbor k ((tickA N)*A*(tickA N) + (1-tickA N)):=by
 refine helios ?_ (neighSub (neighOne _) (loft displace (Nat.zero_le _))); convert! (neigh_mul (neigh_mul displace h) displace) using 1; omega
lemma pinchL(p:Milieu (tickA N) X)(h:Liquid k X e): ∃ M:Op (Single N), IsSelfAdjoint M ∧ M*(1-tickA N)=1-tickA N ∧ ‖M-X‖≤ e ∧ Neighbor k M:=by
 obtain ⟨Y,y,z⟩:= h; have q:IsStarProjection Q:=plus_P _; let Z:= (1/2:ℝ) • (Y+star Y); have he:IsSelfAdjoint Z:= IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg (by norm_num:(0:ℝ)≤1/2)) (show IsSelfAdjoint (Y+star Y) from by unfold IsSelfAdjoint; rw [star_add,star_star,add_comm])  -- tune
 let B:= Q*Z*Q+(1-Q); have hB : Q*Z*Q*(1-Q)=0:=by rw [mul_assoc _ Q,Porth q,mul_zero]
 refine ⟨B,(he.conjugate_self q.2).add q.one_sub.2,by unfold B; rw [add_mul,hB,q.one_sub.1,zero_add],?_, pinch_neighL (bliss (helios y (Window.Brique.Neighbor.adj y)) _)⟩
 have hx:‖star Y-X‖≤ e:=by nth_rw 1 [←p.upperR]; rw [←star_sub,norm_star]; exact z
 have hh:‖Z-X‖≤ e:=by
    have hx1:(1/2:ℝ) • (X+X)=X:=by rw [smul_add, ←add_smul]; norm_num
    nth_rw 1 [←hx1]; unfold Z; rw [←smul_sub,norm_smul,Real.norm_of_nonneg (by norm_num),show Y+star Y-(X+X)=(Y-X)+(star Y-X) by abel]; exact (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add z hx)) (by norm_num: (0:ℝ) ≤1/2)).trans_eq (by ring) -- tune
 unfold B; rw [←p.entire q, add_sub_add_right_eq_sub,←sub_mul,←mul_sub]; exact (needy' q _).trans ((needy q _).trans hh)
lemma pinchZ(p:Spear (tickA N) X)(h:Liquid k X e):∃ M:Op (Single N), Spear (tickA N) M∧ ‖M-X‖≤e∧Neighbor k M:=by
 obtain ⟨Y,y,z⟩:=h; have q:= plus_P N; let B:=Q*Y*(1-Q); have he:Neighbor k B:=by
    convert! neigh_mul (neigh_mul displace y) (neighSub (neighOne 0) displace) using 1; omega
 refine ⟨B,⟨?_,?_⟩, ?_,he⟩
 · change Q*(Q*Y*(1-Q))=_; unfold B; simp only [←mul_assoc, show Q*Q=Q from q.1]
 · unfold B; rw [mul_assoc,q.one_sub.1]
 rw [show B-X=Q*(Y-X)*(1-Q) by unfold B; rw [mul_sub Q,sub_mul,p.up,p.low]]; exact (needy' q.one_sub _).trans ((needy q _).trans z)
-- Freeze family using Brique.
abbrev Ec (k:ℕ)(w:ℕ):Type:= { i: Side × Tulip.Male // w≤ i.1.val ∧ IsStarProjection (spar k i.2 (1:Bkg (More i.1))) }
variable (p:1≤k)
include p
lemma boot :∃ (N₀:ℕ), let m(i:Ec k N₀):=i.val.1; Hemi m (fun i=> spar k i.val.2 (1:Bkg (More (m i)))):=by
 obtain ⟨w,c,C,e,G⟩:= Window.Brique.terrace 1 1 0 0 zero_lt_one zero_lt_one le_rfl le_rfl p; let m(i:Ec k w):=i.val.1; let P(i:Ec k w):Op (Single (m i)):= spar k i.val.2 (1:Bkg (More (m i))); refine ⟨w,⟨⟨1,zero_le_one, fun i=>i.property.2.norm_le _⟩,fun ε v=>?_⟩⟩; obtain ⟨j,t⟩:= ((Window.Brique.tailCloud c C G.level).eventually (gt_mem_nhds v)).exists; refine ⟨j,fun i=> ?_⟩; let C:= G.sparks i.property.1 i.val.2 e le_rfl; exact liq_grow (Window.Brique.casing_neighbor C j 1 (guard0 G.l.le)) le_rfl t.le -- guard0 namespace? needs qualified
variable {δ:ℝ}
lemma tender_set : ∃ (N₀:ℕ), ∀ (b ε:ℝ)(h:0<b)(t:b≤1)(u:0< ε),∃ kL,∀ (N:Side),N₀≤N.val→∀ M:Tulip.Male, let P:= spar k M (1:Bkg (More N)); let Q':=tickA N; IsStarProjection P→ Liquid kL (Lumi Q' P b) ε ∧ Liquid kL (Zami Q' P b) ε:=by
 obtain ⟨w,W⟩:=boot p; refine ⟨w,fun b ε h t u=>?_⟩; obtain ⟨s,S⟩:= (lumiWork W h t).work ε u; obtain ⟨x,X⟩:= (lumiPair W h t).work ε u
 refine ⟨max s x,?_⟩; intro i v M P T l; let Z:Ec k w:=⟨(i,M),v,l⟩; exact ⟨liq_grow (S Z) (le_max_left ..) le_rfl,liq_grow (X Z) (le_max_right ..) le_rfl⟩
abbrev tenderN(k:ℕ)(p:1≤k):=(tender_set p).choose -- include var?
-- public wrapper heights
end Gato
end YM.CF.Window.Presidio
