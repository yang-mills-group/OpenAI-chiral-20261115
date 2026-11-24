import YM.SU5.FiniteGaugeData.LapisQ.Spitz
import YM.Work.F06.Stencil
import YM.Work.F06.Energy
import YM.Work.F06.Phase
set_option autoImplicit false
set_option maxHeartbeats 540000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Vulcan
variable {n:Side} {G:Gauge} {ρ C Δ σ K:ℝ}
section rot
variable {α β γ:Type}[Fintype α][Fintype β][Fintype γ] [DecidableEq α][DecidableEq β][DecidableEq γ]
variable {A:Matrix (Site n×α) (Site n×β) ℝ}{B:Matrix (Site n×β) (Site n×γ) ℝ}(s:Site n)
variable {M M':Site n→Matrix α β ℂ}{Q:Site n→ Matrix β γ ℂ}
def Lease (A:Matrix (Site n×α) (Site n×β) ℝ)(M:Site n→ Matrix α β ℂ):= approached A * rotations n β=rotations n α*fiber M
lemma bendLease (d:Lease A M)(e: Lease B Q): Lease (A*B) fun i => M i*Q i :=by unfold Lease; rw [prom_mul,Matrix.mul_assoc,e,←Matrix.mul_assoc,d, Matrix.mul_assoc, fiber_product]
lemma subequal (p:Lease A M)(q:Lease A M'): M=M':=by
 funext s; ext i j; have h(p':_)(v : Lease A p'): (approached A*rotations n β) (0,i) (s,j)=p' s i j:=by rw [show approached A*rotations n β=_ from v, rot_fiber,cell_origin,one_mul]; -- tune
 exact (h M p).symm.trans (h M' q) -- M' unbound declare
lemma zero_Lease : Lease (0:Matrix (Site n×α) (Site n×β) ℝ) 0:=by
 unfold Lease; rw [show fiber (L:=n) (0:Site n→ Matrix α β ℂ)=0 from ?_, show approached (_:Matrix _ _ ℝ)= (0:Matrix _ _ ℂ) from ?_]; · rw [Matrix.zero_mul, Matrix.mul_zero]
 swap; · ext ⟨i,j⟩ ⟨x,y⟩; simp [fiber] -- tune
 ext i j; simp [approached] -- tune swap
---- formula for stationary & herm
local notation "V" a:max=> rotations n a
def facet (A:Matrix (Site n×α) (Site n×β) ℝ)(p:Site n): Matrix α β ℂ:=Matrix.of (fun i j=> ∑ x:Site n,(A (0,i) (x,j):ℂ)*cell p x)
lemma curtain (S:stationaryB A) : Lease A (facet A):=by
 ext ⟨i,j⟩ ⟨k,v⟩; rw [rot_fiber,mul_apply]; rw [Fintype.sum_prod_type]; simp_rw [rotations, Matrix.of_apply,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]; unfold facet approached; rw [Matrix.of_apply, mul_sum]
 rw [← Equiv.sum_comp (Equiv.addLeft i)]; apply sum_congr rfl; intro x _; rw [show Equiv.addLeft i x = i+x from rfl,cell_add]; have he:= S i; have he0:= congrFun (congrFun he (0,j)) (x,v); change A (0+i,j) (x+i,v)=_ at he0; rw [zero_add] at he0; rw [Matrix.map_apply, add_comm i x, he0]; ring
lemma ballet {A:Matrix (Site n×α) (Site n×α) ℝ}(S:stationaryB A)(h:A.transpose=A) : (facet A s).conjTranspose=facet A s:=by
 ext i j; simp only [conjTranspose_apply,facet,Matrix.of_apply,star_sum,star_mul, Complex.star_def,map_inv₀,conj_ofReal]; rw [←Equiv.sum_comp (Equiv.neg _)]; apply sum_congr rfl; intro x _; change (star (cell s (-x)))*_= _; rw [Complex.star_def,cell_bar,cell_inverse,inv_inv]; change _*(A (0,j) (-x,i):ℂ)= _; have he:= congrFun (congrFun (S x) (0,j)) (-x,i); change A (0+x,j) (-x+x,i)=_ at he; rw [zero_add,neg_add_cancel] at he; rw [← he, show A (x,j) (0,i)=A (0,i) (x,j) from congrFun (congrFun h (0,i)) (x,j), mul_comm]
lemma beamD (i:ℕ) : Lease (d i n) (fun p:Site n=> symbol i (mon p)):= by
 have hp:= circulant n (cobound i) (cobound_safe i); simp_rw [Exterior.reading] at hp; exact hp
abbrev waves (s:Site n)(x:α→ℂ)(i:Site n×α):ℂ:=cell s i.1*x i.2
lemma slotEq (t: Lease A M)(x:β→ℂ): approached A *ᵥ waves s x= waves s (M s*ᵥ x):=by
 funext i
 have hv(j:β) (p:Site n)(b:β): (((approached A)*V β) i (s,j))=(cell s i.1)*(M s i.2 j):= by rw [show approached A*(V β)=_ from t]; exact rot_fiber ..
 have hz(j:β): (∑ p:Site n, (A i (p,j):ℂ)*cell s p)=cell s i.1*M s i.2 j :=by
    have he:= hv j s j; rw [mul_apply,Fintype.sum_prod_type] at he; simp_rw [rotations, Matrix.of_apply, mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true] at he; exact he
 simp only [mulVec,waves,dotProduct,← mul_assoc,Fintype.sum_prod_type,approached,Matrix.map_apply] -- WARN infinite! remove
 rw [sum_comm]; simp_rw [← Finset.sum_mul, hz, mul_assoc, ←Finset.mul_sum]; -- tune cast approached
lemma cell_pay (p q:Site n): ‖cell p q‖=1:= mode_real (mon p) (lift q) (real_frequency p)
lemma crest (x:α→ℂ): sqLength (waves s x)= (n.val:ℝ)^4*sqLength x:=by simp_rw [sqLength_apply,Fintype.sum_prod_type,waves,norm_mul,cell_pay,one_mul]; simp
private lemma boom {B:Matrix α α ℝ}(z:α→ℂ)(P:∀ x:α→ℝ,ρ^2*dotProduct (B*ᵥ x) (B*ᵥ x)≤dotProduct x x): ρ^2*sqLength (approached B*ᵥ z)≤ sqLength z:=by
 let Q(x:α→ℂ):=dotProduct (fun i=> (x i).re) (fun i=>(x i).re)
 let R(x:α→ℂ):=dotProduct (fun i=> (x i).im) (fun i=> (x i).im)
 have he(x:α→ℂ): sqLength x= Q x + R x:=by
    unfold Q R; rw [sqLength_apply]; simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,dotProduct,sum_add_distrib]
 let v:=approached B*ᵥ z
 have hr(i): (v i).re=(B*ᵥ (fun i=>(z i).re)) i:=by simp only [v, approached,mulVec,dotProduct,re_sum,mul_re,map_apply, Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] -- map_apply amb
 have hi(i): (v i).im=(B*ᵥ (fun i=>(z i).im)) i:=by simp only [v, approached,mulVec,dotProduct,im_sum,mul_im,map_apply, Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] -- tune
 change ρ^2*sqLength v≤_; rw [he,he, _root_.mul_add]; unfold Q R; simp_rw [hr,hi]; exact add_le_add (P _) (P _)
lemma glamour {A:Matrix (Site n×α) (Site n×α) ℝ} {M:Site n→ Matrix α α ℂ}(t:Lease A M)(𝕧:∀ x:Site n×α→ℝ,ρ^2*dotProduct (A*ᵥ x) (A*ᵥ x)≤dotProduct x x)(x:α→ℂ) : ρ^2*sqLength (M s*ᵥ x) ≤ sqLength x:=by -- V notation conflict escape
 have he:= boom (waves s x) 𝕧
 rw [slotEq s t, crest, crest] at he; apply le_of_mul_le_mul_left ?_ (pow_pos (side_pos n) 4); linarith only [he] -- nonlinear via explicit division
end rot
variable {u:Stage}{P:Bed}
structure Gate (u:Stage)(P:Bed)(ρ C σ K:ℝ)(n:Side)(A:Matrix (Body 2 n) (Body 2 n) ℝ):Prop where
 F: Floor P u.clip n ρ C
 cost:0<ρ
 pen: P.metric.strip σ K
 width:0<σ
 stands: stationaryB A
 pays: Survey (d 1 n) (P.metric.acts n) A
variable {A:Matrix (Body 2 n) (Body 2 n) ℝ}(g:Gate u P ρ C σ K n A)(p: Site n)
include g
lemma wall_pulse : facet A p * (P.metric.read (mon p)*symbol 1 (mon p))=symbol 1 (mon p):=by
 have he:A*(P.metric.acts n*d 1 n)=d 1 n:= Matrix.ext_iff_mulVec.mpr fun i=>by rw [←mulVec_mulVec,←mulVec_mulVec]; exact g.pays.2.2 _ ⟨i,rfl⟩
 suffices hx: Lease (d 1 n) (fun p=> facet A p * (P.metric.read (mon p)*symbol 1 (mon p))) by exact congrFun (subequal hx (beamD _)) p
  -- from rewrite.H. add helper
 have u: Lease (P.metric.acts n) (fun i:Site n=> P.metric.read (mon i)):= circulant n P.metric (Row.rights _ _ g.pen g.width.le)
 exact Eq.mp (congrArg (fun x=> Lease x (fun i:Site n=> facet A i * (P.metric.read (mon i)*symbol 1 (mon i)))) he) (bendLease (curtain g.stands) (bendLease u (beamD 1))) -- implicit goal instance convert
lemma closed_pulse : symbol 2 (mon p)*facet A p=0:=by
 have he: d 2 n*A=0:=Matrix.ext_iff_mulVec.mpr (fun i=>by obtain ⟨v,b⟩:=g.pays.2.1 i; rw [←mulVec_mulVec, Matrix.zero_mulVec,←b,mulVec_mulVec,Exterior.closed 1 n]; exact Matrix.zero_mulVec v)
 have hx:= bendLease (beamD 2) (curtain g.stands); rw [he] at hx; exact congrFun (subequal hx zero_Lease) p
lemma frontier(p:Site n)(x:TypeFace 2→ℂ): ρ^2*sqLength (facet A p *ᵥ x)≤ sqLength x:= glamour p (curtain g.stands) (sun_rays (d 1 n) g.pays g.cost (fun i=> (g.F.uniform.1 i).1) g.F.symmetric.1) x
lemma frontier_entry(i j:TypeFace 2) : ‖facet A p i j‖≤ 1/ρ:=by
 have hf:= g.cost; let v: TypeFace 2→ℂ:= Pi.single j 1; let x:= facet A p*ᵥ v; rw [le_div_iff₀ hf, ←sq_le_sq₀ (by positivity) zero_le_one]; have hq: sqLength v=1:=by
    rw [sqLength_apply,sum_eq_single j]; · simp [v];
    · intro i t h; simp [v,h]
    simp
 have ht:=frontier g p v; rw [hq] at ht; have hy:x i=facet A p i j:= dotProduct_single_one _ _; rw [←hy,mul_pow, mul_comm _ (ρ^2), one_pow]; exact (mul_le_mul_of_nonneg_left (component_sq_le ..) (sq_nonneg ρ)).trans ht
end Vulcan
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Vulcan.wall_pulse
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Vulcan.closed_pulse
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Vulcan.frontier_entry
