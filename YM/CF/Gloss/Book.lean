import YM.CF.Gloss.Boot
import YM.CF.Spire.Dais
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable{A D d e:ℝ}{m B:Side}{c:Part m B} {W:Scroll m B c}
open scoped ContDiff
open Jet Phase.Sample
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{Q:E→Pack m B}{h a K:ℝ}{n:ℕ}(V:Set E)(b:Floe.Tagged e K n Q V)(hp:1≤K)
lemma kinV(x:Bool)(v:Vect):dove x v=Gloss.doveL x v:=rfl
lemma ζ_Tr (hK:1≤K)(n:ℕ) :∃ Y:ℝ,1 ≤ Y ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{B m:Side}(Q:E→Pack m B)(V:Set E){e:ℝ},Floe.Tagged e K n Q V→∀ x:Era m,Floe.Tagged e Y n (fun i=> vest B x (Q i)) V:=by
 obtain ⟨C,v,H⟩:=tutor K n hK; refine ⟨C,hK.trans v,fun {E _ _ _ B m} Q V {e} b x i hi=>?_⟩ -- syntax
 let X:= x.charge; have ht:=(b i hi).2.1; let S:Site (Domain m B)→Ballot:= fun _=> Phase.first; refine ⟨voxel _ _ _ _ (b i hi).1,(H _ _ _ E (fun i=>(Q i).1) i (fun _=>S) ht (fun j=> allows_const i ((vote_unit _).trans_le hK))).1,?_⟩
 intro j; let F(z:E):=(Q z).2 (ρx x j); let L:=((doveL X).toContinuousLinearMap); have he : ‖L‖≤1:= (Gloss.doveL X).norm_toContinuousLinearMap.le; have hv:= ((b i hi).2.2 (ρx x j)).linear L he
 simp only [one_mul] at hv; exact hv.mono v
variable (q:Axis) {W:Scroll m B c} (u:d>0)(s:ScaleK A D W)(g:Budget B e d)
open Floe
lemma crazy {V:E→Pack m B} (Y:Pack m B→ℂ)(a:ℝ) (x:E)(φ:Era m) (h: Allows n (fun v=> Y (V v)) x a):Allows n (fun t=> payZ φ (Y (V t))) x a:=by -- types, qualify
 unfold payZ; cases wageZ φ
 exact h
 exact (h.linear (starL' ℝ (A:=ℂ)).toContinuousLinearMap (by exact Complex.conjLIE.norm_toContinuousLinearMap.le : ‖(starL' ℝ (A:=ℂ)).toContinuousLinearMap‖≤ 1)).mono (by simp)
variable {s':ℝ} (x:costG m B)
include u g s b
omit u g s b
variable {R:ℝ}
lemma bit_x (hp:1 ≤ K)(p:0<R)(B:Side)(n:ℕ): ∃ (Y₁:ℝ), 0 ≤ Y₁ ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](m:Side)(e d' a b:ℝ)(v: Part m B)(W: Scroll m B v), d'>0→Budget B e d'→GripK W R a b →∀(X:E→Pack m B)(U:Set E),Tagged e K n X U→IsOpen U→∀(x:E),x∈U→∀ i:costG m B, Allows n (fun x=> seedQ W i (X x)) x (max d'⁻¹ 1*Y₁*(1+(chairs m B i.2).card:ℝ)^(2*n)*dinQ W d' i):=by
 obtain ⟨Y,hY,P⟩:=ζ_Tr hp n; obtain ⟨a,b,d,z,p₁,p₂,p₃,p₄,T⟩:= honors_F n hY p B
 let W:=mercury 0 n a (mercury 0 n b z); have hw:0≤W:=p₄.trans ((bigger n _ p₄ p₂).trans (bigger n _ (p₄.trans (bigger n _ p₄ p₂)) p₁))
 refine ⟨2*(d+W),by positivity,fun E _ _ _ m e K r t v Wt q b' g X U p0 V x hx i=>?_⟩
 let Y':= i.1; let k:= max K⁻¹ 1; have he:1≤ k:= le_max_right ..; have hk:k≥0:=zero_le_one.trans he; let n':= (chairs m B i.2).card; let w:= (1+(n':ℝ))^ (2*n); have hu:1≤w:= one_le_pow₀ (by simp)
 let A:= Wt.mint i.2; let G(z:E):=vest B i.1 (X z); have htA:= gainS g.meter b' i.2; have hp:=htA.pos
 have hA(u:Hub m)(s:sanctioned m B i.2 u): Allows n (fun z=> Wt.value i.2 u (G z)) x ((d+W)*w*A):=by
    have hx:= T E e b'.1 m v Wt i.2 G U V (P X U p0 i.1) x hx r t g u s; refine hx.mono ?_
    have ht : mercury n' n a (mercury n' n b (z*A))=W*w*A:=by unfold W mercury w; rw [pow_mul']; push_cast; ring -- pow_mul' signature
    change _+mercury n' n a (mercury n' n b (z*A))≤_; rw [ht,add_mul,add_mul]; exact add_le_add_left (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right p₃ hu) hp) _
 have hc : A ≤ k * dust Wt K i.2  := by
    unfold dust; split
    · rw [←mul_left_comm]; apply le_mul_of_one_le_right hp; rw [←div_le_iff₀ q]; simpa only [one_div] using (le_max_left K⁻¹ (1:ℝ))
    exact le_mul_of_one_le_left hp he
 have he' : 0≤ (d+W)*w*A:=mul_nonneg (by positivity) hp
 have hf: Allows n (fun z=> Wt.term i.2 (G z)) x ((d+W)*w*A):=by
    by_cases p: A=0
    · have hz : Allows n (fun _=> (0:ℂ)) x _ := allows_const _ ((norm_zero.le).trans he'); apply hz.germ; filter_upwards [V.mem_nhds hx] with j hj using Eq.symm (norm_le_zero_iff.mp ((htA.norm _ ((P X U p0 Y' j hj).1)).trans (le_of_eq p)))
    unfold Scroll.term; split; next h=> exact hA _ (Phase.Grove.plane _ (htA.connect p) h)
    exact allows_const _ ((norm_zero.le).trans he')
 have he_:= (hA none (by trivial)).add (hf.smul (-1)); have heF: Allows n (fun z=> Wt.leftover i.2 (G z)) x ((d+W)*w*A*2):=by unfold Scroll.leftover; simp_rw [sub_eq_add_neg]; simp only [neg_one_smul,abs_neg,abs_one,one_mul] at he_; rw [mul_two]; exact he_
 refine ((crazy (Wt.leftover i.2) _ _ i.1 heF).smul (rip m)).mono ?_; rw [abs_of_nonneg (ripp m)]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity: 0≤ (d+W)*w)) (by norm_num: (0:ℝ) ≤ 2)) (ripp m)); unfold dinQ; unfold k w n'; ring_nf; rfl
end YM.CF.Gloss
